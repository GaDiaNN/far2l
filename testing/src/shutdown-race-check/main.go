// shutdown-race-check drives a built far2l binary directly over its raw
// TEST_CMD_* control socket (see WinPort/src/Backend/TestController.cpp /
// TestProtocol.h), independent of the main far2l-smoke harness, through this
// sequence: dismiss Help -> dismiss the first-run OSC52 dialog (if shown) ->
// F10 -> wait for the quit-confirmation dialog -> Enter (the actual quit
// trigger) -> immediately (no added delay) send one more TEST_CMD_STATUS
// request.
//
// This reproduces a real shutdown-ordering bug: before the fix,
// TestController's destructor is simply `_stop = true; WaitThread();`, with
// nothing to wake ClientLoop's thread out of its blocking Recv() if it is
// parked there when far2l starts quitting. Sending one more command after
// the quit keystroke is exactly what a real test client does in practice
// (e.g. a status poll) - and on the unfixed binary it deterministically
// leaves the process hung on exit, needing to be killed, because nothing
// ever wakes that thread again. After the fix, TestController's destructor
// wakes the thread via LocalSocket::Shutdown() and joins it *before*
// WinPortMain resets the console pointers, so the process exits cleanly
// every time regardless of when the extra request lands.
//
// Deliberately does NOT reuse far2l_ExpectExit/ReqBye from the main harness:
// that helper always sends TEST_CMD_DETACH before checking for exit, which
// would itself wake a thread parked in Recv() and could mask the very hang
// this check exists to catch. Process liveness is checked directly instead.
//
// Also deliberately does not reuse the main harness's termtest-based process
// spawning: termtest only reads the pty's master side on demand, inside its
// own Expect*() calls (see far2l-smoke's own D009 history) - since this tool
// talks to the raw control socket directly and never calls into termtest's
// expect layer, nothing would ever drain the pty, and far2l would block in
// tcdrain()/write() once its terminal output fills the buffer (the same
// class of bug the fix under test is adjacent to, just on the harness side).
// Spawning via creack/pty directly, with an explicit always-on drain
// goroutine, avoids that regardless of which layer is doing the reading.
//
// Usage:
//
//	go build -o shutdown-race-check ./shutdown-race-check
//	./shutdown-race-check <path-to-far2l-binary> [iterations]
//
// Exit code 0 if every iteration exited cleanly; 1 if any iteration hung.
package main

import (
	"encoding/binary"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"syscall"
	"time"

	"github.com/creack/pty"
)

// socketBufferSize matches far2l_ConfigureSocketBuffers in ../main.go and
// TestController::ClientLoop's own sock.SetBufferSize(1024*1024) call -
// large enough that a full TestRequestWaitString datagram (2072 bytes) is
// nowhere near any platform's default unix-datagram ceiling (e.g. macOS/BSD's
// net.local.dgram.maxdgram, 2048 by default).
const socketBufferSize = 1024 * 1024

func configureSocketBuffers(conn *net.UnixConn) error {
	rawConn, err := conn.SyscallConn()
	if err != nil {
		return err
	}
	var sockErr error
	err = rawConn.Control(func(fd uintptr) {
		if e := syscall.SetsockoptInt(int(fd), syscall.SOL_SOCKET, syscall.SO_RCVBUF, socketBufferSize); e != nil {
			sockErr = e
			return
		}
		sockErr = syscall.SetsockoptInt(int(fd), syscall.SOL_SOCKET, syscall.SO_SNDBUF, socketBufferSize)
	})
	if err != nil {
		return err
	}
	return sockErr
}

const (
	cmdStatus     = 1
	cmdWaitString = 3
	cmdWaitNoStr  = 4
	cmdSendKey    = 5

	vkEscape = 0x1B
	vkF10    = 0x79
	vkEnter  = 0x0D

	testTextMax = 2048

	// A hang here is permanent (the thread is parked forever, nothing will
	// ever wake it), so this only needs to be long enough not to
	// misclassify a merely slow but still-alive process.
	hangTimeout = 3 * time.Second
)

// Wire layout is TestRequestSendKey (TestProtocol.h): cmd, controls, chr,
// key_code, scan_code, pressed - in that order, each field 4 bytes except
// the trailing 1-byte pressed flag.
func sendKey(sock *net.UnixConn, addr net.Addr, vk uint32, pressed bool) error {
	var buf [24]byte
	binary.LittleEndian.PutUint32(buf[0:], cmdSendKey)
	binary.LittleEndian.PutUint32(buf[12:], vk) // key_code
	if pressed {
		buf[20] = 1
	}
	_, err := sock.WriteTo(buf[:], addr)
	return err
}

func typeVK(sock *net.UnixConn, addr net.Addr, vk uint32) error {
	if err := sendKey(sock, addr, vk, true); err != nil {
		return err
	}
	return sendKey(sock, addr, vk, false)
}

// waitString returns (found, error). found is false both when the string
// genuinely wasn't seen before the timeout and when needPresence is false
// and it stayed absent (mirrors the wire reply's {-1,-1,-1} "not matched"
// sentinel either way).
func waitString(sock *net.UnixConn, addr net.Addr, s string, timeoutMs uint32, needPresence bool, width, height uint32) (bool, error) {
	cmd := uint32(cmdWaitString)
	if !needPresence {
		cmd = cmdWaitNoStr
	}
	buf := make([]byte, 24+testTextMax)
	binary.LittleEndian.PutUint32(buf[0:], cmd)
	binary.LittleEndian.PutUint32(buf[4:], timeoutMs)
	binary.LittleEndian.PutUint32(buf[16:], width)
	binary.LittleEndian.PutUint32(buf[20:], height)
	copy(buf[24:], s)
	if _, err := sock.WriteTo(buf, addr); err != nil {
		return false, err
	}
	if err := sock.SetReadDeadline(time.Now().Add(time.Duration(timeoutMs)*time.Millisecond + 3*time.Second)); err != nil {
		return false, err
	}
	reply := make([]byte, 12)
	n, _, err := sock.ReadFromUnix(reply)
	if err != nil || n != 12 {
		return false, err
	}
	return binary.LittleEndian.Uint32(reply[0:]) != 0xFFFFFFFF, nil
}

// runOnce returns "ok" (clean exit) or "HUNG" (still alive past hangTimeout
// after the racing request), or an error for anything unexpected (setup
// failure, protocol mismatch).
func runOnce(far2lBin, workroot string, idx int) (string, error) {
	base := filepath.Join(workroot, fmt.Sprintf("iter-%d", idx))
	profile, left, right := filepath.Join(base, "profile"), filepath.Join(base, "left"), filepath.Join(base, "right")
	for _, d := range []string{profile, left, right} {
		if err := os.MkdirAll(d, 0700); err != nil {
			return "", err
		}
	}
	sockPath := filepath.Join(base, "ctl.sock")
	os.Remove(sockPath)

	srv, err := net.ListenUnixgram("unixgram", &net.UnixAddr{Name: sockPath, Net: "unixgram"})
	if err != nil {
		return "", err
	}
	defer srv.Close()
	defer os.Remove(sockPath)
	if err := configureSocketBuffers(srv); err != nil {
		return "", err
	}

	cmd := exec.Command(far2lBin, "--tty", "--nodetect", "--mortal", "-u", profile, "-cd", left, "-cd", right)
	cmd.Env = append(os.Environ(),
		"FAR2L_STD="+filepath.Join(base, "far2l.log"),
		"FAR2L_TESTCTL="+sockPath)
	ptmx, err := pty.StartWithSize(cmd, &pty.Winsize{Rows: 25, Cols: 80})
	if err != nil {
		return "", err
	}
	defer ptmx.Close()
	// Nothing else ever reads this pty (the control socket is the only
	// channel this tool uses), so without a drain, far2l's writer thread
	// blocks in tcdrain()/write() as soon as its screen repaints fill the
	// buffer - see the package doc comment.
	go io.Copy(io.Discard, ptmx)

	exitCode := make(chan int, 1)
	go func() {
		cmd.Wait()
		code := -1
		if cmd.ProcessState != nil {
			code = cmd.ProcessState.ExitCode()
		}
		exitCode <- code
	}()
	closeApp := func() {
		if cmd.Process != nil {
			cmd.Process.Kill()
		}
	}

	if err := srv.SetReadDeadline(time.Now().Add(8 * time.Second)); err != nil {
		return "", err
	}
	initBuf := make([]byte, 4096)
	n, addr, err := srv.ReadFromUnix(initBuf)
	if err != nil || n != 2068 {
		closeApp()
		return "", fmt.Errorf("initial status: n=%d err=%v", n, err)
	}
	width := binary.LittleEndian.Uint32(initBuf[12:])
	height := binary.LittleEndian.Uint32(initBuf[16:])

	waitString(srv, addr, "Help - FAR2L", 6000, true, width, height)
	typeVK(srv, addr, vkEscape)
	if found, _ := waitString(srv, addr, "OSC52", 8000, true, width, height); found {
		typeVK(srv, addr, vkEscape)
		waitString(srv, addr, "OSC52", 3000, false, width, height)
	}

	typeVK(srv, addr, vkF10)
	found, err := waitString(srv, addr, "Do you want to quit FAR?", 6000, true, width, height)
	if err != nil || !found {
		closeApp()
		return "", fmt.Errorf("quit dialog not found: found=%v err=%v", found, err)
	}

	typeVK(srv, addr, vkEnter) // the actual quit trigger
	// Immediately (no delay) send one more request, racing teardown.
	var statusReq [4]byte
	binary.LittleEndian.PutUint32(statusReq[:], cmdStatus)
	srv.WriteTo(statusReq[:], addr)
	srv.SetReadDeadline(time.Now().Add(2 * time.Second))
	reply := make([]byte, 4096)
	srv.ReadFromUnix(reply) // don't care whether it answers or times out

	select {
	case code := <-exitCode:
		if code != 0 {
			return "", fmt.Errorf("exited with code %d", code)
		}
		return "ok", nil
	case <-time.After(hangTimeout):
		closeApp() // force-kill cleanup; the process is confirmed hung
		return "HUNG", nil
	}
}

func main() {
	if len(os.Args) < 2 {
		fmt.Println("usage: shutdown-race-check <path-to-far2l-binary> [iterations]")
		os.Exit(1)
	}
	far2lBin, err := filepath.Abs(os.Args[1])
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	iterations := 20
	if len(os.Args) > 2 {
		if v, err := strconv.Atoi(os.Args[2]); err == nil {
			iterations = v
		}
	}

	workroot, err := os.MkdirTemp("", "shutdown_race_check_")
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	defer os.RemoveAll(workroot)

	counts := map[string]int{}
	t0 := time.Now()
	for i := 0; i < iterations; i++ {
		outcome, err := runOnce(far2lBin, workroot, i)
		if err != nil {
			outcome = "anomaly"
			fmt.Printf("[%03d] %s: %v\n", i, outcome, err)
		} else if outcome != "ok" {
			fmt.Printf("[%03d] %s\n", i, outcome)
		}
		counts[outcome]++
	}
	elapsed := time.Since(t0)
	fmt.Printf("==== %d iterations in %.1fs (%.2fs/iter) ====\n", iterations, elapsed.Seconds(), elapsed.Seconds()/float64(iterations))
	for outcome, count := range counts {
		fmt.Printf("  %-24s %d\n", outcome, count)
	}
	if counts["ok"] != iterations {
		os.Exit(1)
	}
}
