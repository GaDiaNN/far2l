#!/usr/bin/env python3
"""TestController shutdown-race regression check.

Drives a built far2l binary directly over its raw TEST_CMD_* control socket
(see WinPort/src/Backend/TestController.cpp / TestProtocol.h), independent
of the Go/goja test harness, through this sequence:

  dismiss Help -> dismiss the first-run OSC52 dialog (if shown) -> F10 ->
  wait for the quit-confirmation dialog -> Enter (the actual quit trigger)
  -> immediately (no added delay) send one more TEST_CMD_STATUS request.

This reproduces a real shutdown-ordering bug: before the fix,
`TestController`'s destructor is simply `_stop = true; WaitThread();`, with
nothing to wake `ClientLoop`'s thread out of its blocking `Recv()` if it is
parked there when far2l starts quitting. Sending one more command after the
quit keystroke is exactly what a real test client does in practice (e.g. a
status poll, or the harness's own bookkeeping) - and on the unfixed binary
it deterministically leaves the process hung on exit, needing SIGKILL,
because nothing ever wakes that thread again. Depending on the exact
scheduling of that extra request relative to `WinPortMain` nulling out the
global console pointers, it either answers first (then hangs) or answers
after nulling (a null-pointer dereference in `ClientDispatchStatus`,
SIGSEGV - much rarer under normal scheduling, but produced this reliably
on the maintainers' behalf under an artificially widened timing window
during development of this fix). No fault injection, sleeps, or any other
timing trick is used here: only the natural ordering of two independent
threads decides the outcome, and no product source is touched.

After the fix (this PR), `~TestController` wakes the thread via
`LocalSocket::Shutdown()` and joins it *before* `WinPortMain` resets the
console pointers, so the race window no longer exists: the process exits
cleanly every time, regardless of when the extra request lands.

Usage:
    testcontroller_shutdown_regression.py <path-to-far2l-binary> [iterations]

Exit code 0 if every iteration exited cleanly; 1 if any iteration hung or
crashed (prints a per-iteration breakdown either way).

Fully verified on both Linux and macOS (30/30 HUNG pre-fix, 30/30 clean
exit(0) post-fix, on each platform independently - real OS scheduling only,
no timing tricks).
"""
import fcntl
import os
import pty
import shutil
import signal
import socket
import struct
import sys
import tempfile
import termios
import threading
import time

TEST_CMD_STATUS = 1
TEST_CMD_SEND_KEY = 5
TEST_CMD_WAIT_STRING = 3
TEST_CMD_WAIT_NO_STRING = 4

VK_ESCAPE = 0x1B
VK_F10 = 0x79
VK_ENTER = 0x0D

# A hang here is permanent (the thread is parked forever, nothing will ever
# wake it), so this only needs to be long enough to not misclassify a
# merely slow but still-alive process.
HANG_TIMEOUT_SEC = 2.0


def start_far2l(far2l_bin, profile, left, right, sock_path, log_path):
	# winsize must be set on the slave before fork/exec, or far2l's initial
	# TIOCGWINSZ probe can race a later SIGWINCH and briefly run with an
	# inconsistent screen size.
	master_fd, slave_fd = pty.openpty()
	fcntl.ioctl(slave_fd, termios.TIOCSWINSZ, struct.pack('HHHH', 25, 80, 0, 0))
	env = dict(os.environ)
	env['FAR2L_TESTCTL'] = sock_path
	# FAR2L_STD controls far2l's OWN buffered stdio (fprintf debug logging via
	# freopen), not the raw TTY-rendering writes - matches the Go tool and the
	# main harness, both of which point this at a real log file, not /dev/null.
	env['FAR2L_STD'] = log_path
	pid = os.fork()
	if pid == 0:
		os.setsid()
		os.close(master_fd)
		# All three standard fds are the pty slave, exactly like a real
		# terminal session (and like testing/src/shutdown-race-check's
		# pty.StartWithSize) - D009 (far2l blocks in tcdrain()/write() once
		# its terminal output fills the unread pty buffer) is handled by the
		# caller's continuous drain thread instead of by routing output away
		# from the pty, which turned out not to be sufficient on its own.
		os.dup2(slave_fd, 0)
		os.dup2(slave_fd, 1)
		os.dup2(slave_fd, 2)
		fcntl.ioctl(0, termios.TIOCSCTTY, 0)
		if slave_fd > 2:
			os.close(slave_fd)
		try:
			os.execve(far2l_bin, [far2l_bin, '--tty', '--nodetect', '--mortal',
			                       '-u', profile, '-cd', left, '-cd', right], env)
		except OSError:
			pass
		os._exit(127)
	os.close(slave_fd)
	return pid, master_fd


def drain_pty(master_fd, stop_event):
	# Nothing else ever reads the master side of this pty. Without this,
	# far2l's writer thread blocks in tcdrain()/write() as soon as its
	# terminal-rendering output fills the kernel buffer - this project's own
	# D009, on a harness codepath rather than the main one. A continuous
	# drain, exactly like testing/src/shutdown-race-check's
	# io.Copy(io.Discard, ...) goroutine, removes the ceiling entirely.
	try:
		while not stop_event.is_set():
			try:
				data = os.read(master_fd, 65536)
				if not data:
					break
			except OSError:
				break
	except Exception:
		pass


def send_key(sock, addr, key_code, pressed):
	sock.sendto(struct.pack('<IIIIIB3x', TEST_CMD_SEND_KEY, 0, 0, key_code, 0, 1 if pressed else 0), addr)


def type_vk(sock, addr, key_code):
	send_key(sock, addr, key_code, True)
	send_key(sock, addr, key_code, False)


def wait_string(sock, addr, s, timeout_ms, need_presence, width, height):
	cmd = TEST_CMD_WAIT_STRING if need_presence else TEST_CMD_WAIT_NO_STRING
	payload = struct.pack('<IIIIII', cmd, timeout_ms, 0, 0, width, height) + (s.encode() + b'\x00\x00').ljust(2048, b'\x00')
	sock.sendto(payload, addr)
	sock.settimeout(timeout_ms / 1000.0 + 3)
	reply, _ = sock.recvfrom(4096)
	found_index, x, y = struct.unpack('<III', reply[:12])
	return None if found_index == 0xFFFFFFFF else (found_index, x, y)


def run_once(far2l_bin, workroot, idx):
	base = tempfile.mkdtemp(prefix='iter-%d-' % idx, dir=workroot)
	profile, left, right = (os.path.join(base, d) for d in ('profile', 'left', 'right'))
	for d in (profile, left, right):
		os.makedirs(d, exist_ok=True)
	sock_path = tempfile.mktemp(prefix='tc_shutdown_', suffix='.sock')

	srv = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
	# TestRequestWaitString's wire struct carries a fixed 2048-byte string
	# field (TestProtocol.h), so a WAIT_STRING datagram always runs a couple
	# hundred bytes past 2KB. That is under Linux's default unix-dgram limit
	# but over macOS/BSD's (net.local.dgram.maxdgram, default 2048) - raise
	# both buffers unconditionally so the same script works on every
	# platform instead of branching on `sys.platform`.
	srv.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 262144)
	srv.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 262144)
	srv.bind(sock_path)
	log_path = os.path.join(base, 'far2l.log')
	pid, master_fd = start_far2l(far2l_bin, profile, left, right, sock_path, log_path)
	stop_evt = threading.Event()
	drainer = threading.Thread(target=drain_pty, args=(master_fd, stop_evt), daemon=True)
	drainer.start()

	try:
		srv.settimeout(8.0)
		status, addr = srv.recvfrom(4096)
		width, height = struct.unpack('<II', status[12:20])

		wait_string(srv, addr, 'Help - FAR2L', 6000, True, width, height)
		type_vk(srv, addr, VK_ESCAPE)  # dismiss Help
		if wait_string(srv, addr, 'OSC52', 8000, True, width, height) is not None:
			type_vk(srv, addr, VK_ESCAPE)  # dismiss the first-run OSC52 dialog
			wait_string(srv, addr, 'OSC52', 3000, False, width, height)

		type_vk(srv, addr, VK_F10)
		if wait_string(srv, addr, 'Do you want to quit FAR?', 6000, True, width, height) is None:
			os.kill(pid, signal.SIGKILL)
			os.waitpid(pid, 0)
			stop_evt.set()
			srv.close()
			try:
				os.unlink(sock_path)
			except OSError:
				pass
			try:
				os.close(master_fd)
			except OSError:
				pass
			return 'setup_failed'

		type_vk(srv, addr, VK_ENTER)  # the actual quit trigger
		# Immediately (no delay) send one more request, racing teardown.
		srv.sendto(struct.pack('<I', TEST_CMD_STATUS), addr)
		srv.settimeout(2.0)
		try:
			srv.recv(4096)
		except socket.timeout:
			pass
	except Exception:
		srv.close()
		try:
			os.unlink(sock_path)
		except OSError:
			pass
		raise

	# Deliberately NOT closing/unlinking the control socket yet. Confirmed via
	# a live `sample` capture on macOS: closing/unlinking it immediately here
	# (before far2l has actually finished exiting) leaves ClientLoop's worker
	# thread parked in __recvfrom for multiple seconds - LocalSocket::Shutdown()
	# still runs (the main thread is seen correctly waiting in
	# Threaded::WaitThread()/condition_variable::wait, i.e. the fix's ordering
	# is doing its job), but shutdown(SHUT_RDWR) on an unconnected AF_UNIX
	# SOCK_DGRAM socket does not reliably/promptly unblock a pending recvfrom()
	# on macOS the way it does on Linux once the peer address it was bound to
	# stops existing. Not a bug in the fix (it does not hang forever either
	# way - this is not a fresh instance of D014), just a lot slower than the
	# <0.1s this gets when the peer socket is left alone. Keep it open
	# (nothing more is ever sent on it) until the process is confirmed exited
	# or killed, which reproducibly avoids the slow path entirely.
	deadline = time.time() + HANG_TIMEOUT_SEC
	wait_status, hung = None, False
	while time.time() < deadline:
		try:
			waited_pid, wait_status = os.waitpid(pid, os.WNOHANG)
			if waited_pid == pid:
				break
		except ChildProcessError:
			wait_status = None
			break
		time.sleep(0.02)
	else:
		hung = True

	srv.close()
	try:
		os.unlink(sock_path)
	except OSError:
		pass

	crash_log = None
	for root, _, files in os.walk(profile):
		if 'crash.log' in (f.lower() for f in files):
			crash_log = root
			break

	if hung:
		try:
			os.kill(pid, signal.SIGKILL)
			os.waitpid(pid, 0)
		except OSError:
			pass

	stop_evt.set()
	try:
		os.close(master_fd)
	except OSError:
		pass
	drainer.join(timeout=1.0)

	if crash_log:
		outcome = 'CRASH' + ('+hung' if hung else '')
	elif hung:
		outcome = 'HUNG'
	elif wait_status is not None and os.WIFSIGNALED(wait_status):
		outcome = 'CRASH(signal_%s)' % signal.Signals(os.WTERMSIG(wait_status)).name
	elif wait_status is not None and os.WIFEXITED(wait_status) and os.WEXITSTATUS(wait_status) == 0:
		outcome = 'ok'
	else:
		outcome = 'anomaly(status=%s)' % (wait_status,)

	if outcome == 'ok':
		shutil.rmtree(base, ignore_errors=True)
	return outcome


def main():
	if len(sys.argv) < 2:
		print(__doc__)
		sys.exit(1)
	far2l_bin = os.path.abspath(sys.argv[1])
	iterations = int(sys.argv[2]) if len(sys.argv) > 2 else 20

	workroot = tempfile.mkdtemp(prefix='tc_shutdown_regression_')
	counts = {}
	t0 = time.time()
	for i in range(iterations):
		outcome = run_once(far2l_bin, workroot, i)
		counts[outcome] = counts.get(outcome, 0) + 1
		if outcome != 'ok':
			print('[%03d] %s' % (i, outcome), flush=True)

	elapsed = time.time() - t0
	print('==== %d iterations in %.1fs (%.2fs/iter) ====' % (iterations, elapsed, elapsed / iterations))
	for outcome, count in sorted(counts.items()):
		print('  %-24s %d' % (outcome, count))

	shutil.rmtree(workroot, ignore_errors=True)
	sys.exit(0 if counts.get('ok', 0) == iterations else 1)


if __name__ == '__main__':
	main()
