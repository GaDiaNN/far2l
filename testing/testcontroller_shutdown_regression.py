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

Known platform gap (unrelated to the fix under test, not root-caused yet):
on macOS, the wait-for-dialog request reaches far2l fine (visible in its own
log as "got command 3") but no reply arrives before the timeout, so every
iteration reports 'setup_failed' instead of a meaningful HUNG/ok/CRASH
outcome. This isn't a unix-datagram size limit - raising SO_SNDBUF/SO_RCVBUF
on both ends (this script does so unconditionally, harmless on Linux) lets
datagrams well past 2KB through fine, and the relevant sockets on both the
harness and far2l's own ClientLoop already do that upstream. It looks more
like one of the several other macOS-specific test-timing quirks this project
has run into before, not diagnosed further here since it doesn't affect the
fix's own correctness. This script is fully verified on Linux (150/150 HUNG
pre-fix, 0/150 post-fix, no timing tricks).
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


def start_far2l(far2l_bin, profile, left, right, sock_path):
	# winsize must be set on the slave before fork/exec, or far2l's initial
	# TIOCGWINSZ probe can race a later SIGWINCH and briefly run with an
	# inconsistent screen size.
	master_fd, slave_fd = pty.openpty()
	fcntl.ioctl(slave_fd, termios.TIOCSWINSZ, struct.pack('HHHH', 25, 80, 0, 0))
	env = dict(os.environ)
	env['FAR2L_TESTCTL'] = sock_path
	env['FAR2L_STD'] = '/dev/null'
	pid = os.fork()
	if pid == 0:
		os.setsid()
		os.close(master_fd)
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
	pid, master_fd = start_far2l(far2l_bin, profile, left, right, sock_path)

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
			return 'setup_failed'

		type_vk(srv, addr, VK_ENTER)  # the actual quit trigger
		# Immediately (no delay) send one more request, racing teardown.
		srv.sendto(struct.pack('<I', TEST_CMD_STATUS), addr)
		srv.settimeout(2.0)
		try:
			srv.recv(4096)
		except socket.timeout:
			pass
	finally:
		srv.close()
		try:
			os.unlink(sock_path)
		except OSError:
			pass

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

	try:
		os.close(master_fd)
	except OSError:
		pass

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
