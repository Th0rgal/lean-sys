#ifndef __APPLE__
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
static inline int64_t fail_close(int fd) { int e = errno; return close(fd), errno = e, -1; }
#ifdef __APPLE__
#include <TargetConditionals.h>
#include <sys/clonefile.h>
#define MSG_NOSIGNAL 0
#define LS_CLONE(s, d) (clonefile(s, d, 0) == 0 ? 0 : link(s, d))
#define LS_FSYNC(fd) (fcntl(fd, F_BARRIERFSYNC) < 0 && fsync(fd) < 0)
static inline int ls_accept(int lfd) { int c = accept(lfd, NULL, NULL); return c >= 0 ? (fcntl(c, F_SETFD, FD_CLOEXEC), c) : -1; }
static inline int ls_ll(const char *ro, const char *rw) { return (void)ro, (void)rw, errno = EOPNOTSUPP, -1; }
#else
#include <linux/landlock.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#define LS_CLONE(s, d) link(s, d)
#define LS_FSYNC(fd) (fsync(fd) < 0)
static inline int ls_accept(int lfd) { return accept4(lfd, NULL, NULL, SOCK_CLOEXEC); }
static inline int ls_rule(int rfd, const char *p, uint64_t acc, int opt) { int f = *p ? open(p, O_PATH | O_CLOEXEC) : -2; struct stat st; struct landlock_path_beneath_attr b = { .allowed_access = acc, .parent_fd = f }; return (f == -2 || (f < 0 && opt && errno == ENOENT)) ? 0 : (f < 0 ? -1 : ((fstat(f, &st) == 0 && !S_ISDIR(st.st_mode) ? (b.allowed_access &= 0x4007ULL) : 0), syscall(__NR_landlock_add_rule, rfd, LANDLOCK_RULE_PATH_BENEATH, &b, 0) ? (int)fail_close(f) : (close(f), 0))); }
static inline int ls_ll(const char *ro, const char *rw) { int v = (int)syscall(__NR_landlock_create_ruleset, NULL, 0, LANDLOCK_CREATE_RULESET_VERSION), r = -1; uint64_t m = v < 2 ? 0x1FFFULL : (v == 2 ? 0x3FFFULL : 0x7FFFULL); struct landlock_ruleset_attr a = { .handled_access_fs = m }; return (!ro || v <= 0) ? (v <= 0 && (errno == ENOSYS || errno == EOPNOTSUPP || !v) ? (errno = EOPNOTSUPP, -1) : v) : ((prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) < 0 || (r = (int)syscall(__NR_landlock_create_ruleset, &a, sizeof(uint64_t), 0)) < 0) ? -1 : ((ls_rule(r, "/usr", 13ULL, 1) || ls_rule(r, "/lib", 13ULL, 1) || ls_rule(r, "/lib64", 13ULL, 1) || ls_rule(r, "/bin", 13ULL, 1) || ls_rule(r, ro, 13ULL, 0) || ls_rule(r, rw, m, 0) || syscall(__NR_landlock_restrict_self, r, 0)) ? (int)fail_close(r) : (close(r), 0))); }
#endif
int rename(const char *, const char *); extern char **environ; uint8_t leansys_verify_slice_bounds(uint64_t, uint64_t, uint64_t);
#define SA (struct sockaddr*)
static inline int ls_mok(int fd, uint64_t o, uint64_t n) { struct stat s; return fstat(fd, &s) < 0 ? 0 : (s.st_size >= 0 && leansys_verify_slice_bounds(o, n, (uint64_t)s.st_size) && leansys_verify_slice_bounds(o, n, SIZE_MAX) ? 1 : (errno = EINVAL, 0)); } static inline lean_obj_res R(int64_t rc) { return lean_io_result_mk_ok(lean_box_uint64(rc < 0 ? ((1ULL << 63) | ((uint64_t)(uint32_t)errno << 32)) : ((uint64_t)rc & 0x7FFFFFFFFFFFFFFFULL))); }
LEAN_EXPORT lean_obj_res leansys_open_flock(b_lean_obj_arg path, uint8_t wr, uint8_t ex, uint32_t aux) { struct stat st; int fl = O_CLOEXEC | (wr ? ((wr == 5 ? 0 : O_CREAT) | O_RDWR | (wr == 2 ? O_APPEND : 0) | (wr == 4 ? O_TRUNC : 0) | (ex == 2 ? O_EXCL : 0)) : O_RDONLY), fd = (wr == 3 || wr >= 7) ? -2 : open(lean_string_cstr(path), fl, wr == 1 && aux == 444 ? 0444 : 0644);
    return R(wr == 3 ? close((int)aux) : (wr == 7 ? (fstat((int)aux, &st) < 0 ? -1 : st.st_size) : (wr == 8 ? fcntl((int)aux, F_DUPFD_CLOEXEC, (int)ex * 65536) : (wr == 9 ? ls_ll(NULL, "") : (fd >= 0 && ex == 1 && flock(fd, LOCK_EX | (aux ? LOCK_NB : 0)) < 0 ? fail_close(fd) : fd))))); }
LEAN_EXPORT lean_obj_res leansys_fs_clone_or_link(b_lean_obj_arg src, b_lean_obj_arg dst, uint8_t op) { const char *s = lean_string_cstr(src), *d = lean_string_cstr(dst); struct stat st; return R(op == 1 ? rename(s, d) : (op == 2 ? chmod(s, 0444) : (op == 3 ? (stat(s, &st) < 0 ? -1 : st.st_size) : (op == 4 ? ls_ll(s, d) : (unlink(d), LS_CLONE(s, d)))))); }
LEAN_EXPORT lean_obj_res leansys_write_all(uint32_t fd, b_lean_obj_arg ba, size_t off, size_t len, uint8_t mode) { size_t sz = lean_sarray_size(ba); int ok = mode == 3 ? 1 : (mode <= 2 && leansys_verify_slice_bounds(mode == 2 ? 0 : off, len, sz) ? (mode == 2 ? ls_mok((int)fd, off, len) : 1) : (errno = EINVAL, 0)); void *m = mode == 3 ? (ftruncate((int)fd, (off_t)off) < 0 ? NULL : &sz) : (mode == 2 && ok && len ? mmap(NULL, off + len, PROT_READ | PROT_WRITE, MAP_SHARED, (int)fd, 0) : MAP_FAILED);
    if (mode >= 2 || !ok) return mode == 3 ? R(m ? 0 : -1) : (m != MAP_FAILED ? (memcpy((uint8_t*)m + off, lean_sarray_cptr(ba), len), munmap(m, off + len), R((int64_t)len)) : R(mode == 2 && ok && !len ? 0 : -1));
    for (const uint8_t *p = lean_sarray_cptr(ba) + off, *end = p + len; p < end;) { ssize_t t = send((int)fd, p, (size_t)(end - p), MSG_NOSIGNAL), w = (t < 0 && (errno == ENOTSOCK || errno == EBADF || errno == EINVAL)) ? write((int)fd, p, (size_t)(end - p)) : t; if (w == 0 ? (errno = EIO, 1) : (w < 0 && errno != EINTR)) return R(-1); p += w > 0 ? (size_t)w : 0; }
    return R((mode == 1 && LS_FSYNC((int)fd)) ? -1 : (int64_t)len); }
LEAN_EXPORT lean_obj_res leansys_pread_ba(uint32_t fd, uint64_t off, size_t max_len) { lean_object *ba = lean_alloc_sarray(1, 0, max_len); uint64_t mo = off & 0x3FFFFFFFFFFFFFFFULL; void *m = (off >> 62) == 2 && ls_mok((int)fd, mo, max_len) && max_len ? mmap(NULL, (size_t)(mo + max_len), PROT_READ, MAP_SHARED, (int)fd, 0) : MAP_FAILED; ssize_t n = 0;
    do { n = m != MAP_FAILED ? (memcpy(lean_sarray_cptr(ba), (uint8_t*)m + (size_t)mo, max_len), munmap(m, (size_t)(mo + max_len)), (ssize_t)max_len) : (off == UINT64_MAX ? read((int)fd, lean_sarray_cptr(ba), max_len) : ((off >> 62) == 2 ? (ssize_t)(max_len ? -1 : 0) : pread((int)fd, lean_sarray_cptr(ba), max_len, (off_t)off))); } while (n < 0 && errno == EINTR && (off >> 62) != 2);
    return (n > 0 ? lean_sarray_set_size(ba, (size_t)n) : (void)0), lean_io_result_mk_ok(ba); }
LEAN_EXPORT lean_obj_res leansys_spawn_group(b_lean_obj_arg cmd, b_lean_obj_arg args, b_lean_obj_arg ro, b_lean_obj_arg rw, uint8_t confine) {
#if defined(__APPLE__) && defined(TARGET_OS_IPHONE) && TARGET_OS_IPHONE
    return (void)cmd, (void)args, (void)ro, (void)rw, (void)confine, errno = ENOSYS, R(-1); }
#else
    size_t n = lean_array_size(args), m = n < 64 ? n : 64; char *argv[66] = { (char*)lean_string_cstr(cmd) };
    for (size_t i = 0; i < m; i++) argv[i + 1] = (char*)lean_string_cstr(lean_array_get_core(args, i));
    pid_t pid = fork(); if (pid == 0) _exit((setpgid(0, 0), confine && ls_ll(lean_string_cstr(ro), lean_string_cstr(rw)) < 0) ? 126 : (execve(argv[0], argv, environ), 127));
    return (pid > 0 ? (void)setpgid(pid, pid) : (void)0), R(pid); }
#endif
LEAN_EXPORT lean_obj_res leansys_kill_wait_group(uint32_t pid, uint32_t sig, uint8_t nohang) { int st = (sig > 0 && pid > 1 ? kill(-(pid_t)pid, (int)sig) : 0, 0); pid_t r = waitpid((pid_t)pid, &st, nohang ? WNOHANG : 0);
    return R(r <= 0 ? r : ((int64_t)r << 16) | (WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st))); }
LEAN_EXPORT lean_obj_res leansys_net_listen(b_lean_obj_arg host, uint16_t port, uint32_t backlog) { int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0), one = 1; struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port), .sin_addr.s_addr = htonl(INADDR_LOOPBACK) }; socklen_t al = sizeof(a);
    return (fd < 0 || (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one)), (inet_pton(AF_INET, lean_string_cstr(host), &a.sin_addr) != 1 ? (errno = EINVAL, -1) : (backlog == 0 ? connect(fd, SA &a, al) : ((bind(fd, SA &a, al) < 0 || listen(fd, (int)backlog) < 0) ? -1 : 0))) < 0)) ? R(fd < 0 ? -1 : fail_close(fd)) : (getsockname(fd, SA &a, &al), R(backlog == 0 ? fd : (((int64_t)ntohs(a.sin_port) << 32) | (uint32_t)fd))); }
LEAN_EXPORT lean_obj_res leansys_net_accept_poll(uint32_t lfd, uint32_t timeout_ms, uint8_t poll_only) { struct pollfd p = { .fd = (int)lfd, .events = POLLIN }; int r = poll(&p, 1, (int)timeout_ms);
    return R(r <= 0 ? (r == 0 ? (errno = EAGAIN, -1) : -1) : (poll_only ? (p.revents & POLLIN ? 1 : 0) : ls_accept((int)lfd))); }
