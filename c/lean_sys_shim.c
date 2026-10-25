#ifndef __APPLE__
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/wait.h>
#ifdef __APPLE__
#include <TargetConditionals.h>
#include <sys/clonefile.h>
#define MSG_NOSIGNAL 0
#define LS_CLONE(s, d) (clonefile(s, d, 0) == 0 ? 0 : link(s, d))
#define LS_FSYNC(fd) (fcntl(fd, F_BARRIERFSYNC) < 0 && fsync(fd) < 0)
static inline int ls_accept(int lfd) { int c = accept(lfd, NULL, NULL); if (c >= 0) fcntl(c, F_SETFD, FD_CLOEXEC); return c; }
#else
#define LS_CLONE(s, d) link(s, d)
#define LS_FSYNC(fd) (fsync(fd) < 0)
static inline int ls_accept(int lfd) { return accept4(lfd, NULL, NULL, SOCK_CLOEXEC); }
#endif
int rename(const char *, const char *); extern char **environ;
#define SA (struct sockaddr*)
static inline lean_obj_res R(int64_t rc) { return lean_io_result_mk_ok(lean_box_uint64(rc < 0 ? ((1ULL << 63) | ((uint64_t)(uint32_t)errno << 32)) : ((uint64_t)rc & 0x7FFFFFFFFFFFFFFFULL))); }
static inline int64_t fail_close(int fd) { int e = errno; close(fd); errno = e; return -1; }
LEAN_EXPORT lean_obj_res leansys_open_flock(b_lean_obj_arg path, uint8_t wr, uint8_t ex, uint8_t nb) {
    if (wr == 3) return R(close((int)((uint32_t)ex | ((uint32_t)nb << 8))));
    int fd = open(lean_string_cstr(path), O_CLOEXEC | (wr ? (O_CREAT | O_RDWR | (wr == 2 ? O_APPEND : 0) | (wr == 4 ? O_TRUNC : 0)) : O_RDONLY), 0644);
    return R(fd >= 0 && ex && flock(fd, LOCK_EX | (nb ? LOCK_NB : 0)) < 0 ? fail_close(fd) : fd); }
LEAN_EXPORT lean_obj_res leansys_fs_clone_or_link(b_lean_obj_arg src, b_lean_obj_arg dst, uint8_t is_ren) { const char *s = lean_string_cstr(src), *d = lean_string_cstr(dst); return R(is_ren ? rename(s, d) : (unlink(d), LS_CLONE(s, d))); }
LEAN_EXPORT lean_obj_res leansys_write_all(uint32_t fd, b_lean_obj_arg ba, size_t off, size_t len, uint8_t do_sync) {
    size_t sz = lean_sarray_size(ba); if (off > sz || len > sz - off) { errno = EINVAL; return R(-1); }
    for (const uint8_t *p = lean_sarray_cptr(ba) + off, *end = p + len; p < end;) {
        ssize_t w = send((int)fd, p, (size_t)(end - p), MSG_NOSIGNAL);
        if (w < 0 && (errno == ENOTSOCK || errno == EBADF || errno == EINVAL)) w = write((int)fd, p, (size_t)(end - p));
        if (w < 0) { if (errno == EINTR) continue; return R(-1); } p += (size_t)w; }
    return R((do_sync && LS_FSYNC((int)fd)) ? -1 : (int64_t)len); }
LEAN_EXPORT lean_obj_res leansys_pread_ba(uint32_t fd, uint64_t off, size_t max_len) {
    lean_object *ba = lean_alloc_sarray(1, 0, max_len); ssize_t n = (off == UINT64_MAX) ? read((int)fd, lean_sarray_cptr(ba), max_len) : pread((int)fd, lean_sarray_cptr(ba), max_len, (off_t)off);
    if (n > 0) lean_sarray_set_size(ba, (size_t)n); return lean_io_result_mk_ok(ba); }
LEAN_EXPORT lean_obj_res leansys_spawn_group(b_lean_obj_arg cmd, b_lean_obj_arg args) {
#if defined(__APPLE__) && defined(TARGET_OS_IPHONE) && TARGET_OS_IPHONE
    (void)cmd; (void)args; errno = ENOSYS; return R(-1); }
#else
    size_t n = lean_array_size(args), m = n < 64 ? n : 64; char *argv[66]; argv[0] = (char*)lean_string_cstr(cmd); argv[m + 1] = NULL;
    for (size_t i = 0; i < m; i++) argv[i + 1] = (char*)lean_string_cstr(lean_array_get_core(args, i));
    pid_t pid = fork(); if (pid == 0) { setpgid(0, 0); execve(argv[0], argv, environ); _exit(127); }
    if (pid > 0) setpgid(pid, pid); return R(pid); }
#endif
LEAN_EXPORT lean_obj_res leansys_kill_wait_group(uint32_t pid, uint32_t sig, uint8_t nohang) { if (sig > 0 && pid > 1) kill(-(pid_t)pid, (int)sig); int st = 0; pid_t r = waitpid((pid_t)pid, &st, nohang ? WNOHANG : 0);
    return R(r <= 0 ? r : ((int64_t)r << 16) | (WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st))); }
LEAN_EXPORT lean_obj_res leansys_net_listen(b_lean_obj_arg host, uint16_t port, uint32_t backlog) {
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0), one = 1; if (fd < 0) return R(-1); setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port) }; socklen_t al = sizeof(a);
    if (inet_pton(AF_INET, lean_string_cstr(host), &a.sin_addr) <= 0) a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if ((backlog == 0 ? connect(fd, SA &a, al) : (bind(fd, SA &a, al) | listen(fd, (int)backlog))) < 0) return R(fail_close(fd));
    getsockname(fd, SA &a, &al); return R(backlog == 0 ? fd : (((int64_t)ntohs(a.sin_port) << 32) | (uint32_t)fd)); }
LEAN_EXPORT lean_obj_res leansys_net_accept_poll(uint32_t lfd, uint32_t timeout_ms) { struct pollfd p = { .fd = (int)lfd, .events = POLLIN }; int r = poll(&p, 1, (int)timeout_ms);
    return R(r <= 0 ? (r == 0 ? (errno = EAGAIN, -1) : -1) : ls_accept((int)lfd)); }
