#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/wait.h>
extern char **environ;
static inline lean_obj_res lsys_ret(int64_t rc) {
    uint64_t p = rc < 0 ? ((1ULL << 63) | ((uint64_t)(uint32_t)errno << 32)) : ((uint64_t)rc & 0x7FFFFFFFFFFFFFFFULL);
    return lean_io_result_mk_ok(lean_box_uint64(p));
}
LEAN_EXPORT lean_obj_res leansys_open_flock(b_lean_obj_arg path, uint8_t wr, uint8_t ex, uint8_t nb) {
    if (wr == 3) return lsys_ret(close((int)((uint32_t)ex | ((uint32_t)nb << 8))));
    int fd = open(lean_string_cstr(path), O_CLOEXEC | (wr ? (O_CREAT | O_RDWR | (wr == 2 ? O_APPEND : 0) | (wr == 4 ? O_TRUNC : 0)) : O_RDONLY), 0644);
    if (fd >= 0 && ex && flock(fd, LOCK_EX | (nb ? LOCK_NB : 0)) < 0) { int e = errno; close(fd); errno = e; return lsys_ret(-1); }
    return lsys_ret(fd);
}
LEAN_EXPORT lean_obj_res leansys_fs_clone_or_link(b_lean_obj_arg src, b_lean_obj_arg dst, uint8_t is_ren) {
    const char *s = lean_string_cstr(src), *d = lean_string_cstr(dst);
    return lsys_ret(is_ren ? rename(s, d) : (unlink(d), link(s, d)));
}
LEAN_EXPORT lean_obj_res leansys_write_all(uint32_t fd, b_lean_obj_arg ba, size_t off, size_t len, uint8_t do_sync) {
    size_t sz = lean_sarray_size(ba); if (off > sz || len > sz - off) { errno = EINVAL; return lsys_ret(-1); }
    for (const uint8_t *p = lean_sarray_cptr(ba) + off, *end = p + len; p < end;) {
        ssize_t w = send((int)fd, p, (size_t)(end - p), MSG_NOSIGNAL);
        if (w < 0 && (errno == ENOTSOCK || errno == EBADF || errno == EINVAL)) w = write((int)fd, p, (size_t)(end - p));
        if (w < 0) { if (errno == EINTR) continue; return lsys_ret(-1); }
        p += (size_t)w;
    }
    return lsys_ret((do_sync && fsync((int)fd) < 0) ? -1 : (int64_t)len);
}
LEAN_EXPORT lean_obj_res leansys_pread_ba(uint32_t fd, uint64_t off, size_t max_len) {
    lean_object *ba = lean_alloc_sarray(1, 0, max_len);
    ssize_t n = (off == UINT64_MAX) ? read((int)fd, lean_sarray_cptr(ba), max_len) : pread((int)fd, lean_sarray_cptr(ba), max_len, (off_t)off);
    if (n > 0) lean_sarray_set_size(ba, (size_t)n);
    return lean_io_result_mk_ok(ba);
}
LEAN_EXPORT lean_obj_res leansys_spawn_group(b_lean_obj_arg cmd, b_lean_obj_arg args) {
    size_t n = lean_array_size(args); char *argv[66]; argv[0] = (char*)lean_string_cstr(cmd);
    for (size_t i = 0; i < n && i < 64; i++) argv[i + 1] = (char*)lean_string_cstr(lean_array_get_core(args, i));
    argv[(n < 64 ? n : 64) + 1] = NULL; pid_t pid = fork();
    if (pid == 0) { setpgid(0, 0); execve(argv[0], argv, environ); _exit(127); }
    if (pid > 0) setpgid(pid, pid);
    return lsys_ret(pid);
}
LEAN_EXPORT lean_obj_res leansys_kill_wait_group(uint32_t pid, uint32_t sig, uint8_t nohang) {
    if (sig > 0 && pid > 1) kill(-(pid_t)pid, (int)sig);
    int st = 0; pid_t r = waitpid((pid_t)pid, &st, nohang ? WNOHANG : 0);
    return lsys_ret(r <= 0 ? r : ((int64_t)r << 16) | (WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st)));
}
LEAN_EXPORT lean_obj_res leansys_net_listen(b_lean_obj_arg host, uint16_t port, uint32_t backlog) {
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0), one = 1; if (fd < 0) return lsys_ret(-1);
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons(port) }; socklen_t al = sizeof(a);
    if (inet_pton(AF_INET, lean_string_cstr(host), &a.sin_addr) <= 0) a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if ((backlog == 0 ? connect(fd, (struct sockaddr*)&a, al) : (bind(fd, (struct sockaddr*)&a, al) | listen(fd, (int)backlog))) < 0) { int e = errno; close(fd); errno = e; return lsys_ret(-1); }
    getsockname(fd, (struct sockaddr*)&a, &al); return lsys_ret(backlog == 0 ? fd : (((int64_t)ntohs(a.sin_port) << 32) | (uint32_t)fd));
}
LEAN_EXPORT lean_obj_res leansys_net_accept_poll(uint32_t lfd, uint32_t timeout_ms) {
    struct pollfd p = { .fd = (int)lfd, .events = POLLIN }; int r = poll(&p, 1, (int)timeout_ms);
    return lsys_ret(r <= 0 ? (r == 0 ? (errno = EAGAIN, -1) : -1) : accept4((int)lfd, NULL, NULL, SOCK_CLOEXEC));
}
