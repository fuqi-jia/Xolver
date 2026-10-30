/* Linux x86-64 adapter for the pinned QCP binary. Only its in-memory SAT entry
 * is replaced. There is deliberately no trampoline to the original backend.
 * The host retains its preprocessing, branch classification and VC generation.
 */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <endian.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <link.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static uintptr_t image_base;
static int worker_socket = -1;
static pid_t worker_pid = -1;
static uint64_t invocation;
static void (*native_print)(void *, FILE *);

static void fail(const char *message) {
    dprintf(STDERR_FILENO, "qcp selected backend: %s\n", message);
    _exit(125);
}

static uint64_t now_ns(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value)) fail("cannot read wall clock");
    return (uint64_t)value.tv_sec * 1000000000 + (uint64_t)value.tv_nsec;
}

static void transfer(void *buffer, size_t length, int sending, uint64_t deadline) {
    unsigned char *next = buffer;
    while (length) {
        uint64_t now = now_ns();
        if (now >= deadline) fail("native SAT query exhausted its 60 second wall budget");
        uint64_t remaining_ms = (deadline - now + 999999) / 1000000;
        struct pollfd descriptor = {worker_socket, sending ? POLLOUT : POLLIN, 0};
        int ready = poll(&descriptor, 1, (int)remaining_ms);
        if (ready < 0 && errno == EINTR) continue;
        if (ready <= 0) fail("backend worker wait failed or timed out");
        ssize_t count = sending ? send(worker_socket, next, length, MSG_NOSIGNAL)
                                : recv(worker_socket, next, length, 0);
        if (count < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)) continue;
        if (count <= 0) fail("backend worker disconnected");
        next += count;
        length -= (size_t)count;
    }
}

static int selected_decision(void *node, int mode) {
    uint64_t started = now_ns(), deadline = started + 60000000000ULL;
    uintptr_t caller = (uintptr_t)__builtin_return_address(0) - image_base;
    if (!node || (mode != 0 && mode != 1)) fail("invalid native SAT argument");
    char *formula = NULL;
    size_t length = 0;
    FILE *stream = open_memstream(&formula, &length);
    if (!stream) fail("cannot create native formula stream");
    native_print(node, stream);
    if (fclose(stream)) fail("cannot finish native formula stream");
    if (!length || length > 16 * 1024 * 1024) fail("native formula size is unsupported");
    uint32_t prefix[] = {htonl((uint32_t)length), htonl((uint32_t)mode)};
    uint64_t metadata[] = {htobe64(invocation++), htobe64(caller), htobe64(started)};
    transfer(prefix, sizeof(prefix), 1, deadline);
    transfer(metadata, sizeof(metadata), 1, deadline);
    transfer(formula, length, 1, deadline);
    free(formula);
    unsigned char reply;
    transfer(&reply, 1, 0, deadline);
    if (now_ns() >= deadline) fail("native SAT response arrived after its wall budget");
    if (reply == '0') return 0;
    if (reply == '1') return 1;
    /* QCP's ABI has no established unknown result. Stop this invocation rather
     * than manufacture SAT/UNSAT or call its original solver. The worker keeps
     * unknown, unsupported, timeout and protocol-error records separately. */
    fail("selected solver did not produce a definite SAT/UNSAT result; see query record");
    return -2;
}

static void finish_worker(void) {
    if (worker_socket >= 0) close(worker_socket);
    if (worker_pid <= 0) return;
    for (int retry = 0; retry < 200; ++retry) {
        int status;
        pid_t result = waitpid(worker_pid, &status, WNOHANG);
        if (result == worker_pid || (result < 0 && errno == ECHILD)) return;
        struct timespec pause = {0, 10000000};
        nanosleep(&pause, NULL);
    }
    kill(worker_pid, SIGKILL);
    while (waitpid(worker_pid, NULL, 0) < 0 && errno == EINTR) {}
}

static const char *setting(const char *name) {
    const char *value = getenv(name);
    if (!value || !*value) fail("missing selected backend configuration");
    return value;
}

static void start_worker(void) {
    const char *python = setting("XOLVER_QCP_PYTHON");
    const char *worker = setting("XOLVER_QCP_WORKER");
    const char *backend = setting("XOLVER_QCP_BACKEND");
    const char *solver = setting("XOLVER_QCP_SOLVER");
    const char *guard = setting("XOLVER_QCP_EXEC_GUARD");
    const char *output = setting("XOLVER_QCP_OUTPUT");
    char folder[PATH_MAX];
    if (snprintf(folder, sizeof(folder), "%s/session-%ld", output, (long)getpid()) >= (int)sizeof(folder))
        fail("session path is too long");
    if (mkdir(folder, 0700)) fail("cannot create unique backend session directory");
    int sockets[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets)) fail("cannot create worker socket");
    pid_t parent = getpid();
    worker_pid = fork();
    if (worker_pid < 0) fail("cannot start worker");
    if (worker_pid == 0) {
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) || getppid() != parent) _exit(126);
        close(sockets[0]);
        if (fcntl(sockets[1], F_SETFD, 0)) _exit(126);
        char descriptor[32];
        snprintf(descriptor, sizeof(descriptor), "%d", sockets[1]);
        /* LD_PRELOAD may also be present in a controller's Python/Rocq children.
         * Inode guards protect those executables; the worker and solvers need
         * no preload at all. */
        unsetenv("LD_PRELOAD");
        execl(python, python, worker, "--worker-fd", descriptor,
              "--backend", backend, "--solver", solver, "--exec-guard", guard,
              "--output", folder, (char *)NULL);
        _exit(126);
    }
    close(sockets[1]);
    worker_socket = sockets[0];
    if (fcntl(worker_socket, F_SETFL, O_NONBLOCK)) fail("cannot bound worker socket waits");
    if (atexit(finish_worker)) fail("cannot register worker cleanup");
}

struct MainImage { uintptr_t base; int found; };
static int find_image(struct dl_phdr_info *info, size_t size, void *opaque) {
    (void)size;
    if (info->dlpi_name && info->dlpi_name[0]) return 0;
    struct MainImage *image = opaque;
    for (size_t i = 0; i < info->dlpi_phnum; ++i) {
        const ElfW(Phdr) *segment = &info->dlpi_phdr[i];
        if (segment->p_type == PT_LOAD && (segment->p_flags & PF_X) &&
            segment->p_vaddr <= 0x1198ed0 && 0x1199eec <= segment->p_vaddr + segment->p_memsz) {
            image->base = info->dlpi_addr;
            image->found = 1;
        }
    }
    return 1;
}

__attribute__((constructor)) static void initialize_backend(void) {
    const char *target = getenv("XOLVER_QCP_BINARY");
    if (!target || !*target) return;
    struct stat executable, expected_file;
    if (stat("/proc/self/exe", &executable) || stat(target, &expected_file))
        fail("cannot identify the selected QCP executable");
    if (executable.st_dev != expected_file.st_dev || executable.st_ino != expected_file.st_ino)
        return;
    struct MainImage image = {0, 0};
    dl_iterate_phdr(find_image, &image);
    if (!image.found) fail("pinned QCP executable mapping is absent");
    image_base = image.base;
    uintptr_t entry = image_base + 0x1199ee0;
    const unsigned char prologue[] = {0x55, 0x48, 0x89, 0xe5, 0x41, 0x57,
                                      0x41, 0x56, 0x41, 0x55, 0x41, 0x54};
    if (memcmp((const void *)entry, prologue, sizeof(prologue))) fail("QCP SAT ABI changed");
    const uintptr_t sites[] = {0x116d585, 0x116d595};
    for (size_t i = 0; i < sizeof(sites) / sizeof(sites[0]); ++i) {
        const unsigned char *code = (const void *)(image_base + sites[i]);
        int32_t displacement;
        memcpy(&displacement, code + 1, sizeof(displacement));
        if (code[0] != 0xe8 || (uintptr_t)(code + 5 + displacement) != entry)
            fail("QCP SAT call sites changed");
    }
    native_print = (void (*)(void *, FILE *))(image_base + 0x1198ed0);
    start_worker();
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0) fail("invalid memory page size");
    uintptr_t page = entry & ~((uintptr_t)page_size - 1);
    if (entry + sizeof(prologue) > page + (uintptr_t)page_size) fail("SAT entry crosses a page");
    if (mprotect((void *)page, (size_t)page_size, PROT_READ | PROT_WRITE | PROT_EXEC))
        fail("cannot install selected SAT backend");
    unsigned char *code = (void *)entry;
    uintptr_t callback = (uintptr_t)selected_decision;
    code[0] = 0x48; code[1] = 0xb8;
    memcpy(code + 2, &callback, sizeof(callback));
    code[10] = 0xff; code[11] = 0xe0;
    __builtin___clear_cache((char *)code, (char *)code + sizeof(prologue));
    if (mprotect((void *)page, (size_t)page_size, PROT_READ | PROT_EXEC))
        fail("cannot restore SAT entry memory protection");
}
