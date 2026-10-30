/* Keep a selected backend from surviving its worker, including after setsid. */
#define _POSIX_C_SOURCE 200809L
#include <signal.h>
#include <stdio.h>
#include <sys/prctl.h>
#include <unistd.h>

int main(int argc, char **argv) {
    pid_t parent = getppid();
    if (argc < 2 || parent == 1 || prctl(PR_SET_PDEATHSIG, SIGKILL) ||
        getppid() != parent) return 126;
    execvp(argv[1], argv + 1);
    perror("qcp backend exec");
    return 126;
}
