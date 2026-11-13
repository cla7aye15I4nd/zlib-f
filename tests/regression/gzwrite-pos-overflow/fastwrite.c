/* Optional: a write() that behaves as the /dev/null device for the descriptor of wpos.c
   (it accepts every byte) without entering the kernel, so that the 2^34 writes of the
   zero fill take about a minute instead of about twenty. Every other descriptor goes to
   the real write(). Linked into the test program, it takes the place of libc's write()
   for the static libz.a. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>

extern int null_fd;

ssize_t write(int fd, const void *buf, size_t n) {
    static ssize_t (*real)(int, const void *, size_t);
    if (fd == null_fd)
        return (ssize_t)n;
    if (real == NULL)
        real = (ssize_t (*)(int, const void *, size_t))dlsym(RTLD_NEXT, "write");
    return real(fd, buf, n);
}
