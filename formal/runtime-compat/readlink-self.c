#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
/* Lean 4.19 uses /proc/<pid>/exe; this runtime exposes /proc/self/exe. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  ssize_t result = original(path, buf, size);
  if (result == -1) {
    char own[64];
    snprintf(own, sizeof own, "/proc/%d/exe", (int)getpid());
    if (strcmp(path, own) == 0) return original("/proc/self/exe", buf, size);
  }
  return result;
}
