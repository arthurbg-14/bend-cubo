// Sys
// ===
//
// Sys.run(cmd): runs cmd through /bin/sh on a worker thread, and answers
// "<exit code> <milliseconds>\n" followed by everything it printed.

#include <stdio.h>
#include <time.h>

static void sys_run_call(IoWork* w) {
  char* cmd = (char*)w->data;
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  FILE* p = popen(cmd, "r");
  free(cmd);
  size_t cap = 4096, len = 64;
  char* out = malloc(cap);
  if (p != NULL) {
    size_t got;
    while ((got = fread(out + len, 1, cap - len, p)) > 0) {
      len += got;
      if (len == cap) {
        cap *= 2;
        out = realloc(out, cap);
      }
    }
  }
  int st = p == NULL ? -1 : pclose(p);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  long ms = (t1.tv_sec - t0.tv_sec) * 1000 + (t1.tv_nsec - t0.tv_nsec) / 1000000;
  int code = st == -1 ? 127 : WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st);
  char head[64];
  int hn = snprintf(head, sizeof head, "%d %ld\n", code, ms);
  size_t body = len - 64;
  memmove(out + hn, out + 64, body);
  memcpy(out, head, hn);
  w->data = out;
  w->size = hn + body;
  w->code = 0;
}

static Term sys_run_pack(Env e, IoWork* w) {
  Term r = io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return r;
}

Term sys_run_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  w->data = io_cstr(e, f[0], &n);
  return io_work(w, sys_run_call, sys_run_pack);
}

static void __attribute__((constructor)) sys_run_use(void) {
  io_eff(CID_SYS_RUN, sys_run_run, 0);
}
