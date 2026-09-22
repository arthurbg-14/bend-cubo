// Sys
// ===
//
// Sys.run(cmd): runs cmd through /bin/sh and answers
// "<exit code> <milliseconds>\n" followed by everything it printed.

function sys_run(cmd) {
  const t0 = performance.now();
  const r = Bun.spawnSync(["/bin/sh", "-c", cmd], { stdout: "pipe", stderr: "inherit" });
  const ms = Math.round(performance.now() - t0);
  const code = r.exitCode === null ? 128 : r.exitCode;
  return io_done(code + " " + ms + "\n" + new TextDecoder().decode(r.stdout));
}
