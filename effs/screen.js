// Screen
// ======
// The JS target has no graphics: a frame hands the window and the header
// back with no events.

function screen_show(window, hdr) {
  return { $: "Tuple", fst: window, snd: { $: "Tuple", fst: hdr, snd: { $: "Nil" } } };
}
