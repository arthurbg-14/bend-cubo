# AGENTS

Cubo is written in Bend 2 (github.com/bendlang/bend). When working on it:

- run `bend guide` (and `bend guide shaders`) to learn Bend before writing any
- the rules of the game are laws in `LAWS.bend`: the human states them, do not
  weaken them to make a change pass
- `bend PROOF.bend` must print "All terms check." before any commit; a change
  that breaks a law is fixed in the code (or its proof), never in the law
- no `@unsafe`, no `?TODO`, no axioms
- polynomial identities in proofs go through `ring.bend`'s `R.eq`; every
  decision in the physics is a Bool handed to a helper, so a lemma can take
  it as a parameter
- the GPU draws (effs/scene.comp.in, through Vulkan in effs/screen.c); the
  simulation is Bend; `tools/order.py file.bend` puts a file's defs in an
  order Bend accepts
- measure with `./bench` (the simulation) and `./cubo still` (the GPU's time
  in the HUD) before and after a performance change
- after touching world.bend, `./build.sh test` must print OK five times: no
  cube inside another, none made or lost, for the list, the octree, the
  colored blocks, the flat array and the game's mix; bit-for-bit comparisons
  between versions are not the test (a different order of the ticks is a
  different, equally valid, simulation)
- no number of cells is written by hand: a neighbour sweep takes its cells
  from the cube's size and the tick's reach (`W.lo`, `W.span`), so the
  physics never depends on how big a cube is
- when `bend PROOF.bend` gets slow, `bend tools/optimize.bend auto <copy>`
  on a copy of the repo times every proof on its own, tries the rewrites the
  slow ones point at, keeps only what checks and helps, and checks all of
  PROOF.bend before and after; `profile <copy>` alone says where the time
  goes. The checker normalizes both sides of every equation in full, so an
  undecided value copied into many places (a let, a match that answers a
  record) is what costs

    phys.bend     the proven physics: bodies, friction, pushes, gated moves, the tick
    ring.bend     the ring tactic (a proven polynomial normalizer)
    world.bend    the endless world: generator, trie of changed cells, sleep and wake
    main.bend     the game: input, camera, tunable constants, HUD, frame loop
    LAWS.bend     the laws          PROOF.bend   their proofs
    bench.bend    the headless benchmark
    clash.bend    the collision test
    effs/         scene.comp.in (the shader), screen.c (Vulkan, window, events),
                  font.glsl (HUD font), spv.sh (shader to SPIR-V in screen.c)
    tools/optimize.bend  the proof optimizer (tools/opt/: prof, hoist, lift, auto)
