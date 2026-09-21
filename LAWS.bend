# Cubo -- the laws. The human states them; PROOF.bend must prove them,
# and `bend PROOF.bend` fails while any is open or false.
#
# Every law holds for every value of the constants (gravity, friction,
# jump speed, the motor: they change while playing, main.bend), for every
# body and every set of obstacles around it -- not just the ones the game
# happens to make. Units (phys.bend): a tick is 1/128 s; a velocity v
# moves a body by v in half a tick, so a tick moves it by v + v' (start
# plus end: the average velocity); gravity g is the velocity lost per
# tick; the energy of a body is vx^2 + vy^2 + vz^2 + g y (kinetic plus
# potential, for unit mass, in those units). Signed numbers are
# Pos{n}/Neg{n}; a law about one writes it as pos - neg, without minus
# signs, by moving the negative parts to the other side.

import Base
import ./phys.bend as P

# Kinematics and energy in flight
# -------------------------------

# LAW: in the air, with no input, a tick that touches nothing keeps the
# body's mechanical energy exactly: what the rise costs in kinetic energy
# it gains in potential, and back on the way down.
law free_flight_energy:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for air: {P.Body.ground(b) == False{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
  {P.Body.energy(P.K.g(k), b2) == P.Body.energy(P.K.g(k), b) : Nat}

# LAW: the same tick is uniformly accelerated motion: gravity takes
# exactly g from the vertical velocity (v' = v - g), the horizontal one
# does not change (no friction in the air), and every coordinate moves by
# the start and end velocities added (x' = x + v + v').
law free_flight_kinematics:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for air: {P.Body.ground(b) == False{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
  {Nat.add(Nat.add(P.Z.pos(P.Body.vy(b2)), P.Z.neg(P.Body.vy(b))), P.K.g(k))
    == Nat.add(P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b2))) : Nat}
  & {Nat.add(Nat.add(P.Body.y(b2), P.Z.neg(P.Body.vy(b))), P.Z.neg(P.Body.vy(b2)))
    == Nat.add(Nat.add(P.Body.y(b), P.Z.pos(P.Body.vy(b))), P.Z.pos(P.Body.vy(b2))) : Nat}
  & {P.Body.vx(b2) == P.Body.vx(b) : P.Z}
  & {P.Body.vz(b2) == P.Body.vz(b) : P.Z}
  & {Nat.add(P.Body.x(b2), Nat.add(P.Z.neg(P.Body.vx(b)), P.Z.neg(P.Body.vx(b))))
    == Nat.add(P.Body.x(b), Nat.add(P.Z.pos(P.Body.vx(b)), P.Z.pos(P.Body.vx(b)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.add(P.Z.neg(P.Body.vz(b)), P.Z.neg(P.Body.vz(b))))
    == Nat.add(P.Body.z(b), Nat.add(P.Z.pos(P.Body.vz(b)), P.Z.pos(P.Body.vz(b)))) : Nat}

# LAW: a whole flight is the parabola of real physics. After n ticks in
# the air touching nothing (whatever the obstacles around, tick by tick),
# the body is exactly where uniformly accelerated motion puts it at the
# time of n ticks: v = v0 - g n, y = y0 + 2 n v0 - g n^2, and the
# horizontal x = x0 + 2 n vx0 (nothing slows it in the air). In meters
# and seconds -- a position unit is 2^-18 m, a velocity unit 2^-10 m/s, a
# tick 2^-7 s, so g is an acceleration of a = g/8 m/s^2 and n ticks are
# t = n/128 s -- 2 n v0 units are v0 t meters and g n^2 units are a t^2 / 2
# meters: y = y0 + v0 t - a t^2 / 2 and v = v0 - a t, free fall exactly
# as physics has it, with no error at any tick however long the flight.
law flight_is_parabola:
  for +k: P.K
  for +obss: List<&2, List<&2, P.Body>>
  for +b: P.Body
  for +free: {P.Flight.clear(k, obss, b) == True{} : Bool}
  n = List.length(&2, List<&2, P.Body>, obss)
  b2 = P.Flight.run(k, obss, b)
  {Nat.add(Nat.add(P.Z.pos(P.Body.vy(b2)), P.Z.neg(P.Body.vy(b))), Nat.mul(n, P.K.g(k)))
    == Nat.add(P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b2))) : Nat}
  & {Nat.add(Nat.add(P.Body.y(b2), Nat.mul(P.K.g(k), Nat.mul(n, n))), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vy(b))))
    == Nat.add(P.Body.y(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vy(b)))) : Nat}
  & {P.Body.vx(b2) == P.Body.vx(b) : P.Z}
  & {P.Body.vz(b2) == P.Body.vz(b) : P.Z}
  & {Nat.add(P.Body.x(b2), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vx(b))))
    == Nat.add(P.Body.x(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vx(b)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vz(b))))
    == Nat.add(P.Body.z(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vz(b)))) : Nat}

# LAW: a jump: standing, with no walking, a takeoff that touches nothing
# gives the body exactly jump^2 of vertical energy -- so, by
# free_flight_energy, it rises until g h = jump^2: the height of a jump is
# fixed by the conservation of energy.
law jump_energy:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for stand: {P.Body.ground(b) == True{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In{None{}, True{}}, b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In{None{}, True{}}, b))
  {P.Body.energy(P.K.g(k), b2)
    == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(b2)), P.Z.sq(P.Body.vz(b2))), Nat.mul(P.K.jump(k), P.K.jump(k))),
               Nat.mul(P.K.g(k), P.Body.y(b))) : Nat}

# LAW: no jumping in mid-air: off the ground, holding jump changes nothing
# (a jump pushes against something).
law no_air_jump:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +w: Maybe<&2, P.Wish>
  for +b: P.Body
  for air: {P.Body.ground(b) == False{} : Bool}
  {P.Body.tick(k, obs, P.In{w, True{}}, b) == P.Body.tick(k, obs, P.In{w, False{}}, b) : P.Body & List<&2, P.Body>}

# LAW: no steering in mid-air: off the ground, holding a direction changes
# nothing. The motor pushes against the ground; in flight there is nothing
# to push against.
law no_air_control:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +w: Maybe<&2, P.Wish>
  for +b: P.Body
  for air: {P.Body.ground(b) == False{} : Bool}
  {P.Body.tick(k, obs, P.In{w, False{}}, b) == P.Body.tick(k, obs, P.In.idle(), b) : P.Body & List<&2, P.Body>}

# The motor
# ---------

# LAW: the motor pushes the same however fast the cube already goes: on
# the ground, walking toward a direction adds exactly acc along it to the
# velocity, whatever the velocity is. There is no top speed, and the push
# neither fades nor grows with the speed.
law motor_is_steady:
  for +k: P.K
  for +b: P.Body
  for +ux: P.Z
  for +uz: P.Z
  for stand: {P.Body.ground(b) == True{} : Bool}
  b1 = P.Body.drive(k, P.In{Some{P.Wish{ux, uz}}, False{}}, b)
  b0 = P.Body.drive(k, P.In.idle(), b)
  {P.Body.vx(b1) == P.Z.add(P.Body.vx(b0), P.Z.q12(P.K.acc(k), ux)) : P.Z}
  & {P.Body.vz(b1) == P.Z.add(P.Body.vz(b0), P.Z.q12(P.K.acc(k), uz)) : P.Z}

# Friction
# --------

# LAW: on the ground, with no input, friction only slows: no component of
# the velocity grows, none turns around.
law friction_never_reverses:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for stand: {P.Body.ground(b) == True{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
  {Nat.is_le(P.Z.pos(P.Body.vx(b2)), P.Z.pos(P.Body.vx(b))) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vx(b2)), P.Z.neg(P.Body.vx(b))) == True{} : Bool}
  & {Nat.is_le(P.Z.pos(P.Body.vz(b2)), P.Z.pos(P.Body.vz(b))) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vz(b2)), P.Z.neg(P.Body.vz(b))) == True{} : Bool}

# LAW: Coulomb's law: the friction a tick applies, the velocity it takes
# (fx, fz), is at most mu g in size, in whatever direction the body
# slides: fx^2 + fz^2 <= (mu g)^2. Friction is mu N, and N = m g.
law coulomb_friction:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for stand: {P.Body.ground(b) == True{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
  fx = Nat.sub(P.Z.mag(P.Body.vx(b)), P.Z.mag(P.Body.vx(b2)))
  fz = Nat.sub(P.Z.mag(P.Body.vz(b)), P.Z.mag(P.Body.vz(b2)))
  {Nat.is_le(Nat.add(Nat.mul(fx, fx), Nat.mul(fz, fz)), Nat.mul(P.K.fric(k), P.K.fric(k))) == True{} : Bool}

# LAW: the work of friction: the kinetic energy a sliding body loses is
# exactly the friction times the distance it slides (per axis, f times
# v + v', the distance of the tick), and it slides that far: the
# work-energy theorem, with the kinematics of the tick.
law friction_work:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  for stand: {P.Body.ground(b) == True{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))) == False{} : Bool}
  b2 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
  ax = P.Z.mag(P.Body.vx(b))
  az = P.Z.mag(P.Body.vz(b))
  bx = P.Z.mag(P.Body.vx(b2))
  bz = P.Z.mag(P.Body.vz(b2))
  {Nat.add(Nat.mul(ax, ax), Nat.mul(az, az))
    == Nat.add(Nat.add(Nat.mul(bx, bx), Nat.mul(bz, bz)),
               Nat.add(Nat.mul(Nat.sub(ax, bx), Nat.add(ax, bx)), Nat.mul(Nat.sub(az, bz), Nat.add(az, bz)))) : Nat}
  & {Nat.add(P.Body.x(b2), Nat.add(P.Z.neg(P.Body.vx(b)), P.Z.neg(P.Body.vx(b2))))
    == Nat.add(P.Body.x(b), Nat.add(P.Z.pos(P.Body.vx(b)), P.Z.pos(P.Body.vx(b2)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.add(P.Z.neg(P.Body.vz(b)), P.Z.neg(P.Body.vz(b2))))
    == Nat.add(P.Body.z(b), Nat.add(P.Z.pos(P.Body.vz(b)), P.Z.pos(P.Body.vz(b2)))) : Nat}
  & {P.Body.y(b2) == P.Body.y(b) : Nat}

# LAW: static friction: a body at rest and held up, with no input and no
# knock, stays exactly where it is -- the same place, the same nothing of
# a velocity, still held. Only the way it is turned may change: what
# holds a cube presses up on it, and where that press lands is what turns
# it (Rot.held). A cube the press tips over is knocked, which is what the
# no-knock hypothesis leaves out -- a cube that topples is not at rest.
law rest_stays:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +rt: P.Rot
  for +on: {P.Geo.held(P.Quat.flat(P.Rot.q(rt)), P.K.size(k), x, y, z, P.Rot.q(rt), obs) == True{} : Bool}
  for +clear: {P.Geo.free(P.K.size(k), x, y, z, P.Rot.q(rt), obs) == True{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, P.In.idle(),
    P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))) == False{} : Bool}
  {P.Body.tick(k, obs, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
    == (P.Body.setrot(P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt},
         P.Body.rot(P.Tick.body(P.Body.tick(k, obs, P.In.idle(),
           P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})))), obs) : P.Body & List<&2, P.Body>}

# Collisions and energy
# ---------------------

# LAW: a push keeps momentum: two bodies meeting along an axis leave with
# velocities adding up to what they came with (equal masses).
law push_momentum:
  for a: P.Z
  for b: P.Z
  s = P.Share.go(a, b)
  {Nat.add(Nat.add(P.Z.pos(P.Share.fst(s)), P.Z.pos(P.Share.snd(s))), Nat.add(P.Z.neg(a), P.Z.neg(b)))
    == Nat.add(Nat.add(P.Z.pos(a), P.Z.pos(b)), Nat.add(P.Z.neg(P.Share.fst(s)), P.Z.neg(P.Share.snd(s)))) : Nat}

# LAW: a push never makes energy: the kinetic energy after is at most the
# kinetic energy before (the rest goes to the collision).
law push_energy:
  for a: P.Z
  for b: P.Z
  s = P.Share.go(a, b)
  {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(s)), P.Z.sq(P.Share.snd(s))), Nat.add(P.Z.sq(a), P.Z.sq(b))) == True{} : Bool}

# LAW: energy never grows by itself: with no input, a tick leaves the body
# and everything it touched with at most the mechanical energy they had.
# Flight keeps it, friction, landings and pushes spend it; only the
# player's motor and jump add any.
# the same words with a name on them, so that the proof can hand the law
# back as it stands instead of having the whole tick worked out twice
def EnergyAfter(+k: P.K, +obs: List<&2, P.Body>, +b: P.Body) -> Type:
  r = P.Body.tick(k, obs, P.In.idle(), b)
  {Nat.is_le(Nat.add(P.Body.energy(P.K.g(k), P.Tick.body(r)), P.Body.energies(P.K.g(k), P.Tick.obs(r))),
             Nat.add(P.Body.energy(P.K.g(k), b), P.Body.energies(P.K.g(k), obs))) == True{} : Bool}

law energy_never_grows:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +b: P.Body
  EnergyAfter(k, obs, b)

# LAW: no clipping: a body clear of its obstacles is still clear of them
# after a tick, whatever the input -- nothing walks, falls or is pushed
# into another cube. With turning in, the law asks for more than it used
# to: the body has to be clear where it ends up AND turned the way it
# ends up turned, so a cube can no more turn into a neighbour than walk
# into one.
# LAW: a turn is the spin taken up. A tick that ends with no knock leaves
# the body turned by exactly the turn its spin asks for: the orientation
# after the tick is the one before -- as the tick's linear part left it --
# turned by `Rot.turn`, which is the spin's angle about the spin's axis.
# Without this the four laws above would hold of a cube that never turns
# at all: they pin the spin it carries, this one makes the body follow it.
law spin_turns_the_body:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +inp: P.In
  for +b: P.Body
  for +spin: {P.Wv.null(P.Rot.w(P.Body.rot(P.Tick.body(P.Body.step(k, obs, inp, b))))) == False{} : Bool}
  for +free: {P.Body.hit(P.Tick.body(P.Body.tick(k, obs, inp, b))) == False{} : Bool}
  {P.Rot.q(P.Body.rot(P.Tick.body(P.Body.tick(k, obs, inp, b))))
    == P.Rot.turn(P.Rot.q(P.Body.rot(P.Tick.body(P.Body.step(k, obs, inp, b)))),
                  P.Rot.w(P.Body.rot(P.Tick.body(P.Body.step(k, obs, inp, b))))) : P.Quat}

# LAW: it falls or it stands. A body in the air, with no input and with
# gravity on, ends the tick either still going down or standing on
# something -- never stopped in mid-air. Without this a tick may refuse a fall it cannot take and
# leave the body hanging: its fall's speed wiped, nothing under it, and
# its sideways speed untouched, because friction only reaches a body that
# is standing. That is a cube that floats and slides away for ever, and
# no other law here forbids it.
law it_falls_or_it_stands:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +obs: List<&2, P.Body>
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +vx: P.Z
  for +vz: P.Z
  for +q: Nat
  for +going: {Nat.is_lt(0n, q) == True{} : Bool}
  for +h: Bool
  for +rt: P.Rot
  a = P.Tick.body(P.Body.tick(k, obs, P.In.idle(),
    P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, h, rt}))
  {Bool.or(Nat.is_lt(0n, P.Z.neg(P.Body.vy(a))), P.Body.ground(a)) == True{} : Bool}

# LAW: nothing goes into the floor. The floor of the world is at 0, and
# a turned cube reaches below its own corner by Geo.sag, so its lowest
# point is y - sag. A body whose lowest point starts at or above the
# floor ends every tick there too -- whatever the input, whatever the
# obstacles, however it fell, landed, was pushed or turned.
law never_under_the_floor:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +inp: P.In
  for +b: P.Body
  for +above: {Nat.is_le(P.Geo.sag(P.K.size(k), P.Rot.q(P.Body.rot(b))), P.Body.y(b)) == True{} : Bool}
  a = P.Tick.body(P.Body.tick(k, obs, inp, b))
  {Nat.is_le(P.Geo.sag(P.K.size(k), P.Rot.q(P.Body.rot(a))), P.Body.y(a)) == True{} : Bool}

# LAW: nothing floats. A body that ends a tick standing is really held
# up: it cannot go any lower -- one unit past the hair a turned cube
# keeps under it (Geo.gap), it would be in the floor or in a cube.
# Standing is what switches gravity off for a body (Move.stay), so a
# stand that nothing holds is a cube hanging in the air, and that is
# what this law forbids -- for any body, input and obstacles.
law standing_is_held:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +inp: P.In
  for +b: P.Body
  for +stands: {P.Body.ground(P.Tick.body(P.Body.tick(k, obs, inp, b))) == True{} : Bool}
  r = P.Body.tick(k, obs, inp, b)
  {P.Tick.sinks(P.K.size(k), P.Tick.obs(r), P.Body.x(P.Tick.body(r)), P.Body.y(P.Tick.body(r)),
    P.Body.z(P.Tick.body(r)), P.Rot.q(P.Body.rot(P.Tick.body(r)))) == False{} : Bool}

# LAW: past the edge, it tips. A cube at rest, standing on one cube (the
# cube's top no higher than its middle, their columns overlapping, and
# nothing lower for it to go to) and not on the floor, whose middle is
# past that cube's edge -- the whole
# of what holds it on one side of its middle -- comes out of the tick's
# forces turning towards the overhang. Its weight pulls down through the
# middle; the only thing pushing back is the cube under it, off to one
# side; that pair is a torque, and nothing in the tick cancels it. It
# holds however the cube is turned: square with the world or standing on
# a corner. Right-hand rule: tipping towards +x is a turn about -z,
# towards +z a turn about +x. One law for each of the four sides.
law past_the_edge_it_tips_px:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +rt: P.Rot
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, P.Rot.q(rt)) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(P.Body.x(o), P.K.size(k)), Nat.add(x, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  a = P.Tick.body(P.Body.step(k, [o], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))
  {P.Z.above(P.Wv.z(P.Rot.w(rt)), P.Wv.z(P.Rot.w(P.Body.rot(a)))) == True{} : Bool}

law past_the_edge_it_tips_nx:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +rt: P.Rot
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, P.Rot.q(rt)) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(x, Nat.div(P.K.size(k), 2n)), P.Body.x(o)) == True{} : Bool}
  a = P.Tick.body(P.Body.step(k, [o], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))
  {P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(a))), P.Wv.z(P.Rot.w(rt))) == True{} : Bool}

law past_the_edge_it_tips_pz:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +rt: P.Rot
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, P.Rot.q(rt)) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(P.Body.z(o), P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  a = P.Tick.body(P.Body.step(k, [o], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))
  {P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(a))), P.Wv.x(P.Rot.w(rt))) == True{} : Bool}

law past_the_edge_it_tips_nz:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +rt: P.Rot
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, P.Rot.q(rt)) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(z, Nat.div(P.K.size(k), 2n)), P.Body.z(o)) == True{} : Bool}
  a = P.Tick.body(P.Body.step(k, [o], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))
  {P.Z.above(P.Wv.x(P.Rot.w(rt)), P.Wv.x(P.Rot.w(P.Body.rot(a)))) == True{} : Bool}

# LAW: the turning a hold gives is never thrown away. A cube at rest --
# going nowhere, turning not at all -- standing on one cube, off the
# floor, with its middle past that cube's edge, ends the tick either
# turned (its orientation is not the one it had) or still turning
# towards the overhang. The laws above only ask that the hold give it
# that turning; a tick that gave it and then threw it away, leaving the
# cube exactly as it was, balanced on an edge that nothing can hold it
# on, would keep them all. That is what this law forbids. One law for
# each of the four sides; tipping towards +x is a turn about -z, towards
# +z a turn about +x.
law tipping_is_never_thrown_away_px:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +q: P.Quat
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, q) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, q) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(P.Body.x(o), P.K.size(k)), Nat.add(x, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  a = P.Tick.body(P.Body.tick(k, [o], P.In.idle(),
    P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}))
  {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(a)), q)), P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(P.Body.rot(a))))) == True{} : Bool}

law tipping_is_never_thrown_away_nx:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +q: P.Quat
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, q) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, q) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(x, Nat.div(P.K.size(k), 2n)), P.Body.x(o)) == True{} : Bool}
  a = P.Tick.body(P.Body.tick(k, [o], P.In.idle(),
    P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}))
  {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(a)), q)), P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(a))), P.Pos{0n})) == True{} : Bool}

law tipping_is_never_thrown_away_pz:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +q: P.Quat
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, q) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, q) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(P.Body.z(o), P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  a = P.Tick.body(P.Body.tick(k, [o], P.In.idle(),
    P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}))
  {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(a)), q)), P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(a))), P.Pos{0n})) == True{} : Bool}

law tipping_is_never_thrown_away_nz:
  for +k: P.K
  for +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool}
  for +o: P.Body
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +h: Bool
  for +q: P.Quat
  for +held: {P.Tick.sinks(P.K.size(k), [o], x, y, z, q) == False{} : Bool}
  for +off: {P.Geo.onfloor(P.K.size(k), y, q) == False{} : Bool}
  for +under: {Nat.is_le(P.Geo.top(P.K.size(k), P.Body.y(o), P.Body.rot(o)), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool}
  for +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, P.Body.x(o))) == True{} : Bool}
  for +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, P.Body.z(o))) == True{} : Bool}
  for +past: {Nat.is_lt(Nat.add(z, Nat.div(P.K.size(k), 2n)), P.Body.z(o)) == True{} : Bool}
  a = P.Tick.body(P.Body.tick(k, [o], P.In.idle(),
    P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}))
  {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(a)), q)), P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(P.Body.rot(a))))) == True{} : Bool}

# LAW: a push is a touch. A move along x that hands its velocity to an
# obstacle has to have reached it: if the mover, where the move leaves
# it, could still go one unit on the way it was going, nothing was in
# its way, and every obstacle comes out of the move exactly as it went
# in. Without this a cube is shoved from across the room by one that
# never got to it. The same along z.
law a_push_is_a_touch_x:
  for +s: Nat
  for +obs: List<&2, P.Body>
  for +v0: P.Z
  for +b: P.Body
  for +room: {P.Geo.free(s, P.Z.shift(P.Body.x(P.Tick.body(P.Move.x(s, obs, v0, b))), P.Z.like(P.Z.add(v0, P.Body.vx(b)), 1n)),
    P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool}
  {P.Tick.obs(P.Move.x(s, obs, v0, b)) == obs : List<&2, P.Body>}

law a_push_is_a_touch_z:
  for +s: Nat
  for +obs: List<&2, P.Body>
  for +v0: P.Z
  for +b: P.Body
  for +room: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Z.shift(P.Body.z(P.Tick.body(P.Move.z(s, obs, v0, b))), P.Z.like(P.Z.add(v0, P.Body.vz(b)), 1n)),
    P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool}
  {P.Tick.obs(P.Move.z(s, obs, v0, b)) == obs : List<&2, P.Body>}

law no_clip:
  for +k: P.K
  for +obs: List<&2, P.Body>
  for +inp: P.In
  for +b: P.Body
  for clear: {P.Geo.free(P.K.size(k), P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs)
    == True{} : Bool}
  r = P.Body.tick(k, obs, inp, b)
  {P.Geo.free(P.K.size(k), P.Body.x(P.Tick.body(r)), P.Body.y(P.Tick.body(r)), P.Body.z(P.Tick.body(r)),
    P.Rot.q(P.Body.rot(P.Tick.body(r))), P.Tick.obs(r)) == True{} : Bool}


# Turning
# -------

# LAW: a cube in flight turns for ever at the same rate. A cube resists
# turning the same about every axis, so there is no wobble to change its
# angular velocity, and the angle it has turned grows by exactly that rate
# every tick -- whatever the rate and whatever the angle.
law free_spin_keeps_the_turning:
  for +r: P.Rot
  s1 = P.Rot.free(r)
  {P.Wv.x(P.Rot.w(s1)) == P.Wv.x(P.Rot.w(r)) : P.Z}
  & {P.Wv.y(P.Rot.w(s1)) == P.Wv.y(P.Rot.w(r)) : P.Z}
  & {P.Wv.z(P.Rot.w(s1)) == P.Wv.z(P.Rot.w(r)) : P.Z}

# LAW: a hit puts the whole of its turning into the body -- all three
# parts of the arm crossed with the impulse, not just the part that lies
# along some axis the body was already turning on. A cube hit on a corner
# comes off turning about the axis that hit asks for.
law a_hit_adds_the_whole_turning:
  for +r: P.Rot
  for +rx: P.Z
  for +ry: P.Z
  for +rz: P.Z
  for +jx: P.Z
  for +jy: P.Z
  for +jz: P.Z
  s1 = P.Rot.w(P.Rot.hit(r, rx, ry, rz, jx, jy, jz))
  k = P.Rot.kick(rx, ry, rz, jx, jy, jz)
  {P.Wv.x(s1) == P.Z.add(P.Wv.x(P.Rot.w(r)), P.Wv.x(k)) : P.Z}
  & {P.Wv.y(s1) == P.Z.add(P.Wv.y(P.Rot.w(r)), P.Wv.y(k)) : P.Z}
  & {P.Wv.z(s1) == P.Z.add(P.Wv.z(P.Rot.w(r)), P.Wv.z(k)) : P.Z}

# LAW: a hit dead centre does not turn anything. What turns a body is the
# arm -- how far from its middle it was hit -- crossed with the impulse,
# so an arm of zero gives nothing to cross with, however hard the hit.
law no_spin_from_the_middle:
  for +jx: P.Z
  for +jy: P.Z
  for +jz: P.Z
  {P.Z.mag(P.Rot.crx(P.Pos{0n}, P.Pos{0n}, jy, jz)) == 0n : Nat}
  & {P.Z.mag(P.Rot.cry(P.Pos{0n}, P.Pos{0n}, jz, jx)) == 0n : Nat}
  & {P.Z.mag(P.Rot.crz(P.Pos{0n}, P.Pos{0n}, jx, jy)) == 0n : Nat}

# LAW: a hit only turns a body about the axes across it. The turning about
# x comes from the arm and the impulse in y and z; a hit whose arm and
# push both point along x turns nothing about y or z either.
law spin_is_across_the_push:
  for +rx: P.Z
  for +jx: P.Z
  {P.Z.mag(P.Rot.crx(P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, P.Pos{0n})) == 0n : Nat}
  & {P.Z.mag(P.Rot.cry(P.Pos{0n}, rx, P.Pos{0n}, jx)) == 0n : Nat}
