"""Symbolic checks for the Lie--Poisson Jacobi note (sympy).
All fields are on T^3 = R^3/(2 pi Z)^3; integrals are over [0,2pi]^3.
Bracket convention used throughout: [v,w] := (w.grad)v - (v.grad)w.
"""
import sympy as sp
from itertools import product

x, y, z = X = sp.symbols('x y z', real=True)

def grad(f): return sp.Matrix([sp.diff(f, s) for s in X])
def div(v): return sum(sp.diff(v[i], X[i]) for i in range(3))
def curl(v):
    return sp.Matrix([sp.diff(v[2], y) - sp.diff(v[1], z),
                      sp.diff(v[0], z) - sp.diff(v[2], x),
                      sp.diff(v[1], x) - sp.diff(v[0], y)])
def adv(a, v):  # (a.grad) v
    return sp.Matrix([sum(a[j]*sp.diff(v[i], X[j]) for j in range(3)) for i in range(3)])
def br(v, w):   # [v,w] = (w.grad)v - (v.grad)w
    return adv(w, v) - adv(v, w)
def cross(a, b): return a.cross(b)
def dot(a, b): return (a.T*b)[0]
def integ(f):
    return sp.simplify(sp.integrate(sp.expand(f), (x, 0, 2*sp.pi), (y, 0, 2*sp.pi), (z, 0, 2*sp.pi)))

def genfield(name):
    return sp.Matrix([sp.Function(f'{name}{i}')(x, y, z) for i in (1, 2, 3)])

ok = True
def report(label, expr):
    global ok
    e = sp.simplify(sp.expand(expr))
    zero = (e == sp.zeros(*e.shape)) if hasattr(e, 'shape') else (e == 0)
    ok &= bool(zero)
    print(f"[{'PASS' if zero else 'FAIL'}] {label}")

a, b = genfield('a'), genfield('b')
# (1) curl(a x b) = a div b - b div a + (b.grad)a - (a.grad)b, generic fields
report("curl(a x b) = a div b - b div a + (b.grad)a - (a.grad)b  (generic smooth a,b)",
       curl(cross(a, b)) - (a*div(b) - b*div(a) + adv(b, a) - adv(a, b)))

# (2) for div-free v = curl A, w = curl B: [v,w] = curl(v x w) and div [v,w] = 0
A, B = genfield('A'), genfield('B')
v, w = curl(A), curl(B)
report("div(curl A) = 0", div(v))
report("[v,w] = curl(v x w) for v=curl A, w=curl B (div-free)", br(v, w) - curl(cross(v, w)))
report("closure: div [v,w] = 0 for div-free v,w", div(br(v, w)))
# without div-free, [v,w] != curl(v x w): exhibit
v0 = sp.Matrix([sp.sin(x), 0, 0]); w0 = sp.Matrix([0, sp.cos(x), 0])
print("   non-div-free example v=(sin x,0,0), w=(0,cos x,0): [v,w]-curl(v x w) =",
      list(sp.simplify(br(v0, w0) - curl(cross(v0, w0)))))

# (3) Jacobi identity for the bracket, generic (not even div-free) fields
u, v1, w1 = genfield('u'), genfield('v'), genfield('w')
report("vector-field Jacobi [u,[v,w]]+[v,[w,u]]+[w,[u,v]] = 0 (generic fields)",
       br(u, br(v1, w1)) + br(v1, br(w1, u)) + br(w1, br(u, v1)))

# (4) m.curl(v x w) - curl(m).(v x w) = div((v x w) x m)  (pointwise, generic)
m = genfield('m')
report("m.curl(c) - curl(m).c = div(c x m), c = v x w (generic)",
       dot(m, curl(cross(v1, w1))) - dot(curl(m), cross(v1, w1)) - div(cross(cross(v1, w1), m)))

# (5) concrete trigonometric fields on T^3: correct identity vs the draft's step
# each field is a sum of modes (c cos(k.x) + d sin(k.x)) with integer c,d perpendicular to k  => div-free
K = [(1,0,0),(0,1,0),(1,1,0),(0,1,1),(1,0,1),(1,1,1),(1,-1,0)]
def perp(k, s):
    # two integer vectors perpendicular to k, picked deterministically by seed s
    kk = sp.Matrix(k); cands = [sp.Matrix(c) for c in product((-1,0,1,2), repeat=3)
                               if sp.Matrix(c).dot(kk) == 0 and any(c)]
    return cands[s % len(cands)], cands[(3*s+1) % len(cands)]
def trig_field(modes):
    f = sp.zeros(3,1)
    for k, s in modes:
        ph = k[0]*x + k[1]*y + k[2]*z
        c, d = perp(k, s)
        f += c*sp.cos(ph) + d*sp.sin(ph)
    return f
mT = trig_field([(K[0],1),(K[1],2),(K[2],3),(K[3],4)])
vF = trig_field([(K[1],5),(K[4],6),(K[5],7)])
vG = trig_field([(K[0],8),(K[3],9),(K[6],10),(K[5],11)])
for name, f in (("m", mT), ("vF", vF), ("vG", vG)):
    assert sp.simplify(div(f)) == 0, name
om = curl(mT)
lhs_correct = integ(dot(mT, br(vF, vG)))
rhs_correct = integ(dot(om, cross(vF, vG)))
print(f"   <m,[vF,vG]> = {lhs_correct},   int omega.(vF x vG) = {rhs_correct}")
report("correct identity <m,[vF,vG]> = int curl(m).(vF x vG) on concrete trig fields",
       lhs_correct - rhs_correct)
draft_lhs = integ(dot(om, adv(vG, vF)))   # int omega.((vG.grad)vF)
draft_rhs = integ(dot(om, cross(vF, vG)))
print(f"   draft step: int omega.((vG.grad)vF) = {draft_lhs}  vs  int omega.(vF x vG) = {draft_rhs}")
alt = integ(dot(mT, adv(vG, vF)))
print(f"   (also: int m.((vG.grad)vF) alone = {alt}; the second transport term is needed)")
if sp.simplify(draft_lhs - draft_rhs) != 0:
    print("[PASS] counterexample: the draft's integration-by-parts step is false on these fields")
else:
    ok = False; print("[FAIL] no counterexample found")

# (6) coadjoint representative: <m,[v,w]> = int (w x omega).v
report("<m,[vF,vG]> = int (vG x omega).vF  (K_w m = P(w x omega))",
       lhs_correct - integ(dot(cross(vG, om), vF)))

# (7) sign check: with + sign, F=<m,a>, H=1/2|m|^2 gives Euler d/dt<u,a> = -<(u.grad)u,a>
aT = trig_field([(K[2],12),(K[4],13),(K[0],14),(K[1],15)])
assert sp.simplify(div(aT)) == 0
bracket_plus = integ(dot(mT, br(aT, mT)))
euler_rhs = -integ(dot(adv(mT, mT), aT))
print(f"   {{F,H}}_+ = {bracket_plus},  -<(u.grad)u,a> = {euler_rhs}")
report("+ sign reproduces Euler: {<.,a>, 1/2|.|^2}_+ (u) = -<(u.grad)u, a>", bracket_plus - euler_rhs)

# (8) finite-dimensional Lie--Poisson Jacobi, arbitrary smooth F,G,H
def lp_jacobi(struct, n, label):
    xs = sp.symbols(f'p1:{n+1}')
    F, G, H = [sp.Function(s)(*xs) for s in 'FGH']
    def pb(P, Q):  # {P,Q}(p) = sum_k p_k c^k_{ij} dP/dp_i dQ/dp_j
        return sum(xs[k]*c*sp.diff(P, xs[i])*sp.diff(Q, xs[j]) for (i, j, k), c in struct.items())
    J = sp.expand(pb(F, pb(G, H)) + pb(G, pb(H, F)) + pb(H, pb(F, G)))
    report(f"finite-dim Lie-Poisson Jacobi on {label}* for arbitrary smooth F,G,H", J)
    # show the second-derivative terms of a single term are nonzero
    single = sp.expand(pb(F, pb(G, H)))
    second = [t for t in single.as_ordered_terms() if any(isinstance(d, sp.Derivative) and d.derivative_count == 2 for d in t.atoms(sp.Derivative))]
    print(f"   {label}: {{F,{{G,H}}}} alone has {len(second)} terms containing second derivatives (nonzero individually)")

so3 = {}
for (i, j, k) in product(range(3), repeat=3):
    e = sp.LeviCivita(i, j, k)
    if e != 0: so3[(i, j, k)] = e
lp_jacobi(so3, 3, "so(3)")
# sl(2,R): basis h,e,f with [h,e]=2e,[h,f]=-2f,[e,f]=h ; index 0=h,1=e,2=f
sl2 = {(0, 1, 1): 2, (1, 0, 1): -2, (0, 2, 2): -2, (2, 0, 2): 2, (1, 2, 0): 1, (2, 1, 0): -1}
lp_jacobi(sl2, 3, "sl(2,R)")

print("ALL PASS" if ok else "SOME CHECK FAILED")
