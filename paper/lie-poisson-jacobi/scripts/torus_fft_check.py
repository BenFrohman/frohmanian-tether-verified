"""Floating-point check of the derived formula for delta{G,H}/delta m and of the
Jacobi identity for the Lie--Poisson bracket on sdiff(T^3)^*, T^3 = R^3/(2 pi Z)^3.

No Galerkin truncation of the bracket is used: every field below is an exact
trigonometric polynomial, every product is evaluated pointwise, and the grid
(N = 48 points per direction) is large enough that spectral differentiation,
Leray projection and grid quadrature are EXACT for all trigonometric polynomials
that occur (max degree <= 16 < N/2 for derivatives/projection; integrands of
degree <= 30 < N for quadrature).  The only error is IEEE roundoff (and, in
test (a), the finite-difference error of the epsilon-derivative).
This is a numerical sanity check, not a proof.
"""
import numpy as np
rng = np.random.default_rng(20261109)
N = 48
L = 2*np.pi
xs = np.arange(N)*L/N
Xg = np.array(np.meshgrid(xs, xs, xs, indexing='ij'))
k1 = np.fft.fftfreq(N, d=1.0/N)
KK = np.array(np.meshgrid(k1, k1, k1, indexing='ij'))
K2 = (KK**2).sum(0); K2s = np.where(K2 == 0, 1, K2)
VOL = L**3

def pair(a, b):            # <a,b> = int_{T^3} a.b dx  (exact grid quadrature)
    return VOL*np.mean((a*b).sum(0))
def d(f, j):               # exact spectral derivative of a trig polynomial
    return np.real(np.fft.ifftn(1j*KK[j]*np.fft.fftn(f)))
def adv(a, v):             # (a.grad) v
    return np.array([sum(a[j]*d(v[i], j) for j in range(3)) for i in range(3)])
def br(v, w):              # [v,w] = (w.grad)v - (v.grad)w
    return adv(w, v) - adv(v, w)
def curl(v):
    return np.array([d(v[2],1)-d(v[1],2), d(v[0],2)-d(v[2],0), d(v[1],0)-d(v[0],1)])
def div(v): return sum(d(v[j], j) for j in range(3))
def leray(v):              # P = I - grad Delta^{-1} div ; k=0 mode (constants) kept
    vh = np.array([np.fft.fftn(c) for c in v])
    kv = (KK*vh).sum(0)/K2s
    return np.array([np.real(np.fft.ifftn(vh[i] - KK[i]*kv)) for i in range(3)])
def cross(a, b): return np.cross(a, b, axis=0)
def Kop(w, m):             # coadjoint representative: <Kop(w,m), v> = <m,[v,w]>
    return leray(cross(w, curl(m)))

def rand_field(deg=2, const=True):
    """random real divergence-free trig polynomial with |k_i| <= deg (incl. constant mode)"""
    vh = np.zeros((3, N, N, N), complex)
    mask = (np.abs(KK) <= deg).all(0)
    vh[:, mask] = rng.normal(size=(3, mask.sum())) + 1j*rng.normal(size=(3, mask.sum()))
    if not const: vh[:, 0, 0, 0] = 0
    v = np.array([np.real(np.fft.ifftn(c)) for c in vh])*N**3/50
    return leray(v)

# ---- admissible functionals: value, delta (in g), Hessian action (in g) ----
class Cylindrical:
    """F(m) = Phi(<m,a_1>,<m,a_2>,<m,a_3>), Phi nonlinear, a_i in g."""
    def __init__(self, a, Phi, dPhi, d2Phi): self.a, self.Phi, self.dPhi, self.d2Phi = a, Phi, dPhi, d2Phi
    def y(self, m): return np.array([pair(m, ai) for ai in self.a])
    def val(self, m): return self.Phi(self.y(m))
    def delta(self, m): g = self.dPhi(self.y(m)); return sum(g[i]*self.a[i] for i in range(3))
    def hess(self, m, b):
        Hm = self.d2Phi(self.y(m)); yb = np.array([pair(b, ai) for ai in self.a])
        c = Hm @ yb; return sum(c[i]*self.a[i] for i in range(3))
class LocalCubic:
    """F(m) = int m1 m2 m3 dx ; delta = P(m2m3, m1m3, m1m2); Hess b = P(D^2psi(m) b)."""
    def val(self, m): return VOL*np.mean(m[0]*m[1]*m[2])
    def delta(self, m): return leray(np.array([m[1]*m[2], m[0]*m[2], m[0]*m[1]]))
    def hess(self, m, b):
        return leray(np.array([m[2]*b[1]+m[1]*b[2], m[2]*b[0]+m[0]*b[2], m[1]*b[0]+m[0]*b[1]]))
class Energy:
    def val(self, m): return 0.5*pair(m, m)
    def delta(self, m): return m.copy()
    def hess(self, m, b): return b.copy()

def PB(F, G, m):  # {F,G}_+(m) = <m,[dF,dG]>
    return pair(m, br(F.delta(m), G.delta(m)))
def delta_PB(G, H, m, hot=True):
    """derived formula: delta{G,H} = [g,h] + Hess_G(K_h m) - Hess_H(K_g m)"""
    g, h = G.delta(m), H.delta(m)
    out = br(g, h)
    if hot: out = out + G.hess(m, Kop(h, m)) - H.hess(m, Kop(g, m))
    return out
def PB_outer(F, G, H, m, hot=True):  # {F,{G,H}}(m) = <m,[dF, delta{G,H}]>
    return pair(m, br(F.delta(m), delta_PB(G, H, m, hot)))

# functionals
aF = [rand_field() for _ in range(3)]; aH = [rand_field() for _ in range(3)]
F = Cylindrical(aF, lambda y: y[0]*y[1]**2 + np.sin(y[2]) + y[0]*y[2],
                lambda y: np.array([y[1]**2 + y[2], 2*y[0]*y[1], np.cos(y[2]) + y[0]]),
                lambda y: np.array([[0, 2*y[1], 1], [2*y[1], 2*y[0], 0], [1, 0, -np.sin(y[2])]]))
G = LocalCubic()
H = Cylindrical(aH, lambda y: np.exp(0.1*y[0])*y[1] + y[2]**3,
                lambda y: np.array([0.1*np.exp(0.1*y[0])*y[1], np.exp(0.1*y[0]), 3*y[2]**2]),
                lambda y: np.array([[0.01*np.exp(0.1*y[0])*y[1], 0.1*np.exp(0.1*y[0]), 0],
                                    [0.1*np.exp(0.1*y[0]), 0, 0], [0, 0, 6*y[2]]]))
E = Energy()
m = rand_field()
print(f"N={N}; max |div m| = {np.abs(div(m)).max():.2e}; mean of m = {np.round(m.mean((1,2,3)),4)}")

# (0) checks of the ingredients
v, w = rand_field(), rand_field()
print("(0a) |<m,[v,w]> - <Kop(w,m),v>|          =", abs(pair(m, br(v, w)) - pair(Kop(w, m), v)))
print("(0b) |<m,[v,w]> - int curl m.(v x w)|     =", abs(pair(m, br(v, w)) - pair(curl(m), cross(v, w))))
print("(0c) max|div [v,w]|                        =", np.abs(div(br(v, w))).max())
u = rand_field()
J = br(u, br(v, w)) + br(v, br(w, u)) + br(w, br(u, v))
print("(0d) max|vector-field Jacobi|              =", np.abs(J).max(), " (scale", np.abs(br(u, br(v, w))).max(), ")")
for name, Q in (("F", F), ("G", G), ("H", H)):
    a, b = rand_field(), rand_field()
    print(f"(0e) Hessian symmetry {name}: |<a,Hb>-<b,Ha>| =", abs(pair(a, Q.hess(m, b)) - pair(b, Q.hess(m, a))))

# (a) derivative of {G,H} along a vs <a, delta{G,H}> from the derived formula
def ddeps(fun, m, a, h=1e-3):
    # 6th-order central difference
    c = [(1, -3/4), (2, 3/20), (3, -1/60)]
    return sum(-wt*(fun(m + s*h*a) - fun(m - s*h*a)) for s, wt in c)/h
for (A, B, lab) in ((G, H, "G,H"), (F, G, "F,G"), (H, E, "H,E")):
    a = rand_field()
    fd = ddeps(lambda mm: PB(A, B, mm), m, a)
    full = pair(a, delta_PB(A, B, m, True)); naive = pair(a, delta_PB(A, B, m, False))
    print(f"(a) {{{lab}}}: FD derivative={fd:.10e}  <a,formula>={full:.10e}  rel.err={abs(fd-full)/abs(fd):.1e}"
          f"   | naive <a,[dA,dB]> only = {naive:.6e} (rel.err {abs(fd-naive)/abs(fd):.1e})")

# (b) Jacobi identity
for trip, lab in (((F, G, H), "F,G,H"), ((F, G, E), "F,G,E"), ((G, H, E), "G,H,E")):
    A, B, C = trip
    t = [PB_outer(A, B, C, m), PB_outer(B, C, A, m), PB_outer(C, A, B, m)]
    tn = [PB_outer(A, B, C, m, False), PB_outer(B, C, A, m, False), PB_outer(C, A, B, m, False)]
    print(f"(b) {lab}: terms = {[f'{s:.6e}' for s in t]}  cyclic sum = {sum(t):.3e}  (rel {abs(sum(t))/max(map(abs,t)):.1e})")
    print(f"    per-term effect of the second-derivative terms (full - naive): {[f'{p_-q_:.6e}' for p_, q_ in zip(t, tn)]}")
    print(f"    naive terms (second-derivative terms dropped): {[f'{q_:.6e}' for q_ in tn]}, their cyclic sum = {sum(tn):.1e}")
    print("    -> each individual {A,{B,C}} changes by an O(1) amount; only the cyclic sum of the six omitted terms vanishes")
    # the six Q-terms individually and their pairwise cancellation
    fA, fB, fC = A.delta(m), B.delta(m), C.delta(m)
    kA, kB, kC = Kop(fA, m), Kop(fB, m), Kop(fC, m)
    Q = lambda Fn, p, q: pair(p, Fn.hess(m, q))
    six = {"-Q_B(kA,kC)": -Q(B, kA, kC), "+Q_B(kC,kA)": Q(B, kC, kA),
           "+Q_C(kA,kB)": Q(C, kA, kB), "-Q_C(kB,kA)": -Q(C, kB, kA),
           "+Q_A(kB,kC)": Q(A, kB, kC), "-Q_A(kC,kB)": -Q(A, kC, kB)}
    print("    six second-derivative terms:", {k: f"{v_:.6e}" for k, v_ in six.items()})
    print(f"    pair sums: B:{six['-Q_B(kA,kC)']+six['+Q_B(kC,kA)']:.1e}  C:{six['+Q_C(kA,kB)']+six['-Q_C(kB,kA)']:.1e}  A:{six['+Q_A(kB,kC)']+six['-Q_A(kC,kB)']:.1e}")
    jac = pair(m, br(fA, br(fB, fC)) + br(fB, br(fC, fA)) + br(fC, br(fA, fB)))
    print(f"    <m, [a,[b,c]]+cyc> = {jac:.1e}")
