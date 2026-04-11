#!/usr/bin/env python3
"""N5 — Guinand-Weil explicit formula self-consistency.
Requires mpmath. Threshold: residual < 5%."""
import json, sys
try:
    import mpmath
    mpmath.mp.dps = 25
except ImportError:
    print("  [SKIP] mpmath not installed"); sys.exit(0)
from math import log, sqrt, pi, exp

PASS = True
def check(name, cond):
    global PASS
    if not cond: PASS = False
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

W = 2.0
def h(r): return W**2/(r**2+W**2)
def g(u): return W/2*exp(-W*abs(u))

# Zero side (nontrivial + trivial)
Z_nt = sum(2*h(float(mpmath.im(mpmath.zetazero(n)))) for n in range(1,201))
Z_triv = sum(W**2/(W**2-(2*n+0.5)**2) for n in range(1,501))
Z_all = Z_nt + Z_triv

# Archimedean side
g0_term = W/2 * log(1/pi)
def integ(t):
    t=float(t); z=mpmath.mpc(0.25,t/2)
    return h(t)*float(mpmath.re(mpmath.digamma(z)+mpmath.digamma(mpmath.conj(z))))
I = float(mpmath.quad(integ, [0,500]))
A = g0_term + I/pi

# Prime side
X = 500000
sieve = bytearray(X+1); sieve[0]=sieve[1]=1
for i in range(2,int(X**0.5)+1):
    if not sieve[i]:
        for j in range(i*i,X+1,i): sieve[j]=1
P = 0.0
for p in range(2,X+1):
    if not sieve[p]:
        logp=log(p); pk=p
        while pk<=X:
            P+=logp/sqrt(pk)*g(log(pk)); pk*=p
P *= 2

RHS = A - P
E = Z_all - RHS
rel = abs(E)/max(abs(Z_all),abs(RHS),1)

check(f"Z_all = {Z_all:.6f}", True)
check(f"A - Π = {RHS:.6f}", True)
check(f"Résidu E = {E:.6f}", True)
check(f"Résidu relatif = {rel:.4f} < 0.05 (5%)", rel < 0.05)
check(f"Résidu relatif = {rel:.4f} < 0.02 (2%)", rel < 0.02)

# Euler tail
P235=0.0
for p in [2,3,5]:
    logp=log(p); pk=p
    while pk<=X: P235+=logp/sqrt(pk)*g(log(pk)); pk*=p
P235*=2
tail_pct = 100*(1-P235/(P)) if P>0 else 0
check(f"Euler tail (p≥7) = {tail_pct:.1f}% > 10%", tail_pct > 10)

result = {"test":"N5_guinand_weil","pass":PASS,"E":E,"rel":rel,"tail_pct":tail_pct}
print(f"\n{'PASS' if PASS else 'FAIL'} — N5 Guinand-Weil")
json.dump(result, open("outputs/N5.json","w"), indent=2)
sys.exit(0 if PASS else 1)
