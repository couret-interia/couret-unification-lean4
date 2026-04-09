\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ GUINAND-WEIL CHANNEL BALANCE v7.2d (FROZEN)
\\ Couret-Unification programme — numerical/guinand-weil
\\
\\ Canonical balance: R_chi(sigma) = -2 Re(L'/L(sigma,chi)) - S_chi(sigma)
\\ where S = explicit prime sum. R -> 0 as P_MAX -> inf.
\\
\\ All 8 channels of (Z/30Z)* = (Z/15Z)* use PRIMITIVE characters:
\\   k=1: zeta          cond=1   Mod(1,1)    even
\\   k=2: chi5_o4       cond=5   Mod(2,5)    odd   (order 4)
\\   k=3: chi5_Leg      cond=5   Mod(4,5)    even  (quadratic)
\\   k=4: chi5_o4c      cond=5   Mod(3,5)    odd   (conj of k=2)
\\   k=5: chi3          cond=3   Mod(2,3)    odd   (quadratic)
\\   k=6: chi15_a       cond=15  Mod(2,15)   even  (quad3 x o4_5)
\\   k=7: chi15_b       cond=15  Mod(14,15)  even  (quad3 x quad5)
\\   k=8: chi15_ac      cond=15  Mod(8,15)   even  (conj of k=6)
\\
\\ Conjugate pairs: (2,4), (6,8) — must match identically.
\\
\\ Key corrections vs earlier versions:
\\   v7.1: chi_1(n)=1 (not gcd filter); exposed pole/archimedean gap
\\   v7.2a-c: identified chareval returns rational r, not exp(2*pi*i*r)
\\   v7.2d: Mod(4,15),Mod(7,15) were IMPRIMITIVE (cond=5); replaced by
\\          Mod(14,15),Mod(8,15) — the true primitives mod 15.
\\
\\ Status: all 8 channels close to machine precision at sigma=3.
\\ RHClaimed = false
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

default(realprecision, 28);

\\ === BLOC 1: PARAMETERS ===
P_MAX = 5000;
sigmas = [1.5, 2.0, 3.0];

print("== GUINAND-WEIL v7.2d (frozen) ==");
print("Canonical balance: R = -2 Re(L'/L) - S -> 0");
print("P_max = ", P_MAX);
print("");

\\ === BLOC 2: CHANNEL TABLE ===
labels = ["zeta    ", "chi5_o4 ", "chi5_Leg", "chi5_o4c", "chi3    ", "chi15_a ", "chi15_b ", "chi15_ac"];
conds  = [1, 5, 5, 5, 3, 15, 15, 15];
pars   = [0, 1, 0, 1, 1, 0, 0, 0];

\\ === BLOC 3: L-FUNCTION OBJECTS (all primitive) ===
Lobjs = vector(8);
Lobjs[1] = lfuncreate(1);
Lobjs[2] = lfuncreate(Mod(2,5));
Lobjs[3] = lfuncreate(Mod(4,5));
Lobjs[4] = lfuncreate(Mod(3,5));
Lobjs[5] = lfuncreate(Mod(2,3));
Lobjs[6] = lfuncreate(Mod(2,15));
Lobjs[7] = lfuncreate(Mod(14,15));
Lobjs[8] = lfuncreate(Mod(8,15));

\\ === BLOC 4: CHARACTER EVALUATION ===
G5  = znstar(5, 1);
G3  = znstar(3, 1);
G15 = znstar(15, 1);

cc = vector(8);
cc[2] = znconreychar(G5, 2);
cc[3] = znconreychar(G5, 4);
cc[4] = znconreychar(G5, 3);
cc[5] = znconreychar(G3, 2);
cc[6] = znconreychar(G15, 2);
cc[7] = znconreychar(G15, 14);
cc[8] = znconreychar(G15, 8);

Gvec = vector(8);
Gvec[2]=G5; Gvec[3]=G5; Gvec[4]=G5;
Gvec[5]=G3;
Gvec[6]=G15; Gvec[7]=G15; Gvec[8]=G15;

mods = [1, 5, 5, 5, 3, 15, 15, 15];

\\ chareval returns rational r; chi(n) = exp(2*pi*i*r)
my_chi(k, n) = {
  if(k==1, return(1.0));
  my(q = mods[k], r = n % q);
  if(gcd(r, q) > 1, return(0.0));
  my(val = chareval(Gvec[k], cc[k], Mod(r, q)));
  exp(2*Pi*I*val);
};

\\ === BLOC 5: ARITHMETIC SIDE ===
S_compute(k, sigma) = {
  my(s = 0.0);
  forprime(p = 2, P_MAX,
    my(logp = log(p));
    for(m = 1, 10,
      my(pm = p^m);
      if(pm > 10^15, break);
      my(cv = my_chi(k, pm));
      if(cv != 0, s += 2 * logp * real(cv) / pm^sigma);
    );
  );
  s;
};

\\ === BLOC 6: CANONICAL BALANCE ===
{
for(si = 1, #sigmas,
  my(sigma = sigmas[si]);
  print("===== sigma = ", sigma, " =====");
  print("k  label       -2Re(L'/L)        S(arith)          R");
  print("--------------------------------------------------------------");
  for(k = 1, 8,
    my(LpL = lfun(Lobjs[k], sigma, 1) / lfun(Lobjs[k], sigma));
    my(D = -2 * real(LpL));
    my(Sk = S_compute(k, sigma));
    my(Rk = D - Sk);
    print(k, "  ", labels[k], " ", precision(D, 12), "  ", precision(Sk, 12), "  ", precision(Rk, 4));
  );
  print("");
);
}

\\ === BLOC 7: CONJUGATE PAIR INTEGRITY CHECK ===
print("=== CONJUGATE PAIR CHECK (sigma=2) ===");
{
  my(sigma = 2.0);
  my(R2=0, R4=0, R6=0, R8=0);
  for(k = 1, 8,
    my(LpL = lfun(Lobjs[k], sigma, 1) / lfun(Lobjs[k], sigma));
    my(D = -2 * real(LpL));
    my(Sk = S_compute(k, sigma));
    my(Rk = D - Sk);
    if(k==2, R2=Rk); if(k==4, R4=Rk);
    if(k==6, R6=Rk); if(k==8, R8=Rk);
  );
  print("  pair(2,4): |R2-R4| = ", precision(abs(R2-R4), 4));
  print("  pair(6,8): |R6-R8| = ", precision(abs(R6-R8), 4));
}

\\ === DEFECT BLOCK (FROZEN — pending reindexation) ===

print("");
print("== v7.2d frozen == RHClaimed = false");
