/* channel_balance_v7.gp -- Guinand-Weil per channel
   Test function: h(t) = 2/(1/4 + t^2)  [= the V_eff function]

   Spectral:   V(chi) = sum_rho 2/(1/4 + gamma^2)
   Arithmetic: S(chi) = 2 * sum_{p,m} log(p) Re[chi(p^m)] / p^m
   Inferred:   W(chi) = V(chi) - S(chi)

   Both sides converge: no uncertainty principle issue.

   Couret-Unification -- April 2026
   RHClaimed = false */

P_MAX = 5000;
N_ZEROS = 500;

print("== GUINAND-WEIL v7 ==");
print("h(t) = 2/(1/4+t^2),  P_max=", P_MAX, " N_zeros=", N_ZEROS);

\\ Tables
cond_table = [1, 5, 5, 5, 3, 15, 15, 15];
parity_table = [0, 1, 0, 1, 1, 0, 1, 0];
fhat_table = [3, 1, 3, 1, -1, -1, -1, -1];
labels = ["zeta    ", "chi5_o4 ", "chi5_Leg", "chi5_o4c", "chi3    ", "chi15_c ", "chi15_r ", "chi15_cc"];

\\ V(chi) = sum 2/(1/4 + gamma^2)
V_from_zeros(zv) = { my(s = 0.0); for(i = 1, #zv, s += 2.0 / (0.25 + zv[i]^2)); s; };

\\ Arithmetic: S(chi) = 2 * sum log(p) Re[chi(p^m)] / p^m
S_from_char(chifn, pmax) = { my(s = 0.0); forprime(p = 2, pmax, my(logp = log(p)); for(m = 1, 10, my(pm = p^m, cv = chifn(pm)); if(cv != 0 && pm < 10^15, s += 2 * logp * real(cv) / pm))); s; };

\\ Characters
chi_1(n) = if(gcd(n, 30) == 1, 1, 0);
chi_3(n) = if(gcd(n, 30) == 1, kronecker(5, n), 0);
chi_5(n) = if(gcd(n, 30) == 1, kronecker(-3, n), 0);
chi_7(n) = if(gcd(n, 30) == 1, kronecker(-15, n), 0);

dlog5 = Map();
mapput(dlog5, 1, 0); mapput(dlog5, 2, 1); mapput(dlog5, 4, 2); mapput(dlog5, 3, 3);
chi_o4(n) = { my(r5 = n % 5); if(r5 == 0, return(0)); I^mapget(dlog5, r5); };
chi_2(n) = if(gcd(n, 30) == 1, chi_o4(n), 0);
chi_4(n) = conj(chi_2(n));
chi_6(n) = if(gcd(n, 30) == 1, kronecker(-3, n) * chi_o4(n), 0);
chi_8(n) = conj(chi_6(n));

\\ L-functions and zeros
print("Creating L-functions...");
L1 = lfuncreate(1);
L2 = lfuncreate(Mod(2, 5));
L3 = lfuncreate(5);
L5 = lfuncreate(-3);
L6 = lfuncreate(Mod(2, 15));
L7 = lfuncreate(-15);

print("Extracting zeros...");
z1 = lfunzeros(L1, N_ZEROS); print("  zeta:   ", #z1, " zeros");
z2 = lfunzeros(L2, N_ZEROS); print("  chi5o4: ", #z2, " zeros");
z3 = lfunzeros(L3, N_ZEROS); print("  chi5L:  ", #z3, " zeros");
z5 = lfunzeros(L5, N_ZEROS); print("  chi3:   ", #z5, " zeros");
z6 = lfunzeros(L6, N_ZEROS); print("  chi15c: ", #z6, " zeros");
z7 = lfunzeros(L7, N_ZEROS); print("  chi15r: ", #z7, " zeros");

\\ Compute V (spectral)
Vvec = vector(8);
Vvec[1] = V_from_zeros(z1);
Vvec[2] = V_from_zeros(z2);
Vvec[3] = V_from_zeros(z3);
Vvec[4] = Vvec[2];
Vvec[5] = V_from_zeros(z5);
Vvec[6] = V_from_zeros(z6);
Vvec[7] = V_from_zeros(z7);
Vvec[8] = Vvec[6];

\\ Compute S (arithmetic)
print("Computing arithmetic sums (P_max=", P_MAX, ")...");
Svec = vector(8);
Svec[1] = S_from_char(chi_1, P_MAX);
Svec[2] = S_from_char(chi_2, P_MAX);
Svec[3] = S_from_char(chi_3, P_MAX);
Svec[4] = S_from_char(chi_4, P_MAX);
Svec[5] = S_from_char(chi_5, P_MAX);
Svec[6] = S_from_char(chi_6, P_MAX);
Svec[7] = S_from_char(chi_7, P_MAX);
Svec[8] = S_from_char(chi_8, P_MAX);

\\ Results
print("");
print("=== RESULTS ===");
print("k  Label     Cond Par Fh   V(chi)        S(chi)        W=V-S");
print("----------------------------------------------------------------------");
for(k = 1, 8, my(Wk = Vvec[k] - Svec[k]); print(k, "  ", labels[k], " ", cond_table[k], "   ", parity_table[k], "  ", fhat_table[k], "  ", Vvec[k], "  ", Svec[k], "  ", Wk));

\\ Archimedean diagnostic
print("");
print("=== W INFERRED (should depend only on conductor + parity) ===");
print("Parity 0 (even):");
for(k = 1, 8, if(parity_table[k] == 0, print("  k=", k, " N=", cond_table[k], "  W=", Vvec[k] - Svec[k])));
print("Parity 1 (odd):");
for(k = 1, 8, if(parity_table[k] == 1, print("  k=", k, " N=", cond_table[k], "  W=", Vvec[k] - Svec[k])));

\\ V_eff computation (from test_veff.gp)
print("");
print("=== V_eff (weighted by |F_hat|^2/64) ===");
Veff = 0.0;
for(k = 1, 8, Veff += fhat_table[k]^2 / 64.0 * Vvec[k]);
print("  V_eff = ", Veff);
print("  1/7   = ", 1.0/7);
print("  ratio = ", Veff * 7);

\\ Defect projection
defect_coeffs = [0, -2, -2, 0, 0, 2, 2, 0];
Vd = 0.0; Sd = 0.0;
for(k = 1, 8, my(d = defect_coeffs[k]); if(d != 0, Vd += d * Vvec[k]; Sd += d * Svec[k]));
print("");
print("=== DEFECT d19-d29 ===");
print("  V_defect = ", Vd);
print("  S_defect = ", Sd);
print("  W_defect = ", Vd - Sd);

print("");
print("Parseval: ", sum(k=1,8,fhat_table[k]^2));
print("RHClaimed = false");
