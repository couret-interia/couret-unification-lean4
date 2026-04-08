/* ================================================================
   PACK THOMAS — Calcul V_eff exact
   Programme Couret-Unification, 6 avril 2026

   OBJECTIF : calculer V_eff = Σ |c_χ|² V(χ) pour les 8 caractères
   mod 30 et vérifier si V_eff ≈ 1/7 = 0.142857...

   PRÉREQUIS : PARI/GP (sudo apt install pari-gp)
   TEMPS : < 1 minute
   ================================================================ */

/* ────────────────────────────────────────────────────────────────
   CONTEXTE POUR THOMAS

   On a 8 caractères de Dirichlet mod 30.
   Le triplet de Couret TC = {1, 11, 29} dans (Z/30Z)*.

   Chaque caractère χ a un coefficient de Fourier c_χ :
     (0,0) principal  : c = 3/8,  |c|² = 9/64,  conducteur 1  (= ζ)
     (0,2) Legendre/5  : c = 3/8,  |c|² = 9/64,  conducteur 5
     (1,0) Legendre/3  : c = -1/8, |c|² = 1/64,  conducteur 3
     (1,2) χ₃·χ₅²     : c = -1/8, |c|² = 1/64,  conducteur 15
     (0,1) ordre 4/5   : c = 1/8,  |c|² = 1/64,  conducteur 5
     (0,3) conj(0,1)   : c = 1/8,  |c|² = 1/64,  conducteur 5
     (1,1) χ₃·ordre4/5 : c = 1/8,  |c|² = 1/64,  conducteur 15
     (1,3) conj(1,1)   : c = 1/8,  |c|² = 1/64,  conducteur 15

   Pour chaque caractère, on calcule :
     V(χ) = Σ_{γ>0} 2/(1/4 + γ²)
   où les γ sont les parties imaginaires des zéros sur la ligne critique.

   Puis : V_eff = Σ |c_χ|² V(χ)

   Question : V_eff = 1/7 ?
   ──────────────────────────────────────────────────────────────── */

\\ ================================================================
\\ ÉTAPE 1 : Fonction qui calcule V(χ) à partir des zéros
\\ ================================================================

V_from_zeros(zeros_vec) = {
  my(s = 0.0);
  for(i = 1, #zeros_vec,
    my(g = zeros_vec[i]);
    s += 2.0 / (0.25 + g^2)
  );
  s
};

\\ ================================================================
\\ ÉTAPE 2 : Calcul des zéros pour chaque L-function primitive
\\
\\ PARI/GP encode les caractères de Dirichlet via :
\\   - Kronecker symbols pour les réels : lfuncreate(D)
\\   - Mod(n, q) pour les caractères généraux
\\
\\ Les 4 conducteurs primitifs sont 1, 3, 5, 15.
\\ Certains caractères sont complexes (ordre 4).
\\ ================================================================

print("=== CALCUL V_eff EXACT ===");
print("N = 500 zéros par caractère (erreur < 1%)");
print("");

\\ --- Caractère principal : ζ(s), conducteur 1 ---
print("Computing V(zeta)...");
Lz = lfuncreate(1);
zz = lfunzeros(Lz, 500);
Vz = V_from_zeros(zz);
print("  V(zeta) = ", Vz, "  (", #zz, " zeros)");

\\ --- Legendre mod 3 : Kronecker(-3/.), conducteur 3, pair ---
print("Computing V(chi_3)...");
L3 = lfuncreate(-3);
z3 = lfunzeros(L3, 500);
V3 = V_from_zeros(z3);
print("  V(chi_3) = ", V3, "  (", #z3, " zeros)");

\\ --- Legendre mod 5 : Kronecker(5/.), conducteur 5, pair ---
print("Computing V(chi_5 Legendre)...");
L5 = lfuncreate(5);
z5 = lfunzeros(L5, 500);
V5 = V_from_zeros(z5);
print("  V(chi_5 Leg) = ", V5, "  (", #z5, " zeros)");

\\ --- Ordre 4 mod 5 : caractère complexe, conducteur 5, impair ---
\\ En PARI : Mod(2, 5) est un générateur de (Z/5Z)*,
\\ le caractère d'ordre 4 est chi(2) = i
print("Computing V(chi_5 order 4)...");
L5c = lfuncreate(Mod(2, 5));
z5c = lfunzeros(L5c, 500);
V5c = V_from_zeros(z5c);
print("  V(chi_5 ord4) = ", V5c, "  (", #z5c, " zeros)");

\\ --- Caractères mod 15 ---
\\ chi_3 * chi_5_Legendre : conducteur 15, pair
\\ Kronecker(-15/.) ou Mod(2, 15) selon la table
print("Computing V(chi_15 real)...");
L15r = lfuncreate(-15);
z15r = lfunzeros(L15r, 500);
V15r = V_from_zeros(z15r);
print("  V(chi_15 real) = ", V15r, "  (", #z15r, " zeros)");

\\ chi_3 * chi_5_order4 : conducteur 15, impair, complexe
\\ Mod(2,15) a ordre lcm(2,4)=4 dans (Z/15Z)*
print("Computing V(chi_15 complex)...");
L15c = lfuncreate(Mod(2, 15));
z15c = lfunzeros(L15c, 500);
V15c = V_from_zeros(z15c);
print("  V(chi_15 cpx) = ", V15c, "  (", #z15c, " zeros)");

\\ ================================================================
\\ ÉTAPE 3 : Assemblage de V_eff
\\
\\ Poids |c_χ|² :
\\   principal (cond 1)      : 9/64
\\   Legendre/5 (cond 5)     : 9/64
\\   Legendre/3 (cond 3)     : 1/64
\\   chi_15 real (cond 15)   : 1/64
\\   ordre4/5 (cond 5)       : 1/64  (×2 car conjugué)
\\   chi_15 cpx (cond 15)    : 1/64  (×2 car conjugué)
\\
\\ Total : 9+9+1+1+2+2 = 24/64 = 3/8  ✓ (Parseval)
\\ ================================================================

print("");
print("=== ASSEMBLAGE V_eff ===");
print("");

Veff = (9/64)*Vz + (9/64)*V5 + (1/64)*V3 + (1/64)*V15r + (2/64)*V5c + (2/64)*V15c;

print("Contributions :");
print("  (9/64) * V(zeta)      = ", (9/64)*Vz);
print("  (9/64) * V(chi5_Leg)  = ", (9/64)*V5);
print("  (1/64) * V(chi3)      = ", (1/64)*V3);
print("  (1/64) * V(chi15_r)   = ", (1/64)*V15r);
print("  (2/64) * V(chi5_o4)   = ", (2/64)*V5c);
print("  (2/64) * V(chi15_c)   = ", (2/64)*V15c);
print("");

print("========================================");
print("  V_eff     = ", Veff);
print("  1/7       = ", 1/7.0);
print("  sqrt(Veff)= ", sqrt(Veff));
print("  1/sqrt(7) = ", 1/sqrt(7.0));
print("  RATIO     = ", Veff / (1/7.0));
print("========================================");
print("");

\\ Vérification Parseval
sum_c2 = 9/64 + 9/64 + 1/64 + 1/64 + 2/64 + 2/64;
print("Check Parseval : sum |c|^2 = ", sum_c2, " (doit etre 3/8 = ", 3/8.0, ")");

\\ V_bar = V_eff / sum_c2 (moyenne pondérée des V)
Vbar = Veff / sum_c2;
print("V_bar = V_eff / (3/8) = ", Vbar);
print("Cible V_bar si V_eff=1/7 : 64/105 = ", 64/105.0);
print("Ratio V_bar / cible = ", Vbar / (64/105.0));

print("");
print("=== CONTROLE DE STABILITE (N=300 vs N=500) ===");
\\ Recalculer avec seulement les 300 premiers zéros
V_from_first_N(zeros_vec, N) = {
  my(s = 0.0, m = min(N, #zeros_vec));
  for(i = 1, m, s += 2.0 / (0.25 + zeros_vec[i]^2));
  s
};

Veff_300 = (9/64)*V_from_first_N(zz,300) + (9/64)*V_from_first_N(z5,300) + (1/64)*V_from_first_N(z3,300) + (1/64)*V_from_first_N(z15r,300) + (2/64)*V_from_first_N(z5c,300) + (2/64)*V_from_first_N(z15c,300);

print("  V_eff(N=300) = ", Veff_300);
print("  V_eff(N=500) = ", Veff);
print("  Derive relative = ", abs(Veff - Veff_300)/Veff * 100, "%");
print("  (doit etre < 1%)");

print("");
print("=== FIN ===");
print("Si RATIO ~ 1.00 : la proximite 3/8 ~ 1/sqrt(7) a un mecanisme analytique.");
print("Si RATIO loin de 1 : c'est une coincidence numerique. Erreur 23 fermee.");
