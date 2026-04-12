# Passage Local → Global : Dossier Complet
## Programme Couret-Unification — Avril 2026

---

## 1. Architecture du passage

```
ACQUIS (local)                          OUVERT (global)
─────────────                          ──────────────
Noyau fini mod 30
  │ spectre {3²,1⁴,(−1)²}
  │ Parseval/φ = 3
  ↓
Tour primoriale
  │ CRT : φ(qp) = φ(q)·(p−1)
  │ Parseval invariant sous transport
  │ Défaut IR : Δ_χ = −χ(p)
  │ β_IR = 1/(p−1) → 0
  ↓
Décomposition channelwise
  │ 8 caractères mod 30
  │ conducteurs 1, 3, 5, 15
  │ Π(g,χ) calculé par canal
  ↓
Formule explicite Guinand-Weil     ←── T4 acquis (résidu 0.92%)
  │ Z + Π = A vérifié numériquement
  │ Convention Lorentzian h=W²/(r²+W²)
  ↓
                                       Complétion eulérienne (C2) ← OUVERT
                                         │ Queue p≥7 = 12.2% de Π
                                         │ Route multiplicative MORTE
                                         ↓
                                       Normalisation archimédienne (C1) ← OUVERT
                                         │ ψ(1/4+it/2) vs log|z| mismatch
                                         │ B_arch domine (~1.13)
                                         ↓
                                       Appariement des zéros (C3) ← OUVERT
                                         │ det₂(I−zS) ∝ ξ(1/2+iz)
                                         │ = lock3 = Hilbert-Pólya
                                         ↓
                                       RH (conditionnel à lock3)
```

## 2. Ce qui est PROUVÉ (Lean)

### 2.1 Tour primoriale — transport CRT
```
φ(30)    = 8     [native_decide]
φ(210)   = 48    [native_decide]  = 8 · 6   = 8 · (7−1)
φ(2310)  = 480   [native_decide]  = 48 · 10  = 48 · (11−1)
φ(30030) = 5760  [native_decide]  = 480 · 12 = 480 · (13−1)
```
Le transport CRT préserve Parseval/φ = 3 exactement à chaque niveau.

### 2.2 Défaut d'Euler infrarouge (identité exacte)
Pour chaque transition q → qp, le défaut par caractère hérité est :
```
Δ_χ^IR(q,p) = −χ(p)     [exact, pas asymptotique]
‖Δ_IR‖² = φ(q)          [somme sur tous les caractères]
β_IR = 1/(p−1)           [normalisé par φ(qp)]
```
β_IR → 0 le long de la tour = **liberté asymptotique arithmétique**.

### 2.3 Chaîne Hadamard / Lock 2 dissous
```
B₁ = 0  [prouvé algébriquement : ∀ B₁, (∀ s, B₁·s = B₁·(1−s)) → B₁ = 0]
```
Conséquence : det₂ = ξ/ξ(1/2) est **tautologique** conditionnellement à lock3.
Lock 2 n'est pas un verrou indépendant.

### 2.4 Pipeline T5 → T6 (compilé)
```
AbelTailCore v8 :  ∫_T^∞ log(t)/t³ dt = O(log T / T²)  [compilé, 0 sorry]
AbelTailCompare :  f = O(abelIntegrand) → tailIntegral f = O(log T / T²)
Integration :      mkSpectralDataFromAbel → SpectralData.hAbelTail
ZeroDensityAxioms: boundaryTermBound = O(T log T) · O(T⁻³) = O(log T / T²)
                   spectralTailBound = boundaryTermBound + hAbelTail
```

### 2.5 Pont 7 composantes (Lean typé)
```
finiteCore       : closed        [T1]
characterDecomp  : constructed   [8 caractères, CRT]
primorialTower   : constructed   [transport, Parseval]
eulerPartial     : constructed   [Euler partiel {2,3,5}]
limitOperator    : conditional   [dépend de HS norm control]
traceFormula     : OPEN          [H3 = LE MUR]
zeroMatching     : OPEN          [lock3]
```

## 3. Ce qui est MESURÉ (Python)

### 3.1 Guinand-Weil scalaire (T4)
Formule vérifiée à 0.92% :
```
Z_all = −2.2308  (200 nt + 500 triv zeros)
A − Π = −2.2103  (archimédien − premiers)
E     = −0.0205  (résidu)
|E|/|Z| = 0.0092
```
Test function : h(r) = W²/(r²+W²), W=2.

### 3.2 Décomposition eulérienne
```
Π_{2,3,5}  = 0.5069  (87.8%)  ← mod 30 visible
Π_{7}      = 0.0303  ( 5.2%)  ← premier manquant
Π_{11..29} = 0.0329  ( 5.7%)
Π_{≥31}    = 0.0074  ( 1.3%)
Queue p≥7  = 12.2%   ← NON négligeable
```

### 3.3 Channelwise Π(g,χ)
```
χ(0,0) trivial │ Π = 0.5775  │ ratio 1.000
χ(0,1) f=5     │ Π = 0.0257  │ ratio 0.044
χ(0,2) f=5     │ Π = 0.0283  │ ratio 0.049
χ(0,3) f=5     │ Π = 0.0257  │ ratio 0.044
χ(1,0) f=3     │ Π = 0.0231  │ ratio 0.040
χ(1,1) f=15    │ Π = 0.0239  │ ratio 0.041
χ(1,2) f=15    │ Π = 0.0412  │ ratio 0.071
χ(1,3) f=15    │ Π = 0.0239  │ ratio 0.041
```
Le trivial domine. Les 7 non-triviaux contribuent 4-7% chacun.

### 3.4 Séparation archimédien / eulérien
```
A_even (ψ at 1/4) = −0.9603
A_odd  (ψ at 3/4) = −2.2105
Δ(A)               =  1.2502
```
Le mismatch archimédien est d'ordre O(1), pas infinitésimal.
B_euler ≈ 0 en régime tronqué, mais B_arch domine.

### 3.5 V(χ) — Premier calcul (T_max=30)
```
χ₀ (ζ)  │ V = 0.037  │ (50 zéros mpmath)
χ₀₁ f=5 │ V = 4.185  │ (37 zéros)
χ₀₂ f=5 │ V = 1.369  │ (38 zéros)
χ₀₃ f=5 │ V = 2.057  │ (43 zéros)
χ₁₀ f=3 │ V = 1.085  │ (30 zéros)
χ₁₁ f=15│ V = 1.753  │ (48 zéros)
χ₁₂ f=15│ V = 1.604  │ (45 zéros)
χ₁₃ f=15│ V = 2.443  │ (59 zéros)

V_eff = Σ |c_χ|² · V(χ) / Σ |c_χ|² = 1.696
Cible 1/7 = 0.143
Ratio V_eff/(1/7) = 11.88
```
Le ratio ≠ 1 avec T_max=30. Troncature sévère probable.

## 4. Ce qui BLOQUE (H3)

### 4.1 Structure fine de H3
```
H3.A1–A6 : Fermeture fonctionnelle    [FERMÉ, 6 pièces]
H3.B1    : Euler + archimédien        [IDENTIFIÉ, 95%]
H3.B2    : Cohérence                   [VALIDÉ NUM., 95%]
H3.C1    : det₂ ∼ ξ(s)               [CANDIDAT, 30-50%, BLOQUANT]
```

### 4.2 Les 3 sous-verrous
- **C1 (archimédien)** : la normalisation gamma exacte. Le facteur
  Γ_R(s) = π^{-s/2}Γ(s/2) doit être absorbé par l'opérateur.
  Structuré mais non fermé.

- **C2 (eulérien global)** : la complétion au-delà de {2,3,5}.
  Route multiplicative MORTE (R(s) croît exponentiellement).
  Route coefficientielle (Euler-Trace) viable mais non exécutée.

- **C3 (appariement des zéros)** : det₂(I−zS) = C·ξ(1/2+iz).
  Conditionnel à C1+C2. C'est lock3.

### 4.3 Le sorry unique
```lean
-- Logic/H3/Lemma7Residual.lean
theorem critical_line_residual_vanishes
    (hBridge : ArithmeticBridgeRecord)
    (hLocal : hBridge.euler.local_factors_modelled)
    (hArch : hBridge.arch.gamma_factor_identified)
    (hNorm : hBridge.arch.gamma_normalization_exact)
    (hComp : hBridge.euler.completion_beyond_235) :
    hBridge.euler.critical_line_residual_vanishes := by
  sorry  -- ← UNIQUE SORRY = lock3 = Hilbert-Pólya
```

### 4.4 Pourquoi le local ne suffit pas
Le local donne :
- Σ_χ ⟨S_k 1, χ⟩ L(χ,s) = Σ_{(n,q_k)=1} Λ_k(n) n^{-s}  [exact pour q_k fixé]
- Quand k → ∞, le côté droit → −ζ'/ζ(s)
- Mais le côté gauche diverge (Σ sur tous les caractères)
- La renormalisation ln(p_k) · S̃_k stabilise la limite (Mertens)
- MAIS : le passage Σ_k → Σ_∞ est le cœur arithmétique ouvert

Autrement dit : **chaque étage fini est exact, le recollement infini est le mur.**

## 5. Résultats négatifs sur le passage

### 5.1 Route multiplicative MORTE
det₂ ≠ K̃ × Euler. Le résidu R(s) = K̃(s)/[π^{-s/2}Γ(s/2)]
croît exponentiellement sur la ligne critique. Mismatch 10⁶ à k=4.

### 5.2 Renormalisation scalaire insuffisante
det₂(I−z·c·S) = ∏(1−zc·λ_n)e^{zc·λ_n}. Un scalaire c dilate
tous les eigenvalues uniformément. Mais le produit d'Euler exige
des facteurs (1−p^{-s})^{-1} indépendants par premier.

### 5.3 Obstruction de Hasse (analogie structurelle)
Les solutions locales (canaux χ) existent et sont cohérentes.
Mais la compatibilité globale (recollement en ξ) bloque.
H3 est une obstruction de Hasse arithmético-spectrale.

## 6. Pistes ouvertes pour le passage

### 6.1 Tour des caractères + Euler-Trace (piste 3+4+5)
Décomposer le passage global en composantes de caractères.
Mesurer E_{T,χ} par canal séparément. Si tous convergent
indépendamment, le pont se ferme canal par canal.

### 6.2 Résidu unique explicite
H3 réduit à : `critical_line_residual_vanishes`.
C'est le contenu irréductible. Si ce lemme tombe, tout suit.

### 6.3 V_eff à haute résolution
Refaire le test V_eff avec T_max=1000+ (PARI/lcalc).
Le ratio V_eff/(1/7) est le test quantitatif décisif.

---

**Formule de synthèse :** Le local est exact, le transport est prouvé,
la formule explicite est vérifiée à 0.92%. Le mur est le recollement
infini : passer de Σ_k (fini, exact) à Σ_∞ (global, ouvert).
RHClaimed = false.
