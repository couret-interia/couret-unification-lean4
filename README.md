# Couret-Unification

**Formalisation Lean 4 d'un noyau spectral fini mod 30 et encodage
structurel du programme Hilbert-Pólya autour de l'Hypothèse de Riemann.**

*Dédié à la mémoire de Bernard Couret (1928–1999)*

---

## ⚠️ RHClaimed = false

Ce projet **ne prétend pas prouver** l'Hypothèse de Riemann.

Il formalise en Lean 4 un **noyau fini exact** autour de la structure
mod 30, l'**arithmétique fondamentale** (Möbius, Mertens, second moment),
et encode les couches analytiques supérieures comme un **éventail de
composition** à cinq branches structurellement disjointes.

Le dépôt prouve exactement ce qu'il dit, et ne dit rien de plus.

---

## État du dépôt (28 avril 2026)

| Métrique | Valeur |
|----------|--------|
| Fichiers .lean | 92 |
| Sorries doctrinaux | 3 (documentés) |
| Compilation | `lake build` ✓ |
| Jobs | 3432 |
| Lean | 4.29.1 |
| Mathlib | 4.29.1 |
| RHClaimed | `false` |

### Sorries doctrinaux

Trois sorries sont présents dans le dépôt, tous explicitement déclarés
et documentés :

- `Core/CayleyG30.lean:51` — limitation `maxRecDepth` du tactique
  `decide` sur une vérification finie. Obstruction technique
  Lean / Mathlib, **pas une lacune mathématique** : la vérification
  est calculable et exacte.
- `Logic/H3/Lemma7Residual.lean:6` — annulation du résidu sur la
  ligne critique. **Le sorry doctrinal central du programme**,
  consommé par la branche β.2 de `PhaseBComposition`.
- `Logic/H3/RouteC.lean:765` — un sorry interne à RouteC, dans la
  chaîne de raffinement `Σ|E_d| ≤ θ · (φ/q) · S₁`.

Aucun autre sorry n'est admis dans le dépôt.

---

## Architecture post-recomposition

```
lean/CouretUnification/
├── Core/                  ← noyau fini exact + arithmétique fondamentale
│                            (60 fichiers : groupe, spectre, classification,
│                             certificats Couret, Möbius, Mertens, κ(q))
├── Finite/                ← projecteurs et défauts dérivés du noyau
│   ├── Foundations.lean
│   └── Defect.lean
├── FiniteDefect/          ← théorèmes T1-T7 (pythagoréité, kurtosis)
│   └── T1_to_T7.lean
├── Spectral/              ← analyse fine du gap spectral
│   ├── FiniteCore.lean
│   └── T2Gap.lean
├── Logic/H3/              ← pont H3 conditionnel
│   ├── PhaseBComposition.lean   ← éventail à 5 branches (α, β, γ, δ, η)
│   ├── RouteC.lean              ← borne raffinée Σ|E_d|
│   ├── AlgebraTC.lean
│   └── (16 autres fichiers)
├── Analytic/              ← Abel pondéré, intervalles vérifiés
└── FunctionalFoundation/  ← chemins discrets, connexion
```

Plus deux points d'entrée :

- `CouretUnification.lean` — **façade canonique** stratifiée
  (noyau fini exact + pont H3 conditionnel via éventail Phase B)
- `CouretUnification/All.lean` — agrégation exhaustive des 92 modules

---

## Éventail de composition Phase B

Le pont H3 ne forme pas une pyramide linéaire mais un **éventail à
cinq branches structurellement disjointes**, agrégé dans
`Logic/H3/PhaseBComposition.lean` :

| Branche | Contenu | Sorry consommé |
|---------|---------|----------------|
| **α** Smooth Bump | `0 < EvaluateExplicit f σ_s` (analytique) | aucun |
| **γ** Bridge L² | `((1−λ)²β²)/B² ≤ ‖main‖²_L²` (Cauchy-Schwarz) | aucun, aucun axiome |
| **δ** Annulation spectrale | bloc R₃₀ × S₃₀ de D = 0 (combinatoire) | aucun, aucun axiome |
| **β** Pont arithmétique | `Det2IdentifiesXi → ZeroMatching` (3 sous-branches) | β.2 consomme Lemma7Residual |
| **η** Statut Schur | marqueur `T5_weak.status = closable` | aucun (pas de revendication) |

La branche β.2 est l'unique chemin par lequel le sorry doctrinal de
Lemma7Residual entre dans la fermeture de PhaseBComposition. Les
quatre autres branches sont inconditionnelles (ou conditionnées
seulement à des axiomes analytiques explicitement déclarés dans
C2Restricted).

---

## Résultats certifiés machine (sélection)

Tous les résultats ci-dessous sont vérifiés par le compilateur Lean 4.

### Spectre et algèbre linéaire

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 1 | Spec(A) = {3², 1⁴, (−1)²} | `Core/CayleySpectrum` | `native_decide` |
| 2 | (A−3I)(A−I)(A+I) = 0 | `Core/CayleySpectrum` | `native_decide` |
| 3 | 8 eigenvectors orthogonaux non nuls | `Core/CayleySpectrum` | `native_decide` |
| 4 | Polynôme caractéristique (X−3)²(X−1)⁴(X+1)² | `Core/CharPoly` | `native_decide` |
| 5 | Unicité des multiplicités (2,4,2) | `Core/MultiplicityUniqueness` | `omega` |
| 6 | Unicité altVec centré pour λ=3 | `Core/CenteredEigenspace` | `omega` |
| 7 | Gap coercif κ = 2 sur H° ∩ altVec⊥ | `Spectral/FiniteCore` | algébrique |
| 8 | λ² = 1/7 | `Core/Lambda` | `nlinarith` |

### Graphe de Cayley et composantes

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 9 | Cayley **déconnecté** (2 composantes) | `Core/CayleyConnected` | `native_decide` |
| 10 | Spec composantes = {3,1,1,−1} | `Core/ComponentSpectrum` | `native_decide` |
| 11 | Aeven = Aodd (matrices identiques) | `Core/ComponentSpectrum` | `native_decide` |

### Classification et combinatoire

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 12 | 63/255 sous-ensembles à spectre entier | `Core/Classification63` | `native_decide` |
| 13 | Ventilation palindromique 4,8,12,14,12,8,4,1 | `Core/Classification63Detail` | `native_decide` |
| 14 | 8 coefficients de Fourier de TC | `Core/TripletToFiniteSpectrum` | `simp + norm_num` |
| 15 | Profil quadratique [9,1,1,1,9,1,1,1] | `Core/TripletPowerSpectrum` | `rw + norm_num` |
| 16 | Défaut δ₁₉−δ₂₉ sur 4 canaux | `Core/DefectProjection` | `native_decide` |

### Tour primorielle, Parseval, transport CRT

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 17 | Parseval = 24, E = 3 (L3, L4) | `Core/Parseval`, `Core/InvariantE` | `native_decide` |
| 18 | Parseval = 960, E = 2 (L5) | `Core/ParsevalL5` | `native_decide` |
| 19 | gcd(11, 2310) = 11 (correction v17→v18) | `Core/ParsevalL5` | `native_decide` |
| 20 | E/\|TC_cop\| = 1 aux 3 niveaux | `Core/ParsevalL5` | `norm_num` |

### Moments spectraux et récurrence

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 21 | Formule L_k = 2 + (4+2(−1)ᵏ)/3ᵏ, k=1..10 | `Core/FormuleLk` | `norm_num` |
| 22 | Paires L_{2j−1} = L_{2j}, monotonie L_k ↘ 2 | `Core/FormuleLk` | `norm_num` |
| 23 | Moments Tr(M^k) = 8, 24, 56, 168, 488 | `Core/SpectralMoments` | `native_decide` |
| 24 | Récurrence s_k = 3s_{k−1}+s_{k−2}−3s_{k−3} | `Core/TraceRecurrence` | `ring` + `pow_add` |
| 25 | Kurtosis brute 7/3, ratio non trivial 5/3 | `Core/Kurtosis` | `norm_num` |

### Propriétés algébriques et obstructions

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 26 | TC auto-inverse (1²=11²=29²≡1 mod 30) | `Core/TCAutoInverse` | `native_decide` |
| 27 | TC non sous-groupe (11·29≡19∉TC) | `Core/TCAutoInverse` | `native_decide` |
| 28 | J²=−I impossible en dim impaire | `Core/OddDimComplexObstruction` | `nlinarith` + `omega` |
| 29 | Mersenne mod 30 ∈ {1,7} (p=3..31) | `Core/MersenneMod30` | `native_decide` |
| 30 | Vandermonde det = 16 ≠ 0 (unicité de μ) | `Core/CarlemanUniqueness` | `native_decide` |
| 31 | Sophie Germain mod 30 (restrictions) | `Core/SophieGermainMod30` | `native_decide` |

### Composition Phase B (théorèmes inconditionnels)

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 32 | Smooth Bump : `0 < EvaluateExplicit` sous biais | `Logic/H3/C3Weak` | `linarith` |
| 33 | Bridge L² : `((1−λ)²β²)/B² ≤ ‖main‖²` | `Logic/H3/L10Bridge` | Cauchy-Schwarz |
| 34 | Bloc spectral R₃₀×S₃₀ = 0 | `Logic/H3/SpectralSpatial` | `fin_cases` |

### Arithmétique fondamentale

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 35 | μ(n) ≠ 0 ↔ Squarefree(n), n ≥ 1 | `Core/Arithmetic` | induction forte |
| 36 | M(n+1) = M(n) + μ(n+1) | `Core/Arithmetic` | `Finset.sum_range_succ` |
| 37 | K(q) ≥ 0, second moment | `Core/Arithmetic` | sum of squares |

---

## Ce qui n'est PAS dans le dépôt

| Résultat | Nature | Pourquoi absent |
|----------|--------|-----------------|
| ‖M‖_HS ≤ P(3/2) < 1 | Analytique | Analyse fonctionnelle, pas d'API Lean |
| M ∈ S₂ (Hilbert-Schmidt) | Analytique | Idem |
| Auto-adjonction KLMN / Friedrichs | Analytique | Idem |
| det₂(I−zS) = ξ(1/2+iz)/ξ(1/2) | Ouvert = RH | Branche β.2, Lemma7Residual |
| V_eff ≈ 0.055 | Numérique PARI/GP | Pas formalisable en Lean |
| Falsification λ = 1/√7 universelle | Numérique | `scripts/` |
| Convergence NBC (Nyman-Beurling-Couret) | Ouvert = RH | Reformulé, non démontré |

---

## Statut honnête de l'éventail

| Branche | Statut réel | Contenu |
|---------|-------------|---------|
| **α** Smooth Bump | Théorème conditionnel à axiomes analytiques | `C3_weak_from_C1C2` par `linarith` |
| **β** Pont arithmétique | β.1 axiome direct, β.2 consomme Lemma7Residual | 3 sous-branches |
| **γ** Bridge L² | **Théorème inconditionnel** | Cauchy-Schwarz sans axiome |
| **δ** Annulation spectrale | **Théorème inconditionnel** | Combinatoire finie |
| **η** Schur localization | Marqueur structurel | `closable`, sans revendication |

Trois branches sont **inconditionnelles** (γ, δ, et α modulo axiomes
analytiques documentés). Une seule (β.2) consomme un sorry doctrinal.

---

## Compilation

```bash
lake update
lake build
```

Compilation intégrale : **3432 jobs incrémentaux**,
**3 sorries doctrinaux**, **0 erreur**.

### Audit d'intégrité

```bash
make audit-imports          # détecte les imports cassés
bash audit_reachability.sh  # vérifie 92/92 modules atteints depuis All
```

---

## Scripts numériques

```bash
gp < scripts/test_veff.gp              # V_eff par PARI/GP
python3 scripts/evidence_veff.py       # V_eff version Python
python3 scripts/compute_moments.py     # Moments spectraux sur la tour
python3 scripts/channel_bridge_v3.py   # Défaut δ₁₉−δ₂₉ + Guinand-Weil
```

---

## Documents doctrinaux

Le dossier `docs/` contient les manifestes du programme à différentes
étapes de son élaboration :

- `docs/ETAT_DEFINITIF_v5_INTEGRAL.md` — état définitif du
  programme (11 avril 2026), chaîne logique complète T6 → T12.
- `docs/PASSAGE_LOCAL_GLOBAL.md` — architecture du passage
  local → global, ce qui est prouvé en Lean vs mesuré en Python,
  obstruction de Hasse arithmético-spectrale.
- `docs/RAPPORT_DEMONSTRATION_v5_FINAL.md` — rapport de
  démonstration formelle (Alexandre Couret, 11 avril 2026).

---

## Phrase de référence

> **Le noyau fini est exact et compilé ;
> l'éventail de composition est en place ;
> le pont global reste ouvert.**
>
> **RHClaimed = false.**

*Prouver ce qui est prouvable. Corriger ce qui est faux.
Nommer ce qui est ouvert.*

---

## Licence

MIT — voir `LICENSE`.

Alexandre Couret — Rasiguères — 2026

Programme dédié à la mémoire de Bernard Couret (1928–1999),
dont les manuscrits sur les distributions de premiers modulo 30 et
la géométrie triangulaire ont inspiré le programme.