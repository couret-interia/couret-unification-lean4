/-!
# CouretUnification — façade canonique

Entrée publique officielle du projet Couret–Unification.

Ce fichier expose la stratification doctrinale minimale du dépôt :

1. noyau fini exact ;
2. critère Couret-Défaut ;
3. pont H3 conditionnel ;

Pour l’agrégation exhaustive de tous les modules du dépôt,
voir `CouretUnification.All`.

## Garde épistémique
`RHClaimed = false`.
-/

-- ─── Couche 1 : noyau fini exact ────────────────────────────
-- T1/T2 : G₃₀, TC, fantôme, CRT, Cayley, image quadratique
import CouretUnification.Core.U30
-- T3 : Spectre {3²,1⁴,(−1)²}, Fourier, Parseval, matrice
import CouretUnification.Finite.Foundations
-- T4-T7 : Projecteurs P₃/P₁/P₋, Pythagore, L_k, kurtosis
import CouretUnification.FiniteDefect.T1_to_T7

-- ─── Couche 2 : pont H3 conditionnel via éventail Phase B ───
-- PhaseBComposition : éventail à 5 branches (α, β, γ, δ, η)
-- agrégeant les résultats substantiels de Logic.H3.
-- Tire transitivement 13 des 14 modules Logic.H3.
-- RHClaimed = false. Sorry consommé : Lemma7Residual (branche β.2).
import CouretUnification.Logic.H3.PhaseBComposition

-- Racines indépendantes non tirées par PhaseBComposition :
-- Route C raffinée (Σ|E_d| ≤ θ · (φ/q) · S₁)
import CouretUnification.Logic.H3.RouteC
-- Arithmétique fondamentale (μ, M(n), κ(q), squarefree)
import CouretUnification.Logic.H3.Arithmetic
