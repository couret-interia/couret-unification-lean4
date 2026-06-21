/-
# Empirical/SophieGermainExpected.lean — Matrice HL attendue (v35.8)

## Statut épistémique

  - Couche : Empirical
  - Statut : [C] empirical — valeurs HL attendues calculées par Python
             (reproductible via SG_HL_matrix_calculation.py), encodées
             pour traçabilité et soumission éditoriale.
  - sorryCount : 0
  - RHClaimed = false
  - **Ce fichier n'est jamais importé par Logic/.**

## Doctrine

Ce fichier complète `Empirical/SophieGermainTransitions.lean` en
encodant explicitement la **matrice Hardy-Littlewood attendue**
sous l'hypothèse d'indépendance conditionnelle aux marginales
empiriques globales :

    E_HL[i,j] = (Σ_j' M_obs[i,j']) × (Σ_i' M_obs[i',j]) / N_total

ainsi que les résidus standardisés case par case et leur contribution
au χ² total.

Les valeurs encodées sont **calculées** par le script Python
`SG_HL_matrix_calculation.py` (joint au paquet) et arrondies à la
décimale appropriée. Aucune valeur n'est prouvée par Lean. La
traçabilité du calcul est garantie par le script reproductible.

## Lien avec la note de soumission

Cette matrice est la matière directement requise pour l'article
autonome Sophie Germain (cible : *Experimental Mathematics*). Elle
fournit le calcul χ²_HL case par case avec décomposition de la
contribution diagonale (55 % du total).
-/

import CouretUnification.Meta.Layer
import Mathlib.Data.Real.Basic

namespace CouretUnification
namespace Empirical
namespace SophieGermainExpected

open CouretUnification.Meta

/-! ## Section 1 — Matrice attendue HL (encodée) -/

/-- Matrice attendue sous Hardy-Littlewood pour les transitions SG mod 30,
    classes {11, 23, 29}, calculée à partir des marginales observées. -/
structure ExpectedMatrix where
  /-- Ligne 11 → {11, 23, 29}. -/
  e_11_11 : ℝ
  e_11_23 : ℝ
  e_11_29 : ℝ
  /-- Ligne 23 → {11, 23, 29}. -/
  e_23_11 : ℝ
  e_23_23 : ℝ
  e_23_29 : ℝ
  /-- Ligne 29 → {11, 23, 29}. -/
  e_29_11 : ℝ
  e_29_23 : ℝ
  e_29_29 : ℝ

/-- Valeurs attendues sous HL, calculées par Python sur N_total = 30 653. -/
def expected_HL : ExpectedMatrix := {
  e_11_11 := 3398.45
  e_11_23 := 3426.75
  e_11_29 := 3381.80
  e_23_11 := 3426.08
  e_23_23 := 3454.62
  e_23_29 := 3409.30
  e_29_11 := 3381.47
  e_29_23 := 3409.63
  e_29_29 := 3364.90
}

/-! ## Section 2 — Résidus standardisés (encodés) -/

/-- Résidus standardisés `R_ij = (O_ij − E_ij) / √E_ij`. -/
structure StandardizedResiduals where
  /-- Ligne 11. -/
  r_11_11 : ℝ
  r_11_23 : ℝ
  r_11_29 : ℝ
  /-- Ligne 23. -/
  r_23_11 : ℝ
  r_23_23 : ℝ
  r_23_29 : ℝ
  /-- Ligne 29. -/
  r_29_11 : ℝ
  r_29_23 : ℝ
  r_29_29 : ℝ

/-- Résidus calculés par Python. Les résidus diagonaux dominent
    en magnitude négative : signature de répulsion intra-classe. -/
def residuals_HL : StandardizedResiduals := {
  r_11_11 := -6.1144
  r_11_23 := 5.3170
  r_11_29 := 0.7773
  r_23_11 := 0.0840
  r_23_23 := -6.5098
  r_23_29 := 6.4687
  r_29_11 := 6.0452
  r_29_23 := 1.2223
  r_29_29 := -7.2904
}

/-! ## Section 3 — Décomposition χ² par case (% contribution) -/

/-- Contribution de chaque case au χ²_HL total (en pourcentage). -/
structure ChiSquareCellContribution where
  /-- Ligne 11. -/
  pct_11_11 : ℝ
  pct_11_23 : ℝ
  pct_11_29 : ℝ
  /-- Ligne 23. -/
  pct_23_11 : ℝ
  pct_23_23 : ℝ
  pct_23_29 : ℝ
  /-- Ligne 29. -/
  pct_29_11 : ℝ
  pct_29_23 : ℝ
  pct_29_29 : ℝ
  /-- Contribution diagonale totale. -/
  diagonal_total_pct : ℝ

/-- Décomposition par case du χ² total = 241.68. -/
def chi2_decomposition : ChiSquareCellContribution := {
  pct_11_11 := 15.47
  pct_11_23 := 11.70
  pct_11_29 := 0.25
  pct_23_11 := 0.00
  pct_23_23 := 17.53
  pct_23_29 := 17.31
  pct_29_11 := 15.12
  pct_29_23 := 0.62
  pct_29_29 := 21.99
  diagonal_total_pct := 55.00
}

/-! ## Section 4 — Résumé synthétique -/

/-- Synthèse complète pour soumission éditoriale (Experimental Mathematics). -/
structure HLAnalysisReport where
  /-- N_total observé (30 653 transitions). -/
  N_total : Nat
  /-- χ²_HL calculé. -/
  chi2_HL : ℝ
  /-- Degrés de liberté. -/
  df : Nat
  /-- Borne supérieure de la p-value. -/
  p_value_upper : ℝ
  /-- Maximum |résidu diagonal| en valeur absolue. -/
  max_diagonal_residual_abs : ℝ
  /-- Fraction du χ² provenant de la diagonale. -/
  diagonal_chi2_fraction : ℝ

def hl_analysis_report : HLAnalysisReport := {
  N_total := 30653
  chi2_HL := 241.6776
  df := 4
  p_value_upper := 1e-49
  max_diagonal_residual_abs := 7.2904
  diagonal_chi2_fraction := 0.55
}

/-! ## Section 5 — Énoncé descriptif -/

def empirical_statement : Statement := {
  title := "Matrice HL attendue + chi² par case (Sophie Germain mod 30)"
  layer := .C
  status := .empirical
  content :=
    "Calcul de la matrice E_HL[i,j] = (R_i × C_j) / N_total et χ² case " ++
    "par case sur N=30 653 transitions SG (p ≤ 10⁷). Diagonale contribue " ++
    "à 55% du χ²_HL total = 241.68 (df=4, p < 10⁻⁴⁹). Signature dominante : " ++
    "répulsion intra-classe à -6 à -7σ. Résultat indépendant de RH."
}

/-! ## Section 6 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Empirical/SophieGermainExpected.lean"
  layer := CouretUnification.Meta.Layer.C
  status := CouretUnification.Meta.Status.empirical
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl
example : fileIdentity.layer = .C := rfl

/-! ## Notes finales

1. **Reproductibilité** : toutes les valeurs encodées sont calculées
   par `SG_HL_matrix_calculation.py` (joint au paquet). Le script
   peut être réexécuté avec n'importe quel snapshot des données
   observées pour vérification.

2. **Aucune valeur prouvée par Lean** : ce sont des données numériques
   importées comme constantes. La traçabilité passe par le script
   Python, pas par une preuve formelle.

3. **Lecture correcte** : les données rejettent **très fortement** le
   modèle d'indépendance HL conditionnelle. Cela ne constitue pas
   une "loi structurelle démontrée" — c'est une régularité empirique
   forte, suggérant une mémoire arithmétique.

4. **Indépendant de RH** : aucun élément ne dépend ni ne contraint RH.

5. **Cible éditoriale** : *Experimental Mathematics*. Cet ensemble de
   données + interprétation est suffisant pour une soumission autonome.
-/

end SophieGermainExpected
end Empirical
end CouretUnification
