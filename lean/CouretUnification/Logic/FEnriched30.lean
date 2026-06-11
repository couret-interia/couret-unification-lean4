/-
Copyright (c) 2026 Couret-Unification Programme.

# Logic/H3/FEnriched30.lean — Instanciation du foncteur enrichi à q = 30

## Doctrine

Ce fichier instancie FEnrichedSpec à q = 30, avec :
  - 8 résidus actifs : {1, 7, 11, 13, 17, 19, 23, 29} (coprimes à 30)
  - constante λ = 1/√7 (invariant géométrique du programme)
  - cible : Δ^7_{FR} (simplexe de dimension 7)

Ce fichier reste une cible typée du Registre I.
Aucune fermeture analytique de Fisher-Rao ou de Koopman n'est tentée.

-/

import CouretUnification.Logic.FEnrichedSpec
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

namespace CouretUnification.Logic.FEnriched30

open CouretUnification.Logic.FEnriched

/-!
## Section 1 — Les 8 résidus actifs mod 30

(ℤ/30ℤ)× = {1, 7, 11, 13, 17, 19, 23, 29}
-/

/-- [API] Les 8 résidus coprimes à 30. -/
def G30_residues : Fin 8 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 11
  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17
  | ⟨5, _⟩ => 19
  | ⟨6, _⟩ => 23
  | ⟨7, _⟩ => 29
  | ⟨n+8, h⟩ => absurd h (by omega)

/-- [API] Les 8 résidus sont bien tous coprimes à 30. -/
theorem G30_coprime_30 (i : Fin 8) : Nat.Coprime (G30_residues i) 30 := by
  fin_cases i <;> decide

/-!
## Section 2 — La constante λ = 1/√7

C'est l'invariant géométrique central du programme Couret-Unification.
La chaîne de dérivations log 3 → √3/2 → π/3 → 3/7 → 1/√7 le justifie.
-/

/-- [PROJ] La constante de Couret λ = 1/√7. -/
noncomputable def lambdaCouret : ℝ := 1 / Real.sqrt 7

/-- [P] λ_Couret est strictement positive. -/
theorem lambdaCouret_pos : 0 < lambdaCouret := by
  unfold lambdaCouret
  have h7 : (0 : ℝ) < 7 := by norm_num
  exact one_div_pos.mpr (Real.sqrt_pos.mpr h7)

/-- [P] λ_Couret < 1. -/
theorem lambdaCouret_lt_one : lambdaCouret < 1 := by
  unfold lambdaCouret
  have h7_gt_one : (1 : ℝ) < 7 := by norm_num
  have hsqrt : 1 < Real.sqrt 7 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) h7_gt_one
  exact (div_lt_one (lt_trans (by norm_num : (0:ℝ) < 1) hsqrt)).mpr hsqrt

/-- [P] λ_Couret² = 1/7. -/
theorem lambdaCouret_sq : lambdaCouret^2 = 1 / 7 := by
  unfold lambdaCouret
  rw [div_pow, one_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)]

/-!
## Section 3 — L'objet arithmétique mod 30

Instanciation de ArithmeticModularObject pour q = 30.
-/

/-- [PROJ] Données de A_30 : le vecteur des résidus actifs (poids uniforme). -/
noncomputable def A30_R : Fin 8 → ℝ := fun _ => 1 / 8  -- distribution uniforme initiale

/-- [PROJ] L'objet canonique A_30 dans 𝒜_Π^{mon}. -/
noncomputable def A30 : ArithmeticModularObject where
  modulus := 30
  modulus_pos := by norm_num
  dim_active := 8
  dim_pos := by norm_num
  R_q := A30_R
  R_q_pos := fun i => by
    simp [A30_R]

/-!
## Section 4 — Cible Fisher-Rao Δ^7_{FR}

L'objet cible : simplexe de dimension 7 (8 sommets, dim ambiante 7).
-/

/-- [PROJ] Image canonique de A_30 dans le simplexe Fisher-Rao. -/
noncomputable def FRSimplexImage_A30 : FisherRaoSimplexObject where
  dim := 8
  dim_pos := by norm_num
  prob := fun _ => 1 / 8
  prob_nonneg := fun _ => by norm_num
  prob_sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-!
## Section 5 — Cible typée du Registre I

On pose la "cible" comme un Prop conditionnel,
qui sera atteinte si la spécification est fermée.
-/

/-- [PROJ] La cible Registre I pour q = 30 :
    il existe un foncteur F^{enr} tel que F^{enr}(A_30) = Δ^7_{FR}. -/
def FEnriched30Target : Prop :=
  ∃ (F : FEnrichedCandidate),
    F.obj A30 = FRSimplexImage_A30

/-!
## Section 6 — Lien numérique avec le programme

Le test channel_balance_v7_2d.gp (PARI/GP) fournit l'évaluation
empirique du résiduel sur q = 30.
-/

/-- [PROJ] Borne empirique du résiduel sur q = 30
    (mesurée à 10^{-8} dans le programme). -/
noncomputable def empirical_residual_bound : ℝ := 10^(-8 : ℝ)

/-- [P] La borne empirique est strictement positive. -/
theorem empirical_residual_bound_pos : 0 < empirical_residual_bound := by
  unfold empirical_residual_bound
  exact Real.rpow_pos_of_pos (by norm_num) _

/-!
## Section 7 — Invariant constitutionnel
-/

/-- [API] Ce fichier ne prouve pas RH. -/
def RHClaimed : Bool := false
example : RHClaimed = false := rfl

/-- [API] La promotion de λ_Couret à "ancrage catégoriel" est conditionnelle
    à la fermeture de (F.2) sur q = 30. -/
def LambdaCategoricalAnchor_Conditional : Prop :=
  FEnriched30Target → True  -- placeholder

/-- [I] Identité du fichier — instanciation typée. -/
def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/FEnriched30.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.encoded
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

end CouretUnification.Logic.FEnriched30
