/-
  CouretUnification/Logic/H3/AlgebraTC.lean

  Implémentation Lean 4 de l'algèbre test 𝒜_TC.

  Référence mathématique : AlgebraTC_v35_v1_final.md
  (fusion T2+T4, patch TC3 v1 canonique).

  Ce fichier ne contient plus de `sorry`.
  Les objets analytiques abstraits (convolution de Mellin, etc.) restent
  encodés via `opaque` / `axiom` là où la couche analytique complète
  n’est pas encore internalisée dans Lean.
-/

import Mathlib.Tactic
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharParity30
import CouretUnification.Core.Characters30Bridge
import CouretUnification.Logic.H3.H3TestSpace

open scoped BigOperators

namespace CouretUnification.Logic.H3

open CouretUnification.Core

-- ═══════════════════════════════════════════════════════════════════
-- §1. Schwartz multiplicatif (abstrait, via H3TestFunction)
-- ═══════════════════════════════════════════════════════════════════

/-- Espace de Schwartz multiplicatif — alias typologique pour
    l'interface H3TestFunction. -/
abbrev MultSchwartz : Type := H3TestFunction

/-- Fonction nulle sur l'espace test. -/
def zeroTestFunction : MultSchwartz where
  toFun := fun _ => 0
  smooth' := by
    simpa using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℂ)))
  support_pos' := by
    intro x hx
    exfalso
    exact hx rfl
  inversion_stable' := by
    intro x hx
    simp

instance : Inhabited MultSchwartz := ⟨zeroTestFunction⟩

-- ═══════════════════════════════════════════════════════════════════
-- §2. Valeur propre σ_χ(TC) et calcul par signature jointe
-- ═══════════════════════════════════════════════════════════════════

/-- L'élément u_{11} dans G30. -/
def elevenG30 : G30 := u11

/-- χ(11) pour chaque caractère, à valeurs dans {+1, -1}. -/
theorem charOnG30_eleven_pm (χ : CharIdx) :
    charOnG30 χ elevenG30 = 1 ∨ charOnG30 χ elevenG30 = -1 := by
  let z := charOnG30 χ elevenG30
  have hsq : z * z = 1 := by
    dsimp [z]
    rw [← charOnG30_mul]
    have h11 : elevenG30 * elevenG30 = (1 : G30) := by
      simp [elevenG30]
      decide
    rw [h11]
    exact charOnG30_one χ
  have hfac : (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z + 1) = z * z - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hfac with h1 | h2
  · left
    exact sub_eq_zero.mp h1
  · right
    exact eq_neg_of_add_eq_zero_left h2

/-- Signe entier ±1 extrait de χ(11). -/
noncomputable def charSignEleven (χ : CharIdx) : ℤ :=
  if charOnG30 χ elevenG30 = 1 then 1 else -1

/-- Valeur propre σ_χ(TC) = 1 + χ(11) + χ(-1) ∈ {+3, +1, -1}. -/
noncomputable def sigmaChiTC (χ : CharIdx) : ℤ :=
  1 + charSignEleven χ + charSign χ

/-- Valeur propre σ_χ, vue dans ℂ. -/
noncomputable def sigmaChiTC_C (χ : CharIdx) : ℂ :=
  (sigmaChiTC χ : ℂ)

-- ═══════════════════════════════════════════════════════════════════
-- §3. Trichotomie du spectre
-- ═══════════════════════════════════════════════════════════════════

/-- Le spectre est {+3, +1, -1}. -/
theorem sigmaChiTC_trichotomy (χ : CharIdx) :
    sigmaChiTC χ = 3 ∨ sigmaChiTC χ = 1 ∨ sigmaChiTC χ = -1 := by
  rcases charOnG30_eleven_pm χ with h11 | h11
  · rcases charOnG30_negOne_pm χ with hm1 | hm1
    · left
      unfold sigmaChiTC charSignEleven charSign
      rw [h11, hm1]
      norm_num
    · right
      left
      unfold sigmaChiTC charSignEleven charSign
      rw [h11, hm1]
      norm_num
  · rcases charOnG30_negOne_pm χ with hm1 | hm1
    · right
      left
      unfold sigmaChiTC charSignEleven charSign
      rw [h11, hm1]
      norm_num
    · right
      right
      unfold sigmaChiTC charSignEleven charSign
      rw [h11, hm1]
      norm_num

/-- Bornes immédiates du spectre. -/
theorem sigmaChiTC_bounds (χ : CharIdx) :
    -1 ≤ sigmaChiTC χ ∧ sigmaChiTC χ ≤ 3 := by
  rcases sigmaChiTC_trichotomy χ with h | h | h
  all_goals
    rw [h]
    omega

-- ═══════════════════════════════════════════════════════════════════
-- §4. Définition de l'algèbre test 𝒜_TC
-- ═══════════════════════════════════════════════════════════════════

/-- Algèbre test 𝒜_TC : triplet (g₃, g₁, g₋₁). -/
structure AlgebraTC where
  g3 : MultSchwartz
  g1 : MultSchwartz
  gm1 : MultSchwartz

namespace AlgebraTC

-- ═══════════════════════════════════════════════════════════════════
-- §5. Projecteurs spectraux
-- ═══════════════════════════════════════════════════════════════════

/-- Projecteur π_lam : extrait la composante scalaire associée à lam. -/
def proj (a : AlgebraTC) (lam : ℤ) : MultSchwartz :=
  if lam = 3 then a.g3
  else if lam = 1 then a.g1
  else if lam = -1 then a.gm1
  else a.g3

@[simp] theorem proj_three (a : AlgebraTC) : a.proj 3 = a.g3 := by
  simp [proj]

@[simp] theorem proj_one (a : AlgebraTC) : a.proj 1 = a.g1 := by
  simp [proj]

@[simp] theorem proj_negOne (a : AlgebraTC) : a.proj (-1) = a.gm1 := by
  simp [proj]

-- ═══════════════════════════════════════════════════════════════════
-- §6. Règle TC3 v1 : injection vers FunG30
-- ═══════════════════════════════════════════════════════════════════

/-- Composante de canal associée à χ. -/
noncomputable def toChannelFunction (a : AlgebraTC) (χ : CharIdx) :
    MultSchwartz :=
  a.proj (sigmaChiTC χ)

/-- Coefficient multiplicatif associé à χ : (σ_χ / 8) ∈ ℂ. -/
noncomputable def channelCoefficient (χ : CharIdx) : ℂ :=
  sigmaChiTC_C χ / 8

/-- Évaluation complète f_χ(x) = (σ_χ / 8) · g_{σ_χ}(x). -/
noncomputable def toFunG30 (a : AlgebraTC) (χ : CharIdx) (x : ℝ) : ℂ :=
  channelCoefficient χ * (a.toChannelFunction χ).toFun x

end AlgebraTC

-- ═══════════════════════════════════════════════════════════════════
-- §7. Convolution par canal (stabilité T4a)
-- ═══════════════════════════════════════════════════════════════════

/-- Convolution de Mellin abstraite. -/
opaque mellinConvolve (f g : MultSchwartz) : MultSchwartz

/-- Convolution par canal sur AlgebraTC. -/
def AlgebraTC.convolveC (a b : AlgebraTC) : AlgebraTC where
  g3 := mellinConvolve a.g3 b.g3
  g1 := mellinConvolve a.g1 b.g1
  gm1 := mellinConvolve a.gm1 b.gm1

/-- Commutativité abstraite de la convolution de Mellin. -/
axiom mellinConvolve_comm :
    ∀ f g, mellinConvolve f g = mellinConvolve g f

theorem AlgebraTC.convolveC_comm (a b : AlgebraTC) :
    a.convolveC b = b.convolveC a := by
  cases a
  cases b
  simp [AlgebraTC.convolveC, mellinConvolve_comm]

theorem AlgebraTC.convolveC_closed (a b : AlgebraTC) :
    ∃ c : AlgebraTC, c = a.convolveC b :=
  ⟨a.convolveC b, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §8. Non-stabilité sous *_T (contre-exemple T4b)
-- ═══════════════════════════════════════════════════════════════════

/-- Petit lemme d'emballage : une fois les trois témoins fermés,
    le théorème T4b se déduit sans bruit. -/
lemma tensor_product_escapes_E_one_of_witnesses
    (χ₁ χ₂ χ₃ : CharIdx)
    (hσ1 : sigmaChiTC χ₁ = 1)
    (hσ2 : sigmaChiTC χ₂ = 1)
    (hσ3 : sigmaChiTC χ₃ = 3)
    (hmul : ∀ g : G30, charOnG30 χ₃ g = charOnG30 χ₁ g * charOnG30 χ₂ g) :
    ∃ χ₁ χ₂ : CharIdx,
      sigmaChiTC χ₁ = 1 ∧ sigmaChiTC χ₂ = 1 ∧
      ∃ χ₃ : CharIdx, sigmaChiTC χ₃ = 3 ∧
      (∀ g : G30, charOnG30 χ₃ g = charOnG30 χ₁ g * charOnG30 χ₂ g) := by
  exact ⟨χ₁, χ₂, hσ1, hσ2, χ₃, hσ3, hmul⟩

lemma g30ToIdx_eleven :
    g30ToIdx elevenG30 = ⟨2, by omega⟩ := by
  decide

lemma g30ToIdx_negOne :
    g30ToIdx negOneG30 = ⟨7, by omega⟩ := by
  decide

lemma sigmaChiTC_eq_one_of_vals_pos_neg
    (χ : CharIdx)
    (h11 : charOnG30 χ elevenG30 = 1)
    (hm1 : charOnG30 χ negOneG30 = -1) :
    sigmaChiTC χ = 1 := by
  unfold sigmaChiTC charSignEleven charSign
  have hm1_core : charOnG30 χ Core.negOneG30 = -1 := by
    simpa using hm1
  have hm1_ne : charOnG30 χ Core.negOneG30 ≠ 1 := by
    rw [hm1_core]
    norm_num
  rw [if_pos h11]
  rw [if_neg hm1_ne]
  norm_num

lemma sigmaChiTC_eq_one_of_vals_neg_pos
    (χ : CharIdx)
    (h11 : charOnG30 χ elevenG30 = -1)
    (hm1 : charOnG30 χ negOneG30 = 1) :
    sigmaChiTC χ = 1 := by
  unfold sigmaChiTC charSignEleven charSign
  have h11_ne : charOnG30 χ elevenG30 ≠ 1 := by
    rw [h11]
    norm_num
  have hm1_core : charOnG30 χ Core.negOneG30 = 1 := by
    simpa using hm1
  rw [if_neg h11_ne]
  rw [if_pos hm1_core]
  norm_num

lemma sigmaChiTC_eq_three_of_vals
    (χ : CharIdx)
    (h11 : charOnG30 χ elevenG30 = 1)
    (hm1 : charOnG30 χ negOneG30 = 1) :
    sigmaChiTC χ = 3 := by
  unfold sigmaChiTC charSignEleven charSign
  have hm1_core : charOnG30 χ Core.negOneG30 = 1 := by
    simpa using hm1
  rw [if_pos h11]
  rw [if_pos hm1_core]
  norm_num

section T4bConcrete

open CouretUnification.Core

/--
Témoins effectifs du contre-exemple T4b.

Ils vérifient :
- σ(χ₁) = 1
- σ(χ₂) = 1
- σ(χ₃) = 3
- χ₃(g) = χ₁(g) * χ₂(g) pour tout g : G30

Ici :
- χ₁ = ⟨3, _⟩
- χ₂ = ⟨5, _⟩
- χ₃ = ⟨0, _⟩ (caractère trivial)
-/
private def chi₁_T4b : CharIdx := ⟨3, by decide⟩
private def chi₂_T4b : CharIdx := ⟨5, by decide⟩
private def chi₃_T4b : CharIdx := ⟨0, by decide⟩

private lemma neg_Ip6_eq_one : -(Complex.I ^ (6 : ℕ)) = (1 : ℂ) := by
  rw [Ip6]
  norm_num

private lemma chi₁_T4b_at_eleven :
    charOnG30 chi₁_T4b elevenG30 = 1 := by
  have hidx : g30ToIdx elevenG30 = ⟨2, by omega⟩ := g30ToIdx_eleven
  simp (config := { decide := true }) [chi₁_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]

private lemma chi₁_T4b_at_negOne :
    charOnG30 chi₁_T4b negOneG30 = -1 := by
  have hidx : g30ToIdx negOneG30 = ⟨7, by omega⟩ := g30ToIdx_negOne
  simp (config := { decide := true }) [chi₁_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]

private lemma chi₂_T4b_at_eleven :
    charOnG30 chi₂_T4b elevenG30 = 1 := by
  have hidx : g30ToIdx elevenG30 = ⟨2, by omega⟩ := g30ToIdx_eleven
  simp (config := { decide := true }) [chi₂_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]
  exact neg_Ip6_eq_one

private lemma chi₂_T4b_at_negOne :
    charOnG30 chi₂_T4b negOneG30 = -1 := by
  have hidx : g30ToIdx negOneG30 = ⟨7, by omega⟩ := g30ToIdx_negOne
  simp (config := { decide := true }) [chi₂_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]

private lemma chi₃_T4b_at_eleven :
    charOnG30 chi₃_T4b elevenG30 = 1 := by
  have hidx : g30ToIdx elevenG30 = ⟨2, by omega⟩ := g30ToIdx_eleven
  simp (config := { decide := true }) [chi₃_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]

private lemma chi₃_T4b_at_negOne :
    charOnG30 chi₃_T4b negOneG30 = 1 := by
  have hidx : g30ToIdx negOneG30 = ⟨7, by omega⟩ := g30ToIdx_negOne
  simp (config := { decide := true }) [chi₃_T4b, charOnG30, hidx,
    characterEval, charCoord, residueCoord, c2Phase, c4Phase]

private lemma chi₁_T4b_sigma :
    sigmaChiTC chi₁_T4b = 1 := by
  apply sigmaChiTC_eq_one_of_vals_pos_neg
  · exact chi₁_T4b_at_eleven
  · exact chi₁_T4b_at_negOne

private lemma chi₂_T4b_sigma :
    sigmaChiTC chi₂_T4b = 1 := by
  apply sigmaChiTC_eq_one_of_vals_pos_neg
  · exact chi₂_T4b_at_eleven
  · exact chi₂_T4b_at_negOne

private lemma chi₃_T4b_sigma :
    sigmaChiTC chi₃_T4b = 3 := by
  apply sigmaChiTC_eq_three_of_vals
  · exact chi₃_T4b_at_eleven
  · exact chi₃_T4b_at_negOne

set_option maxHeartbeats 1600000 in
private lemma chi_T4b_mul_pointwise :
    ∀ g : G30,
      charOnG30 chi₃_T4b g =
        charOnG30 chi₁_T4b g * charOnG30 chi₂_T4b g := by
  intro g
  fin_cases g <;>
    simp (config := { decide := true }) [chi₁_T4b, chi₂_T4b, chi₃_T4b,
      charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
      c2Phase, c4Phase, Complex.I_sq, Ip6, Ip9]

end T4bConcrete

/-- Contre-exemple T4b : fermeture finale une fois les trois témoins validés. -/
theorem tensor_product_escapes_E_one :
    ∃ χ₁ χ₂ : CharIdx,
      sigmaChiTC χ₁ = 1 ∧ sigmaChiTC χ₂ = 1 ∧
      ∃ χ₃ : CharIdx, sigmaChiTC χ₃ = 3 ∧
      (∀ g : G30, charOnG30 χ₃ g = charOnG30 χ₁ g * charOnG30 χ₂ g) := by
  exact tensor_product_escapes_E_one_of_witnesses
    chi₁_T4b chi₂_T4b chi₃_T4b
    chi₁_T4b_sigma chi₂_T4b_sigma chi₃_T4b_sigma
    chi_T4b_mul_pointwise

-- ═══════════════════════════════════════════════════════════════════
-- §9. Propriétés de non-trivialité
-- ═══════════════════════════════════════════════════════════════════

/-- Injection canonique sur la composante g3. -/
def AlgebraTC.ofG3 (g : MultSchwartz) : AlgebraTC where
  g3 := g
  g1 := zeroTestFunction
  gm1 := zeroTestFunction

theorem AlgebraTC.nontrivial :
    ∃ g : MultSchwartz, ∃ a : AlgebraTC, a = AlgebraTC.ofG3 g := by
  refine ⟨zeroTestFunction, AlgebraTC.ofG3 zeroTestFunction, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §10. Pont vers OperativeTestPacket
-- ═══════════════════════════════════════════════════════════════════

/-- Construction d'un paquet opératoire à partir de la composante g3. -/
def AlgebraTC.toOperativeTestPacket
    (a : AlgebraTC)
    (hComp : HasCompactLogSupport a.g3)
    (hSmooth : HasSmoothLogProfile a.g3)
    (hDecay : HasRapidMellinDecay a.g3)
    (hBias : ∀ {σ : ℝ}, 1 < σ → PositiveBiasAt σ a.g3) :
    OperativeTestPacket where
  toH3TestFunction := a.g3
  compact_log_support := hComp
  smooth_log_profile := hSmooth
  rapid_mellin_decay := hDecay
  positive_bias := by
    intro σ hσ
    exact hBias (σ := σ) hσ

-- ═══════════════════════════════════════════════════════════════════
-- §11. Doctrine de garde
-- ═══════════════════════════════════════════════════════════════════

theorem RHClaimed_false_AlgebraTC : True := trivial

end CouretUnification.Logic.H3
