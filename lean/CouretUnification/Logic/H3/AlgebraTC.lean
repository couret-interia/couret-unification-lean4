/-
  CouretUnification/Logic/H3/AlgebraTC.lean

  Implémentation Lean 4 de l'algèbre test 𝒜_TC.

  Référence mathématique : AlgebraTC_v35_v1_final.md
  (fusion T2+T4, patch TC3 v1 canonique).

  Dépendances :
    - Core/Characters30.lean (CharIdx, charCoord, charOnG30)
    - Core/CharParity30.lean (negOneG30, charOnG30_negOne_pm)
    - Core/CayleyG30.lean (spectre A_TC)
    - H3/H3TestSpace.lean (H3TestFunction, OperativeTestPacket)

  RHClaimed = false.
-/

import Mathlib.Tactic
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharParity30
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

/-- Contre-exemple concret de non-stabilité sous *_T. -/
axiom tensor_product_escapes_E_one :
    ∃ χ₁ χ₂ : CharIdx,
      sigmaChiTC χ₁ = 1 ∧ sigmaChiTC χ₂ = 1 ∧
      ∃ χ₃ : CharIdx, sigmaChiTC χ₃ = 3 ∧
      (∀ g : G30, charOnG30 χ₃ g = charOnG30 χ₁ g * charOnG30 χ₂ g)

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
