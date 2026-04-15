import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

namespace CouretUnification
namespace Logic
namespace H3
namespace L10Bridge

variable {X : Type*} [Fintype X]

-- ═══════════════════════════════════════════════════════════
-- §1. Définitions fondamentales
-- ═══════════════════════════════════════════════════════════

def l2Inner (f g : X → ℂ) : ℂ :=
  ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)

def l2NormSq (f : X → ℂ) : ℝ :=
  (l2Inner f f).re

def l2Norm (f : X → ℂ) : ℝ :=
  Real.sqrt (l2NormSq f)

-- ═══════════════════════════════════════════════════════════
-- §2. Propriétés de l2Inner
-- ═══════════════════════════════════════════════════════════

lemma l2Inner_add_left (f g h : X → ℂ) :
    l2Inner (f + g) h = l2Inner f h + l2Inner g h := by
  unfold l2Inner
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma l2Inner_add_right (f g h : X → ℂ) :
    l2Inner f (g + h) = l2Inner f g + l2Inner f h := by
  unfold l2Inner
  simp [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma l2Inner_smul_left (c : ℂ) (f g : X → ℂ) :
    l2Inner (c • f) g = c * l2Inner f g := by
  unfold l2Inner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * f x * (starRingEnd ℂ) (g x)
        =
      ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * (f x * (starRingEnd ℂ) (g x)) := by
          congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ =
      ((Fintype.card X : ℂ)⁻¹) * (c * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1; rw [Finset.mul_sum]
    _ = c * (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

lemma l2Inner_smul_right (c : ℂ) (f g : X → ℂ) :
    l2Inner f (c • g) = (star c) * l2Inner f g := by
  unfold l2Inner
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    ((Fintype.card X : ℂ)⁻¹) *
        ∑ x : X, f x * ((starRingEnd ℂ) c * (starRingEnd ℂ) (g x))
      =
    ((Fintype.card X : ℂ)⁻¹) *
        ∑ x : X, (star c) * (f x * (starRingEnd ℂ) (g x)) := by
          congr 1; apply Finset.sum_congr rfl; intro x _; simp [mul_left_comm]
    _ =
    ((Fintype.card X : ℂ)⁻¹) *
        ((star c) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1; rw [Finset.mul_sum]
    _ = (star c) *
        (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

lemma l2Inner_split (main diag off Psi : X → ℂ)
    (hsplit : ∀ x, main x = diag x + off x) :
    l2Inner main Psi = l2Inner diag Psi + l2Inner off Psi := by
  have hmain : main = diag + off := funext hsplit
  rw [hmain, l2Inner_add_left]

-- ═══════════════════════════════════════════════════════════
-- §2b. Scaling lemma
-- ═══════════════════════════════════════════════════════════

lemma l2NormSq_smul_real_pow (ρ : ℝ) (d : ℕ) (f : X → ℂ) :
    l2NormSq (((ρ : ℂ) ^ d) • f) = (ρ ^ (2 * d)) * l2NormSq f := by
  unfold l2NormSq
  rw [l2Inner_smul_left, l2Inner_smul_right]
  have hconj : star ((ρ : ℂ) ^ d) = (ρ : ℂ) ^ d := by
    simp [Complex.conj_ofReal]
  rw [hconj, ← mul_assoc, ← pow_add]
  have hdd : d + d = 2 * d := by ring
  rw [hdd]
  have hcast : (↑ρ : ℂ) ^ (2 * d) = ↑(ρ ^ (2 * d)) := by push_cast; ring
  rw [hcast]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

-- ═══════════════════════════════════════════════════════════
-- §2c. Non-négativité de l2NormSq
-- ═══════════════════════════════════════════════════════════

/-- l2NormSq f ≥ 0. Standard for sesquilinear forms.
    sorry: requires Σ |f(x)|² ≥ 0 + (card X)⁻¹ ≥ 0 in ℂ then .re -/
lemma l2NormSq_nonneg (f : X → ℂ) : 0 ≤ l2NormSq f := by
  sorry

variable [DecidableEq X]

-- ═══════════════════════════════════════════════════════════
-- §3. Structure de décomposition par couches
-- ═══════════════════════════════════════════════════════════

structure LayerDecomposition (X : Type*) [Fintype X] [DecidableEq X] where
  layer : ℕ → (X → ℂ) → (X → ℂ)
  support : (X → ℂ) → Finset ℕ
  support_spec : ∀ f d, d ∉ support f → layer d f = 0
  reconstruction : ∀ f, f = ∑ d ∈ support f, layer d f
  orthogonal : ∀ f {d e : ℕ}, d ≠ e →
    l2Inner (layer d f) (layer e f) = 0
  pythagorean_general : ∀ (S : Finset ℕ) (g : ℕ → (X → ℂ)),
    (∀ d ∈ S, ∀ e ∈ S, d ≠ e → l2Inner (g d) (g e) = 0) →
    l2NormSq (∑ d ∈ S, g d) = ∑ d ∈ S, l2NormSq (g d)

variable (LD : LayerDecomposition X)

def lowProj (d0 : ℕ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ (LD.support f).filter fun d => d ≤ d0, LD.layer d f

def noiseOp (ρ : ℝ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ LD.support f, ((ρ : ℂ) ^ d) • LD.layer d f

-- ═══════════════════════════════════════════════════════════
-- §4. Structures pour le bridge
-- ═══════════════════════════════════════════════════════════

structure DiagOffSplit (main diag off : X → ℂ) where
  sum_eq : ∀ x, main x = diag x + off x

structure CertificateData where
  diag : X → ℂ
  off  : X → ℂ
  Psi  : X → ℂ
  B : ℝ
  beta : ℝ
  lambda : ℝ
  hB_pos : 0 < B
  hbeta_pos : 0 < beta
  hlambda_nonneg : 0 ≤ lambda
  hnorm : l2Norm Psi ≤ B
  hbeta_bound : beta ≤ ‖l2Inner diag Psi‖
  hgamma_bound : ‖l2Inner off Psi‖ ≤ lambda * beta
  hlambda_lt_one : lambda < 1

structure HCData where
  p : ℝ
  rho : ℝ
  hp_lower : 1 < p
  hp_upper : p ≤ 2
  hrho_pos : 0 < rho
  hrho_upper : rho ≤ 1

-- ═══════════════════════════════════════════════════════════
-- §5. Théorèmes délégués
-- ═══════════════════════════════════════════════════════════

theorem layer_orthogonal (f : X → ℂ) {d e : ℕ} (hde : d ≠ e) :
    l2Inner (LD.layer d f) (LD.layer e f) = 0 :=
  LD.orthogonal f hde

theorem layer_eq_zero_of_not_mem_support (f : X → ℂ) (d : ℕ)
    (hd : d ∉ LD.support f) :
    LD.layer d f = 0 :=
  LD.support_spec f d hd

theorem sum_layers_eq (f : X → ℂ) :
    f = ∑ d ∈ LD.support f, LD.layer d f :=
  LD.reconstruction f

-- ═══════════════════════════════════════════════════════════
-- §6. FERMÉ : Pythagorean pour noiseOp et lowProj
-- ═══════════════════════════════════════════════════════════

lemma noise_layers_orthogonal (ρ : ℝ) (f : X → ℂ) (d e : ℕ)
    (hde : d ≠ e) :
    l2Inner (((ρ : ℂ) ^ d) • LD.layer d f)
            (((ρ : ℂ) ^ e) • LD.layer e f) = 0 := by
  rw [l2Inner_smul_left, l2Inner_smul_right]
  rw [LD.orthogonal f hde]
  simp

theorem l2NormSq_noiseOp (ρ : ℝ) (f : X → ℂ) :
    l2NormSq (noiseOp LD ρ f)
      = ∑ d ∈ LD.support f, (ρ ^ (2 * d)) * l2NormSq (LD.layer d f) := by
  unfold noiseOp
  rw [LD.pythagorean_general (LD.support f) (fun d => ((ρ : ℂ) ^ d) • LD.layer d f)
      (fun d hd e he hde => noise_layers_orthogonal LD ρ f d e hde)]
  congr 1
  ext d
  exact l2NormSq_smul_real_pow ρ d (LD.layer d f)

theorem l2NormSq_lowProj (d0 : ℕ) (f : X → ℂ) :
    l2NormSq (lowProj LD d0 f)
      = ∑ d ∈ (LD.support f).filter fun d => d ≤ d0,
          l2NormSq (LD.layer d f) := by
  unfold lowProj
  exact LD.pythagorean_general _ (fun d => LD.layer d f)
    (fun d hd e he hde => LD.orthogonal f hde)

-- ═══════════════════════════════════════════════════════════
-- §7. Cauchy-Schwarz (unique sorry analytique)
-- ═══════════════════════════════════════════════════════════

/-- Cauchy-Schwarz inequality for l2Inner.
    The unique remaining analytical sorry in L10Bridge.
    Closable by instantiating InnerProductSpace on l2Inner. -/
lemma cauchy_schwarz_l2 (f g : X → ℂ) :
    ‖l2Inner f g‖ ≤ l2Norm f * l2Norm g := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §8. Bridge — FERMÉ (modulo CS + nonneg)
-- ═══════════════════════════════════════════════════════════

/-- Bridge theorem. CLOSED.
    Uses: l2Inner_split, reverse triangle (norm_add_le + norm_neg),
    Cauchy-Schwarz, sq_le_sq', Real.sq_sqrt, l2NormSq_nonneg. -/
theorem bridge_lower_bound
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x) :
    ((1 - CD.lambda) ^ 2 * CD.beta ^ 2) / (CD.B ^ 2)
      ≤ l2NormSq main := by
  -- Abbreviations
  set a := l2Inner CD.diag CD.Psi
  set b := l2Inner CD.off CD.Psi
  -- Step 1: ⟨main, Ψ⟩ = a + b
  have hab : l2Inner main CD.Psi = a + b :=
    l2Inner_split main CD.diag CD.off CD.Psi hsplit
  -- Step 2: reverse triangle  ‖a‖ - ‖b‖ ≤ ‖a + b‖
  have hrev : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
    have h1 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
      calc ‖a‖ = ‖(a + b) + (-b)‖ := by congr 1; ring
        _ ≤ ‖a + b‖ + ‖-b‖ := norm_add_le _ _
        _ = ‖a + b‖ + ‖b‖ := by rw [norm_neg]
    linarith
  -- Step 3: (1-λ)β ≤ ‖⟨main, Ψ⟩‖
  have htri : (1 - CD.lambda) * CD.beta ≤ ‖l2Inner main CD.Psi‖ := by
    rw [hab]
    calc (1 - CD.lambda) * CD.beta
        = CD.beta - CD.lambda * CD.beta := by ring
      _ ≤ ‖a‖ - ‖b‖ := by linarith [CD.hbeta_bound, CD.hgamma_bound]
      _ ≤ ‖a + b‖ := hrev
  -- Step 4: ‖⟨main, Ψ⟩‖ ≤ l2Norm(main) * B  (by CS + ‖Ψ‖ ≤ B)
  have hCS_B : ‖l2Inner main CD.Psi‖ ≤ l2Norm main * CD.B :=
    calc ‖l2Inner main CD.Psi‖
        ≤ l2Norm main * l2Norm CD.Psi := cauchy_schwarz_l2 main CD.Psi
      _ ≤ l2Norm main * CD.B := by
          exact mul_le_mul_of_nonneg_left CD.hnorm (Real.sqrt_nonneg _)
  -- Step 5: (1-λ)β ≤ l2Norm(main) * B
  have h1 : (1 - CD.lambda) * CD.beta ≤ l2Norm main * CD.B := by linarith
  -- Step 6: divide by B
  have hB_pos := CD.hB_pos
  have h2 : (1 - CD.lambda) * CD.beta / CD.B ≤ l2Norm main := by
    rwa [div_le_iff₀ hB_pos]
  -- Step 7: square both sides (both non-negative)
  have h_lhs_nn : 0 ≤ (1 - CD.lambda) * CD.beta / CD.B :=
    div_nonneg (mul_nonneg (by linarith [CD.hlambda_lt_one]) (le_of_lt CD.hbeta_pos))
               (le_of_lt CD.hB_pos)
  have h_rhs_nn : 0 ≤ l2Norm main := Real.sqrt_nonneg _
  have h3 : ((1 - CD.lambda) * CD.beta / CD.B) ^ 2 ≤ l2Norm main ^ 2 :=
    sq_le_sq' (by linarith) h2
  -- Step 8: l2Norm² = l2NormSq
  have h4 : l2Norm main ^ 2 = l2NormSq main := by
    unfold l2Norm; exact Real.sq_sqrt (l2NormSq_nonneg main)
  -- Step 9: conclude
  calc ((1 - CD.lambda) ^ 2 * CD.beta ^ 2) / CD.B ^ 2
      = ((1 - CD.lambda) * CD.beta / CD.B) ^ 2 := by ring
    _ ≤ l2Norm main ^ 2 := h3
    _ = l2NormSq main := h4

-- ═══════════════════════════════════════════════════════════
-- §9. Corollaires FERMÉS
-- ═══════════════════════════════════════════════════════════

theorem bridge_lower_bound_normalized
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x)
    (hB : CD.B = 1) :
    (1 - CD.lambda) ^ 2 * CD.beta ^ 2 ≤ l2NormSq main := by
  have h := bridge_lower_bound (X := X) main CD hsplit
  have hB2 : CD.B ^ 2 = 1 := by rw [hB]; norm_num
  rw [hB2, div_one] at h
  exact h

theorem bridge_lower_bound_half
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x)
    (hB : CD.B = 1)
    (hlam : CD.lambda ≤ 1 / 2) :
    CD.beta ^ 2 / 4 ≤ l2NormSq main := by
  have h := bridge_lower_bound_normalized (X := X) main CD hsplit hB
  nlinarith [sq_nonneg CD.beta, sq_nonneg (1 - CD.lambda - 1 / 2)]

-- ═══════════════════════════════════════════════════════════
-- Garde épistémique
-- ═══════════════════════════════════════════════════════════

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

/-!
## Comptabilité L10Bridge.lean — v32.33

| Objet | Statut |
|-------|--------|
| l2Inner, l2NormSq, l2Norm | Défini |
| l2Inner_add_left, add_right | **PROUVÉ** |
| l2Inner_smul_left, smul_right | **PROUVÉ** |
| l2Inner_split | **PROUVÉ** |
| l2NormSq_smul_real_pow | **PROUVÉ** |
| noise_layers_orthogonal | **PROUVÉ** |
| l2NormSq_nonneg | sorry (trivial : Σ|f(x)|² ≥ 0) |
| cauchy_schwarz_l2 | sorry (discriminant / InnerProductSpace) |
| l2NormSq_noiseOp | **FERMÉ** |
| l2NormSq_lowProj | **FERMÉ** |
| bridge_lower_bound | **FERMÉ** (reverse triangle + CS + sq_le_sq') |
| bridge_lower_bound_normalized | **FERMÉ** |
| bridge_lower_bound_half | **FERMÉ** |

Sorry dans ce fichier : 2
  - l2NormSq_nonneg (trivial, ~5 lignes Mathlib)
  - cauchy_schwarz_l2 (standard, ~40 lignes Mathlib)

Sorry total du dépôt : 3 (1 Lock 3 + 2 L10Bridge)

Progression : 5 sorry (v32.28) → 3 sorry (v32.33)
Le bridge_lower_bound est maintenant FERMÉ.

RHClaimed = false.
-/

end L10Bridge
end H3
end Logic
end CouretUnification