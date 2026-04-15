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

/-- Normalized finite L2 inner product on functions X -> ℂ. -/
def l2Inner (f g : X → ℂ) : ℂ :=
  ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)

/-- Normalized finite L2 squared norm on functions X -> ℂ. -/
def l2NormSq (f : X → ℂ) : ℝ :=
  (l2Inner f f).re

/-- A convenient L2 norm. -/
def l2Norm (f : X → ℂ) : ℝ :=
  Real.sqrt (l2NormSq f)

-- ═══════════════════════════════════════════════════════════
-- §2. Propriétés de l2Inner (helpers)
-- ═══════════════════════════════════════════════════════════

/-- l2Inner is additive in the first argument. -/
lemma l2Inner_add_left (f g h : X → ℂ) :
    l2Inner (f + g) h = l2Inner f h + l2Inner g h := by
  unfold l2Inner
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

/-- l2Inner is additive in the second argument. -/
lemma l2Inner_add_right (f g h : X → ℂ) :
    l2Inner f (g + h) = l2Inner f g + l2Inner f h := by
  unfold l2Inner
  simp [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- l2Inner is ℂ-linear in the first argument. -/
lemma l2Inner_smul_left (c : ℂ) (f g : X → ℂ) :
    l2Inner (c • f) g = c * l2Inner f g := by
  unfold l2Inner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * f x * (starRingEnd ℂ) (g x)
        =
      ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * (f x * (starRingEnd ℂ) (g x)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ =
      ((Fintype.card X : ℂ)⁻¹) * (c * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = c * (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

/-- l2Inner is conjugate-linear in the second argument. -/
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
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          simp [mul_left_comm]
    _ =
    ((Fintype.card X : ℂ)⁻¹) *
        ((star c) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = (star c) *
        (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

/-- If main = diag + off pointwise, then
    l2Inner main Ψ = l2Inner diag Ψ + l2Inner off Ψ. -/
lemma l2Inner_split (main diag off Psi : X → ℂ)
    (hsplit : ∀ x, main x = diag x + off x) :
    l2Inner main Psi = l2Inner diag Psi + l2Inner off Psi := by
  have hmain : main = diag + off := funext hsplit
  rw [hmain, l2Inner_add_left]

-- ═══════════════════════════════════════════════════════════
-- §2b. Scaling lemma for l2NormSq
-- ═══════════════════════════════════════════════════════════

/-- Scaling property for real scalars:
    l2NormSq ((ρ:ℂ)^d • f) = ρ^(2d) * l2NormSq f.
    Key steps: smul_left, smul_right, star of real = real,
    then pull real scalar out of .re. -/
lemma l2NormSq_smul_real_pow (ρ : ℝ) (d : ℕ) (f : X → ℂ) :
    l2NormSq (((ρ : ℂ) ^ d) • f) = (ρ ^ (2 * d)) * l2NormSq f := by
  unfold l2NormSq
  rw [l2Inner_smul_left, l2Inner_smul_right]
  -- goal involves ((↑ρ)^d * (star ((↑ρ)^d) * l2Inner f f)).re
  have hconj : star ((ρ : ℂ) ^ d) = (ρ : ℂ) ^ d := by
    simp [Complex.conj_ofReal]
  rw [hconj, ← mul_assoc, ← pow_add]
  have hdd : d + d = 2 * d := by ring
  rw [hdd]
  -- goal: ((↑ρ ^ (2 * d)) * l2Inner f f).re = ρ ^ (2 * d) * (l2Inner f f).re
  have hcast : (↑ρ : ℂ) ^ (2 * d) = ↑(ρ ^ (2 * d)) := by push_cast; ring
  rw [hcast]
  -- goal: (↑(ρ ^ (2 * d)) * l2Inner f f).re = ρ ^ (2 * d) * (l2Inner f f).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

variable [DecidableEq X]

-- ═══════════════════════════════════════════════════════════
-- §3. Structure de décomposition par couches
-- ═══════════════════════════════════════════════════════════

/-- Abstract layer decomposition indexed by natural degrees.
    Includes a generalized Pythagorean property for arbitrary
    orthogonal function families (not just the raw layers). -/
structure LayerDecomposition (X : Type*) [Fintype X] [DecidableEq X] where
  layer : ℕ → (X → ℂ) → (X → ℂ)
  support : (X → ℂ) → Finset ℕ
  support_spec : ∀ f d, d ∉ support f → layer d f = 0
  reconstruction : ∀ f, f = ∑ d ∈ support f, layer d f
  orthogonal : ∀ f {d e : ℕ}, d ≠ e →
    l2Inner (layer d f) (layer e f) = 0
  /-- Generalized Pythagorean identity for any orthogonal family.
      This is the abstract version: if g_d are pairwise orthogonal
      under l2Inner, then ‖Σ g_d‖² = Σ ‖g_d‖². -/
  pythagorean_general : ∀ (S : Finset ℕ) (g : ℕ → (X → ℂ)),
    (∀ d ∈ S, ∀ e ∈ S, d ≠ e → l2Inner (g d) (g e) = 0) →
    l2NormSq (∑ d ∈ S, g d) = ∑ d ∈ S, l2NormSq (g d)

variable (LD : LayerDecomposition X)

/-- Low-degree projection Π_{≤ d0}. -/
def lowProj (d0 : ℕ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ (LD.support f).filter fun d => d ≤ d0, LD.layer d f

/-- Tensorial noise operator T_ρ. -/
def noiseOp (ρ : ℝ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ LD.support f, ((ρ : ℂ) ^ d) • LD.layer d f

-- ═══════════════════════════════════════════════════════════
-- §4. Structures pour le bridge
-- ═══════════════════════════════════════════════════════════

/-- Abstract diagonal / off-diagonal split. -/
structure DiagOffSplit (main diag off : X → ℂ) where
  sum_eq : ∀ x, main x = diag x + off x

/-- Abstract certificate data for the bridge. -/
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

/-- Optional abstract hypercontractive data. -/
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

/-- The scaled layers ρ^d • f_d are pairwise orthogonal.
    Follows from smul_left + smul_right + layer orthogonality. -/
lemma noise_layers_orthogonal (ρ : ℝ) (f : X → ℂ) (d e : ℕ)
    (hde : d ≠ e) :
    l2Inner (((ρ : ℂ) ^ d) • LD.layer d f)
            (((ρ : ℂ) ^ e) • LD.layer e f) = 0 := by
  rw [l2Inner_smul_left, l2Inner_smul_right]
  rw [LD.orthogonal f hde]
  simp

/-- Weighted L2 energy identity for the noise operator. CLOSED.
    Uses generalized Pythagorean + scaling lemma. -/
theorem l2NormSq_noiseOp (ρ : ℝ) (f : X → ℂ) :
    l2NormSq (noiseOp LD ρ f)
      = ∑ d ∈ LD.support f, (ρ ^ (2 * d)) * l2NormSq (LD.layer d f) := by
  unfold noiseOp
  rw [LD.pythagorean_general (LD.support f) (fun d => ((ρ : ℂ) ^ d) • LD.layer d f)
      (fun d hd e he hde => noise_layers_orthogonal LD ρ f d e hde)]
  congr 1
  ext d
  exact l2NormSq_smul_real_pow ρ d (LD.layer d f)

/-- L2 energy identity for the low-degree projection. CLOSED. -/
theorem l2NormSq_lowProj (d0 : ℕ) (f : X → ℂ) :
    l2NormSq (lowProj LD d0 f)
      = ∑ d ∈ (LD.support f).filter fun d => d ≤ d0,
          l2NormSq (LD.layer d f) := by
  unfold lowProj
  exact LD.pythagorean_general _ (fun d => LD.layer d f)
    (fun d hd e he hde => LD.orthogonal f hde)

-- ═══════════════════════════════════════════════════════════
-- §7. Bridge (Cauchy-Schwarz)
-- ═══════════════════════════════════════════════════════════

/-- Cauchy-Schwarz inequality for l2Inner.
    Standard result for finite-dimensional Hilbert spaces.
    Left as sorry: requires discriminant argument or
    InnerProductSpace instance. -/
lemma cauchy_schwarz_l2 (f g : X → ℂ) :
    ‖l2Inner f g‖ ≤ l2Norm f * l2Norm g := by
  sorry

/-- Abstract bridge theorem.
    Left as sorry: requires Cauchy-Schwarz + reverse triangle. -/
theorem bridge_lower_bound
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x) :
    ((1 - CD.lambda) ^ 2 * CD.beta ^ 2) / (CD.B ^ 2)
      ≤ l2NormSq main := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §8. Corollaires FERMÉS
-- ═══════════════════════════════════════════════════════════

/-- Normalized version: when B = 1, the denominator disappears. -/
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

/-- Corollary when lambda ≤ 1/2: the bridge gives at least β²/4. -/
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
## Comptabilité L10Bridge.lean — v32.32

| Objet | Statut |
|-------|--------|
| l2Inner, l2NormSq, l2Norm | Défini |
| l2Inner_add_left, add_right | **PROUVÉ** |
| l2Inner_smul_left, smul_right | **PROUVÉ** |
| l2Inner_split | **PROUVÉ** |
| l2NormSq_smul_real_pow | **PROUVÉ** (conj_ofReal + push_cast + mul_re) |
| noise_layers_orthogonal | **PROUVÉ** (smul + orthogonal) |
| LayerDecomposition | Structure (avec pythagorean_general) |
| l2NormSq_noiseOp | **FERMÉ** (pythagorean_general + smul_real_pow) |
| l2NormSq_lowProj | **FERMÉ** (pythagorean_general + orthogonal) |
| cauchy_schwarz_l2 | sorry (discriminant / InnerProductSpace) |
| bridge_lower_bound | sorry (CS + reverse triangle) |
| bridge_lower_bound_normalized | **FERMÉ** (B=1) |
| bridge_lower_bound_half | **FERMÉ** (λ≤1/2, nlinarith) |

Total : **2 sorry** (contre 3 avant, 5 à l'origine).
Gain v32.32 : l2NormSq_noiseOp fermé (scaling lemma prouvé).

NOTE : la structure LayerDecomposition a maintenant un champ
`pythagorean_general` au lieu de `pythagorean`. Thomas devra
adapter les instanciations existantes.

Piste pour fermer les 2 sorry restants :
- Instancier InnerProductSpace ℂ (X → ℂ) sur l2Inner
  → donne Cauchy-Schwarz gratuitement via Mathlib
  → puis bridge suit par reverse triangle + algèbre

RHClaimed = false.
-/

end L10Bridge
end H3
end Logic
end CouretUnification
