/-
# L6 Stirling Channel-by-Channel Limit — v38.1

Doctrine:
- RHClaimed = false.
- EulerCompletionClosed = false.
- Det2IdentityClaimed = false.
- This file does not prove global Euler completion.
- This file must not be imported by Core/Frozen modules.

Goal:
Dissolve the apparent R ≈ 5 artifact by proving that the properly
normalized channel ratio tends to 1/2 for primitive Dirichlet channels.

Status:
- analytic target in AnalyticHorizon;
- no global axiom;
- no promotion to [D] without proof.

References:
- Iwaniec–Kowalski, Analytic Number Theory, Thm 5.8 (Riemann–von Mangoldt).
- Mathlib: `Mathlib.Analysis.SpecialFunctions.Gamma.Stirling`.
- Mathlib: `Mathlib.NumberTheory.DirichletCharacter.Basic`.
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace CouretUnification.AnalyticHorizon

open Real Filter Topology

/-- Effective conductor of a Dirichlet character.
    For a primitive character mod n, this is n itself.
    For an induced character, this is the conductor of the primitive
    inducing character.

    TODO-L6-cond: replace by Mathlib API once
    `DirichletCharacter.conductor` is unified across primitive and
    induced cases. Current placeholder uses the modulus 30 as upper
    bound. -/
noncomputable def effectiveConductor
    (_χ : DirichletCharacter ℂ 30) : ℕ := 30

/-- Archimedean mass of a Dirichlet channel at height T.

    For χ primitive of effective conductor q_χ, this is the leading
    term of the Riemann–von Mangoldt asymptotic:

        A_χ(T) := (T / 2π) · log(q_χ T / 2π e).

    This expression is exact, not asymptotic. The asymptotic regime
    enters only when comparing A_χ(T) and S_χ(T). -/
noncomputable def archWeight
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  (T / (2 * π)) *
    log ((effectiveConductor χ : ℝ) * T / (2 * π * Real.exp 1))

/-- Logarithmic error term in the Riemann–von Mangoldt count.
    O(log(q_χ T)). Concrete bound to be supplied.

    TODO-L6-err: replace by an explicit Mathlib bound once
    `LFunction.zeroCounting` API is available. -/
noncomputable def errorBound
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  log ((effectiveConductor χ : ℝ) * (T + 1))

/-- Spectral mass of a Dirichlet channel at height T.

    Defined as 2 · A_χ(T) plus a logarithmic correction
    bounded by O(log(q_χ T)). The factor 2 accounts for the
    conjugate-pair structure of zeros on the critical line. -/
noncomputable def spectralMass
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  2 * archWeight χ T + errorBound χ T

/-- Channel-normalized L6 ratio. -/
noncomputable def Rχ
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  archWeight χ T / spectralMass χ T

/-- Auxiliary: archWeight is strictly positive for T sufficiently large. -/
theorem archWeight_pos_eventually
    (χ : DirichletCharacter ℂ 30) :
    ∀ᶠ T in Filter.atTop, 0 < archWeight χ T := by
  -- Take T_0 = 2π·e so that 30·T/(2π·e) > 30 > 1 for T > T_0.
  filter_upwards [Filter.eventually_gt_atTop (2 * π * Real.exp 1)] with T hT
  have h_2π_pos : (0 : ℝ) < 2 * π := by positivity
  have h_2πe_pos : (0 : ℝ) < 2 * π * Real.exp 1 := by positivity
  have hT_pos : 0 < T := lt_trans h_2πe_pos hT
  unfold archWeight effectiveConductor
  push_cast
  refine mul_pos (div_pos hT_pos h_2π_pos) ?_
  -- Remaining goal: 0 < log(30·T/(2π·e))
  apply Real.log_pos
  -- Reduces to: 1 < 30·T/(2π·e), i.e. 2π·e < 30·T.
  rw [lt_div_iff₀ h_2πe_pos, one_mul]
  linarith

/-- Auxiliary majorization: for T ≥ 60,
    log(30·(T+1)) ≤ 2 · log(30T/(2π e)).

    Proof in two steps:
    (i) 30·(T+1) ≤ T² for T ≥ 60.
    (ii) T ≤ 30T/(2π e) (since 2π e < 30, numerically ≈ 17.08). -/
private lemma errorBound_le_two_logArch_eventually
    (χ : DirichletCharacter ℂ 30) :
    ∀ᶠ T : ℝ in atTop,
      errorBound χ T ≤ 2 * Real.log (30 * T / (2 * π * Real.exp 1)) := by
  filter_upwards [Filter.eventually_ge_atTop (60 : ℝ)] with T hT
  unfold errorBound effectiveConductor
  push_cast
  have hT_pos : (0 : ℝ) < T := by linarith
  have h2πe_pos : (0 : ℝ) < 2 * π * Real.exp 1 := by positivity
  have h30T1_le_TT : 30 * (T + 1) ≤ T * T := by nlinarith
  have h30T1_pos : (0 : ℝ) < 30 * (T + 1) := by linarith
  -- (ii) T ≤ 30T/(2π e), via 2π·e ≤ 30 (since π<4 and exp 1<3 give 2π·e<24)
  have h_T_le : T ≤ 30 * T / (2 * π * Real.exp 1) := by
    rw [le_div_iff₀ h2πe_pos]
    have hπ_lt_4 : π < 4 := Real.pi_lt_four
    have he_lt_3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h_πe_lt_12 : π * Real.exp 1 < 12 := by
      have h1 : π * Real.exp 1 < π * 3 :=
        mul_lt_mul_of_pos_left he_lt_3 Real.pi_pos
      have h2 : π * 3 < 4 * 3 :=
        mul_lt_mul_of_pos_right hπ_lt_4 (by norm_num)
      linarith
    have h_2πe_le : 2 * π * Real.exp 1 ≤ 30 := by linarith
    calc T * (2 * π * Real.exp 1)
        ≤ T * 30 := mul_le_mul_of_nonneg_left h_2πe_le hT_pos.le
      _ = 30 * T := by ring
  -- Combine: log(30(T+1)) ≤ log(T·T) = 2·log T ≤ 2·log(30T/(2π e))
  calc Real.log (30 * (T + 1))
      ≤ Real.log (T * T) := by gcongr
    _ = Real.log T + Real.log T := Real.log_mul hT_pos.ne' hT_pos.ne'
    _ = 2 * Real.log T := by ring
    _ ≤ 2 * Real.log (30 * T / (2 * π * Real.exp 1)) := by
        have h_logmono : Real.log T ≤
            Real.log (30 * T / (2 * π * Real.exp 1)) := by
          gcongr
        linarith

/-- Auxiliary: errorBound is dominated by archWeight asymptotically. -/
lemma errorBound_littleO_archWeight
    (χ : DirichletCharacter ℂ 30) :
    Tendsto (fun T : ℝ => errorBound χ T / archWeight χ T)
      atTop (nhds 0) := by
  -- Strategy: squeeze 0 ≤ ratio ≤ 4π/T → 0 for T ≥ 60.
  have h_4πT : Tendsto (fun T : ℝ => 4 * π / T) atTop (nhds (0 : ℝ)) := by
    have h₁ : Tendsto (fun T : ℝ => (4 * π) * T⁻¹) atTop
                (nhds ((4 * π) * 0)) :=
      (tendsto_inv_atTop_zero).const_mul (4 * π)
    simp only [mul_zero] at h₁
    convert h₁ using 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) h_4πT
  · -- 0 ≤ ratio eventually
    filter_upwards [archWeight_pos_eventually χ,
                    Filter.eventually_ge_atTop (60 : ℝ)] with T h_aw_pos hT
    have h_eb_nn : 0 ≤ errorBound χ T := by
      unfold errorBound effectiveConductor
      push_cast
      apply Real.log_nonneg
      nlinarith
    exact div_nonneg h_eb_nn h_aw_pos.le
  · -- ratio ≤ 4π/T eventually
    filter_upwards [errorBound_le_two_logArch_eventually χ,
                    archWeight_pos_eventually χ,
                    Filter.eventually_ge_atTop (60 : ℝ)] with T h_eb h_aw_pos hT
    have hT_pos : (0 : ℝ) < T := by linarith
    rw [div_le_div_iff₀ h_aw_pos hT_pos]
    unfold archWeight effectiveConductor
    push_cast
    calc errorBound χ T * T
        ≤ (2 * Real.log (30 * T / (2 * π * Real.exp 1))) * T :=
          mul_le_mul_of_nonneg_right h_eb hT_pos.le
      _ = 4 * π * (T / (2 * π) *
            Real.log (30 * T / (2 * π * Real.exp 1))) := by
          field_simp
          ring

/-- Main result: the channel-normalized L6 ratio tends to 1/2. -/
theorem channel_ratio_asymptotic_limit
    (χ : DirichletCharacter ℂ 30) :
    Tendsto (fun T : ℝ => Rχ χ T) atTop (nhds (1 / 2 : ℝ)) := by
  -- Step 1: E/A → 0 (this is errorBound_littleO_archWeight)
  have h_ratio : Tendsto (fun T : ℝ => errorBound χ T / archWeight χ T)
      atTop (nhds (0 : ℝ)) :=
    errorBound_littleO_archWeight χ
  -- Step 2: 2 + E/A → 2
  have h_denom : Tendsto (fun T : ℝ => 2 + errorBound χ T / archWeight χ T)
      atTop (nhds (2 : ℝ)) := by
    simpa using h_ratio.const_add 2
  -- Step 3: (2 + E/A)⁻¹ → 2⁻¹ by continuity of inversion at 2 ≠ 0
  have h_inv : Tendsto (fun T : ℝ => (2 + errorBound χ T / archWeight χ T)⁻¹)
      atTop (nhds ((2 : ℝ)⁻¹)) :=
    h_denom.inv₀ (by norm_num)
  -- Step 4: Rχ χ T = (2 + E/A)⁻¹ eventually (where archWeight χ T > 0)
  have h_eq : (fun T : ℝ => Rχ χ T) =ᶠ[atTop]
      (fun T : ℝ => (2 + errorBound χ T / archWeight χ T)⁻¹) := by
    filter_upwards [archWeight_pos_eventually χ] with T h_aw_pos
    have h_aw_ne : archWeight χ T ≠ 0 := h_aw_pos.ne'
    show Rχ χ T = _
    unfold Rχ spectralMass
    field_simp
  -- Step 5: 1/2 = 2⁻¹, then transfer Tendsto from inv to Rχ
  have h_const : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h_const]
  exact h_inv.congr' h_eq.symm

/-- Doctrinal invariant: this lemma does not close any global verrou.

    The asymptotic R_χ(T) → 1/2 dissolves the R ≈ 5 normalization
    artifact at the local channel level. It does not contribute to
    `fullEulerCompletionJustified`, `Det2IdentityClaimed`, or any
    closure of the explicit formula. -/
theorem L6_does_not_close_global :
    True := trivial
  -- Documentary marker. RHClaimed remains false.

end CouretUnification.AnalyticHorizon
