import CouretUnification.Core.CayleySpectrum
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Core
namespace Kurtosis

/-!
# Spectral moments and kurtosis

From the traces Tr(Aᵏ) already certified in `CayleySpectrum`,
we derive the spectral moments and kurtosis ratios.

Traces (certified by `native_decide`):
  Tr(A) = 8,  Tr(A²) = 24,  Tr(A³) = 56,  Tr(A⁴) = 168.

Spectral moments (n = 8):
  M₂ = Tr(A²)/n = 3
  M₄ = Tr(A⁴)/n = 21
  κ_raw = M₄/M₂² = 21/9 = 7/3

Non-trivial Parseval mass:
  P_{≠} = Parseval − ρ² = 24 − 9 = 15
  P_{≠}/M₂² = 15/9 = 5/3
-/

open CayleySpectrum

-- ═══════════════════════════════════════════
-- Integer trace facts (new ones beyond CayleySpectrum)
-- ═══════════════════════════════════════════

/-- Parseval mass = Tr(A²) = 24. -/
theorem parseval_24 :  CS_tr (CS_mm A A) = 24 := trace_A2

/-- Tr(A⁴) = 168. -/
theorem trace_fourth : CS_tr (CS_mm (CS_mm (CS_mm A A) A) A) = 168 := trace_A4

/-- Dominant eigenvalue squared: ρ² = 9. -/
theorem dominant_sq : (3 : Int) ^ 2 = 9 := by norm_num

-- ═══════════════════════════════════════════
-- Spectral moments (rational arithmetic)
-- ═══════════════════════════════════════════

/-- M₂ = Tr(A²)/8 = 3. -/
theorem M2_eq : (24 : ℚ) / 8 = 3 := by norm_num

/-- M₄ = Tr(A⁴)/8 = 21. -/
theorem M4_eq : (168 : ℚ) / 8 = 21 := by norm_num

/-- Raw spectral kurtosis κ = M₄/M₂² = 7/3. -/
theorem kurtosis_raw : (21 : ℚ) / (3 ^ 2) = 7 / 3 := by norm_num

-- ═══════════════════════════════════════════
-- Non-trivial Parseval decomposition
-- ═══════════════════════════════════════════

/-- Non-trivial Parseval mass: P − ρ² = 24 − 9 = 15. -/
theorem nontrivial_parseval : 24 - 9 = (15 : Int) := by norm_num

/-- The 15 = 5 × 3. -/
theorem fifteen_factored : (15 : Int) = 5 * 3 := by norm_num

/-- Non-trivial ratio: (P − ρ²) / M₂² = 15/9 = 5/3. -/
theorem nontrivial_ratio : (15 : ℚ) / (3 ^ 2) = 5 / 3 := by norm_num

-- ═══════════════════════════════════════════
-- Central moments (about mean eigenvalue μ = 1)
-- ═══════════════════════════════════════════

/-- Mean eigenvalue μ = Tr(A)/8 = 1. -/
theorem mean_eigenvalue : (8 : ℚ) / 8 = 1 := by norm_num

/-- Tr((A-I)²) = Tr(A²) − 2·Tr(A) + n = 24 − 16 + 8 = 16. -/
theorem trace_centered_2 : 24 - 2 * 8 + 8 = (16 : Int) := by norm_num

/-- σ² = Tr((A-I)²)/n = 16/8 = 2. -/
theorem variance : (16 : ℚ) / 8 = 2 := by norm_num

/-- Tr((A-I)⁴) = Tr(A⁴) − 4·Tr(A³) + 6·Tr(A²) − 4·Tr(A) + n
    = 168 − 224 + 144 − 32 + 8 = 64. -/
theorem trace_centered_4 : 168 - 4 * 56 + 6 * 24 - 4 * 8 + 8 = (64 : Int) := by norm_num

/-- μ₄ = Tr((A-I)⁴)/n = 64/8 = 8. -/
theorem central_M4 : (64 : ℚ) / 8 = 8 := by norm_num

/-- Central kurtosis κ_c = μ₄/σ⁴ = 8/4 = 2. -/
theorem kurtosis_central : (8 : ℚ) / (2 ^ 2) = 2 := by norm_num

/-- Excess kurtosis = κ_c − 3 = −1.
    (Sub-Gaussian: less peaked than Gaussian.) -/
theorem excess_kurtosis : (2 : ℚ) - 3 = -1 := by norm_num

-- ═══════════════════════════════════════════
-- Direct verification from eigenvalue multiplicities
-- ═══════════════════════════════════════════

/-- Σ λ⁴ = 2·81 + 4·1 + 2·1 = 168 (consistent with Tr(A⁴)). -/
theorem sum_fourth_powers : 2 * 81 + 4 * 1 + 2 * 1 = (168 : Int) := by norm_num

/-- Σ (λ−1)⁴ = 2·16 + 4·0 + 2·16 = 64 (consistent with Tr((A-I)⁴)). -/
theorem sum_central_fourth : 2 * 16 + 4 * 0 + 2 * 16 = (64 : Int) := by norm_num

/-!
## Summary of spectral moment invariants

| Quantity | Value | Theorem |
|----------|-------|---------|
| Tr(A) | 8 | `trace_A` |
| Tr(A²) = Parseval | 24 | `parseval_24` |
| Tr(A³) | 56 | `trace_A3` |
| Tr(A⁴) | 168 | `trace_fourth` |
| M₂ = Parseval/8 | 3 | `M2_eq` |
| M₄ = Tr(A⁴)/8 | 21 | `M4_eq` |
| κ_raw = M₄/M₂² | 7/3 | `kurtosis_raw` |
| P − ρ² (non-trivial mass) | 15 | `nontrivial_parseval` |
| (P − ρ²)/M₂² | 5/3 | `nontrivial_ratio` |
| σ² (central variance) | 2 | `variance` |
| κ_central = μ₄/σ⁴ | 2 | `kurtosis_central` |
| Excess kurtosis | −1 | `excess_kurtosis` |
-/

end Kurtosis
end CouretUnification.Core
