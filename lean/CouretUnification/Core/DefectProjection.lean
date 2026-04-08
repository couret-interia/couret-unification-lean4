import CouretUnification.Core.Classification63
import Mathlib.Tactic

namespace CouretUnification.Core
namespace DefectProjection

/-!
# Projection du défaut δ₁₉ − δ₂₉

The class 19 is a "C₄ phantom": 𝟙_TC(19) = 0 even though 19 ∈ (ℤ/30ℤ)×.
The defect δ₁₉ − δ₂₉ measures the Fourier difference between 19 and 29.

## CRT convention (Lean code, from Characters30.lean)

  19 ↦ (ε=0, k=2),  29 ↦ (ε=1, k=0)

where (ε, k) ∈ C₂ × C₄ with the documentary identification from Mod30.

⚠ NOTE: channel_bridge.py uses a DIFFERENT CRT convention
(generators 11, 7 instead of the documentary identification):
  19 ↦ (0, 2),  29 ↦ (1, 2)  [channel_bridge convention]
  19 ↦ (0, 2),  29 ↦ (1, 0)  [Lean/Characters30 convention]

Both are valid isomorphisms G₃₀ ≅ C₂ × C₄. The mathematical
content is identical; only the labeling of C₄ coordinates differs.

## Result (Lean convention)

  χ_{u,b}(19) = (−1)^b,   χ_{u,b}(29) = (−1)^u

Therefore:
  defect(χ_{u,b}) = (−1)^b − (−1)^u

The defect vanishes iff u ≡ b (mod 2), i.e., on exactly 4 of the 8
characters. The other 4 carry the entire rupture, with coefficient ±2.
-/

open Classification63

-- ═══════════════════════════════════════════
-- Masks for single-element subsets
-- ═══════════════════════════════════════════

/-- Index 5 = residue 19, mask = 2⁵ = 32. -/
def mask19 : Nat := 32
/-- Index 7 = residue 29, mask = 2⁷ = 128. -/
def mask29 : Nat := 128

-- Verify CRT coordinates
theorem crt_19 : crtCoord 5 = (0, 2) := by native_decide
theorem crt_29 : crtCoord 7 = (1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Fourier coefficients of δ₁₉ (single-element indicator)
-- ═══════════════════════════════════════════

theorem f19_ch0 : subsetFourier mask19 0 = (1, 0) := by native_decide
theorem f19_ch1 : subsetFourier mask19 1 = (-1, 0) := by native_decide
theorem f19_ch2 : subsetFourier mask19 2 = (-1, 0) := by native_decide
theorem f19_ch3 : subsetFourier mask19 3 = (-1, 0) := by native_decide
theorem f19_ch4 : subsetFourier mask19 4 = (1, 0) := by native_decide
theorem f19_ch5 : subsetFourier mask19 5 = (-1, 0) := by native_decide
theorem f19_ch6 : subsetFourier mask19 6 = (1, 0) := by native_decide
theorem f19_ch7 : subsetFourier mask19 7 = (1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Fourier coefficients of δ₂₉
-- ═══════════════════════════════════════════

theorem f29_ch0 : subsetFourier mask29 0 = (1, 0) := by native_decide
theorem f29_ch1 : subsetFourier mask29 1 = (1, 0) := by native_decide
theorem f29_ch2 : subsetFourier mask29 2 = (1, 0) := by native_decide
theorem f29_ch3 : subsetFourier mask29 3 = (-1, 0) := by native_decide
theorem f29_ch4 : subsetFourier mask29 4 = (1, 0) := by native_decide
theorem f29_ch5 : subsetFourier mask29 5 = (-1, 0) := by native_decide
theorem f29_ch6 : subsetFourier mask29 6 = (-1, 0) := by native_decide
theorem f29_ch7 : subsetFourier mask29 7 = (-1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Defect = F̂(δ₁₉) − F̂(δ₂₉)
-- ═══════════════════════════════════════════

/-- Defect Fourier coefficient: F̂(δ₁₉)(χ) − F̂(δ₂₉)(χ). -/
def defect (χ : Fin 8) : GI :=
  let f19 := subsetFourier mask19 χ
  let f29 := subsetFourier mask29 χ
  (f19.1 - f29.1, f19.2 - f29.2)

-- The 4 VANISHING channels (u ≡ b mod 2 in Lean convention)
theorem defect_ch0_zero : defect 0 = (0, 0) := by native_decide  -- (0,0): u=0,b=0
theorem defect_ch3_zero : defect 3 = (0, 0) := by native_decide  -- (1,1): u=1,b=1
theorem defect_ch4_zero : defect 4 = (0, 0) := by native_decide  -- (0,2): u=0,b=2
theorem defect_ch5_zero : defect 5 = (0, 0) := by native_decide  -- (1,3): u=1,b=3

-- The 4 NONZERO channels (u ≢ b mod 2 in Lean convention)
theorem defect_ch1_neg2 : defect 1 = (-2, 0) := by native_decide  -- (0,1): u=0,b=1
theorem defect_ch2_neg2 : defect 2 = (-2, 0) := by native_decide  -- (0,3): u=0,b=3
theorem defect_ch6_pos2 : defect 6 = (2, 0) := by native_decide   -- (1,0): u=1,b=0
theorem defect_ch7_pos2 : defect 7 = (2, 0) := by native_decide   -- (1,2): u=1,b=2

-- ═══════════════════════════════════════════
-- Structural properties
-- ═══════════════════════════════════════════

/-- The defect is real (imaginary part = 0 on all channels). -/
theorem defect_real : (List.finRange 8).all (fun χ => (defect χ).2 == 0) = true := by
  native_decide

/-- Exactly 4 channels carry the defect. -/
theorem defect_support_card :
    (List.finRange 8).countP (fun χ => defect χ != (0, 0)) = 4 := by
  native_decide

/-- The defect sums to zero over all characters (Parseval orthogonality). -/
theorem defect_sum_zero :
    (List.finRange 8).foldl (fun acc χ => gi_add acc (defect χ)) gi_zero
      = (0, 0) := by
  native_decide

/-- The defect squared norm: Σ|d_χ|² = 4·4 = 16. -/
def defectNormSq : Nat :=
  (List.finRange 8).foldl
    (fun acc χ => acc + ((defect χ).1 * (defect χ).1 + (defect χ).2 * (defect χ).2).natAbs) 0

theorem defect_norm_sq : defectNormSq = 16 := by native_decide

-- ═══════════════════════════════════════════
-- TC indicator vanishes at 19
-- ═══════════════════════════════════════════

/-- 𝟙_TC(19) = 0 : the Couret triplet does not contain 19. -/
theorem TC_vanishes_at_19 : bitSet couretMask 5 = false := by native_decide

/-- 𝟙_TC(29) = 1 : the Couret triplet contains 29. -/
theorem TC_contains_29 : bitSet couretMask 7 = true := by native_decide

/-- 19 and 29 are in different C₂ sectors. -/
theorem diff_C2 : (crtCoord 5).1 ≠ (crtCoord 7).1 := by native_decide

/-!
## Summary

In the Lean/Characters30 CRT convention:

| χ | dual (u,b) | F̂(δ₁₉) | F̂(δ₂₉) | Defect | u≡b? |
|---|-----------|---------|---------|--------|------|
| 0 | (0,0) | 1 | 1 | 0 | yes |
| 1 | (0,1) | −1 | 1 | −2 | no |
| 2 | (0,3) | −1 | 1 | −2 | no |
| 3 | (1,1) | −1 | −1 | 0 | yes |
| 4 | (0,2) | 1 | 1 | 0 | yes |
| 5 | (1,3) | −1 | −1 | 0 | yes |
| 6 | (1,0) | 1 | −1 | 2 | no |
| 7 | (1,2) | 1 | −1 | 2 | no |

The defect vanishes on exactly the 4 characters where u ≡ b (mod 2),
and equals ±2 on the other 4. The defect is entirely real.

**Formula** (Lean convention):
  defect(χ_{u,b}) = (−1)^b − (−1)^u

**Equivalence with channel_bridge.py**: the text uses generators (11, 7)
where 29 ↦ (1, 2). In that convention the defect lives on u=1 channels.
In the Lean convention (29 ↦ (1, 0)) it lives on the "parity-mismatch"
channels. Both are correct; only the C₄ generator labeling differs.
-/

end DefectProjection
end CouretUnification.Core