import CouretUnification.Core.Characters30
import Mathlib.Tactic

namespace CouretUnification.Core
namespace Classification63

/-!
# Classification 63/255

Among the 2⁸ − 1 = 255 non-empty subsets of (ℤ/30ℤ)×,
exactly 63 have an all-integer Cayley spectrum.

The proof is by exhaustive decidable computation via `native_decide`.
-/

/-- Gaussian integer as (real part, imaginary part). -/
abbrev GI := Int × Int

@[inline] def gi_zero : GI := (0, 0)
@[inline] def gi_add (a b : GI) : GI := (a.1 + b.1, a.2 + b.2)

/-- i^n mod 4, returning (re, im). -/
@[inline] def gi_ipow (n : Nat) : GI :=
  match n % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)
  | _ => (1, 0)

/-- (-1)^n as Gaussian integer. -/
@[inline] def gi_signpow (n : Nat) : GI :=
  if n % 2 = 0 then (1, 0) else (-1, 0)

/-- Gaussian integer multiplication. -/
@[inline] def gi_mul (a b : GI) : GI :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/--
CRT coordinates (ε, k) ∈ C₂ × C₄ for the 8 units mod 30,
in the documentary order [1, 7, 11, 13, 17, 19, 23, 29].
-/
@[inline] def crtCoord : Fin 8 → Nat × Nat
  | ⟨0, _⟩ => (0, 0)  -- 1
  | ⟨1, _⟩ => (0, 1)  -- 7
  | ⟨2, _⟩ => (1, 2)  -- 11
  | ⟨3, _⟩ => (0, 3)  -- 13
  | ⟨4, _⟩ => (1, 3)  -- 17
  | ⟨5, _⟩ => (0, 2)  -- 19
  | ⟨6, _⟩ => (1, 1)  -- 23
  | ⟨7, _⟩ => (1, 0)  -- 29

/--
Character coordinates (u, b) ∈ Ĉ₂ × Ĉ₄ for the 8 dual characters,
in the documentary order.
-/
@[inline] def dualCoord : Fin 8 → Nat × Nat
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (0, 3)
  | ⟨3, _⟩ => (1, 1)
  | ⟨4, _⟩ => (0, 2)
  | ⟨5, _⟩ => (1, 3)
  | ⟨6, _⟩ => (1, 0)
  | ⟨7, _⟩ => (1, 2)

/--
Character χ_{u,b} evaluated at group element (ε,k):
  χ(g) = (−1)^{uε} · i^{bk}
as a Gaussian integer.
-/
@[inline] def giCharEval (χ g : Fin 8) : GI :=
  let (u, b) := dualCoord χ
  let (ε, k) := crtCoord g
  gi_mul (gi_signpow (u * ε)) (gi_ipow (b * k))

/-- Test if bit i is set in mask. -/
@[inline] def bitSet (mask : Nat) (i : Fin 8) : Bool :=
  (mask / (2 ^ i.1)) % 2 == 1

/-- Fourier coefficient of bitmask subset for character χ, as GI. -/
def subsetFourier (mask : Nat) (χ : Fin 8) : GI :=
  (List.finRange 8).foldl
    (fun acc g => if bitSet mask g then gi_add acc (giCharEval χ g) else acc)
    gi_zero

/-- Does the bitmask subset have all-integer Cayley spectrum? (Bool) -/
@[inline] def hasIntSpec (mask : Nat) : Bool :=
  (List.finRange 8).all fun χ => (subsetFourier mask χ).2 == 0

/-- Count of non-empty subsets (1..255) with all-integer spectrum. -/
def intSpecCount : Nat :=
  (List.range 255).countP fun k => hasIntSpec (k + 1)

/--
**Main theorem**: exactly 63 of the 255 non-empty subsets of (ℤ/30ℤ)×
have an all-integer Cayley spectrum.
-/
theorem classification_63_of_255 : intSpecCount = 63 := by
  native_decide

/-- The Couret triplet T_C = {1,11,29} has bitmask 2⁰ + 2² + 2⁷ = 133. -/
def couretMask : Nat := 1 + 4 + 128

theorem couretMask_eq : couretMask = 133 := by decide

/-- T_C is among the 63 integer-spectrum subsets. -/
theorem couret_has_integer_spectrum : hasIntSpec couretMask = true := by
  native_decide

/-- T_C has Fourier coefficients [3,1,1,1,3,1,−1,−1]. -/
theorem couret_fourier_0 : subsetFourier couretMask 0 = (3, 0) := by native_decide
theorem couret_fourier_1 : subsetFourier couretMask 1 = (1, 0) := by native_decide
theorem couret_fourier_2 : subsetFourier couretMask 2 = (1, 0) := by native_decide
theorem couret_fourier_3 : subsetFourier couretMask 3 = (1, 0) := by native_decide
theorem couret_fourier_4 : subsetFourier couretMask 4 = (3, 0) := by native_decide
theorem couret_fourier_5 : subsetFourier couretMask 5 = (1, 0) := by native_decide
theorem couret_fourier_6 : subsetFourier couretMask 6 = (-1, 0) := by native_decide
theorem couret_fourier_7 : subsetFourier couretMask 7 = (-1, 0) := by native_decide

/-- Parseval mass for T_C: Σ|F̂|² = 24. -/
def parsevalMass (mask : Nat) : Nat :=
  (List.finRange 8).foldl
    (fun acc χ =>
      let f := subsetFourier mask χ
      acc + (f.1 * f.1 + f.2 * f.2).natAbs)
    0

theorem couret_parseval : parsevalMass couretMask = 24 := by native_decide

/-- 63 = 2⁶ − 1, a Mersenne number. -/
theorem count_is_mersenne : intSpecCount = 2 ^ 6 - 1 := by native_decide

end Classification63
end CouretUnification.Core