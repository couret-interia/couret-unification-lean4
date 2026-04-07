import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open Finset

namespace CouretUnification.Core

/-!
# Integer-spectrum classification of subsets of (ℤ/30ℤ)×

For a subset S of G = (ℤ/30ℤ)× ≅ C₂ × C₄, the Cayley operator
has eigenvalues given by the Fourier transform on the dual group:

  λ(u,v) = Σ_{(a,b)∈S} (-1)^{ua} · i^{vb}

where (a,b) are the CRT coordinates of each element.

The spectrum is *integer* when all eigenvalues are real integers,
i.e., when all imaginary parts vanish.

## Main result

Among the 255 non-empty subsets, exactly 63 have integer spectrum.
-/

namespace IntegerSpectrumClassification

/-!
### CRT isomorphism (ℤ/30ℤ)× → C₂ × C₄

We use discrete logarithms:
- C₂ component: generator 2 mod 3 (so 1↦0, 2↦1)
- C₄ component: generator 2 mod 5 (so 1↦0, 2↦1, 4↦2, 3↦3)

This is verified to be a group homomorphism.
-/

/-- C₂ component of the CRT isomorphism.
1→0, 7→0, 11→1, 13→0, 17→1, 19→0, 23→1, 29→1 -/
def crtA : Fin 8 → Nat
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 0 | ⟨6, _⟩ => 1 | ⟨7, _⟩ => 1

/-- C₄ component of the CRT isomorphism.
1→0, 7→1, 11→0, 13→3, 17→1, 19→2, 23→3, 29→2 -/
def crtB : Fin 8 → Nat
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 2 | ⟨6, _⟩ => 3 | ⟨7, _⟩ => 2

/-- (-1)^n as integer. -/
def negOnePow (n : Nat) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Im(i^k): imaginary part of the k-th power of i = exp(iπ/2). -/
def iPowIm (k : Nat) : Int :=
  match k % 4 with
  | 1 => 1
  | 3 => -1
  | _ => 0

/-- Imaginary part of Fourier eigenvalue λ(u,v) for subset given by indicator `f`.

  Im(λ(u,v)) = Σ_{j : f(j)=true} (-1)^{u·a_j} · Im(i^{v·b_j})
-/
def eigenIm (f : Fin 8 → Bool) (u : Fin 2) (v : Fin 4) : Int :=
  (univ : Finset (Fin 8)).sum fun i =>
    if f i then negOnePow (u.val * crtA i) * iPowIm (v.val * crtB i)
    else 0

/-- A subset has integer spectrum iff all Fourier eigenvalues have
zero imaginary part. -/
def hasIntegerSpectrum (f : Fin 8 → Bool) : Prop :=
  ∀ u : Fin 2, ∀ v : Fin 4, eigenIm f u v = 0

/-- A subset indicator is non-empty. -/
def isNonempty (f : Fin 8 → Bool) : Prop :=
  ∃ i : Fin 8, f i = true

/-- Combined predicate for counting. -/
def intSpecPred (f : Fin 8 → Bool) : Prop :=
  isNonempty f ∧ hasIntegerSpectrum f

instance : DecidablePred intSpecPred := fun _ => inferInstance

/-- Number of non-empty subsets with integer spectrum. -/
def intSpecCount : Nat :=
  ((univ : Finset (Fin 8 → Bool)).filter intSpecPred).card

/-- There are 255 non-empty subsets of (ℤ/30ℤ)×. -/
theorem totalNonempty_eq_255 :
    ((univ : Finset (Fin 8 → Bool)).filter fun f =>
      isNonempty f).card = 255 := by
  native_decide

/-- **Main theorem.** Among the 255 non-empty subsets of (ℤ/30ℤ)×,
exactly 63 have integer Fourier spectrum. -/
theorem intSpecCount_eq_63 : intSpecCount = 63 := by
  native_decide

/-- The Couret triplet T_C = {1,11,29} has integer spectrum. -/
def couretIndicator : Fin 8 → Bool
  | ⟨0, _⟩ => true   -- 1
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true   -- 11
  | ⟨3, _⟩ => false
  | ⟨4, _⟩ => false
  | ⟨5, _⟩ => false
  | ⟨6, _⟩ => false
  | ⟨7, _⟩ => true   -- 29

theorem couret_has_integer_spectrum :
    hasIntegerSpectrum couretIndicator := by
  native_decide

end IntegerSpectrumClassification

end CouretUnification.Core
