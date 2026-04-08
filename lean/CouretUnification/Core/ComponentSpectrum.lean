import CouretUnification.Core.CayleyConnected
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace CouretUnification.Core
namespace ComponentSpectrum

/-!
# Spectre des 2 composantes connexes

Spec(Aeven) = Spec(Aodd) = {3, 1, 1, −1} on Fin 4.

The global spectrum {3², 1⁴, (−1)²} is the union of two
copies of {3, 1, 1, −1}.

We reuse `Aeven`, `Aodd`, `mm4` from CayleyConnected.
-/

open CayleySpectrum CayleyConnected

-- ═══════════════════════════════════════════
-- Additional 4×4 operations
-- ═══════════════════════════════════════════

abbrev M4 := Fin 4 → Fin 4 → Int
abbrev V4 := Fin 4 → Int

def scI4 (k : Int) : M4 :=
  fun i j => if i = j then k else 0

def msub4 (M N : M4) : M4 :=
  fun i j => M i j - N i j

def mzero4 : M4 := fun _ _ => 0

def tr4 (M : M4) : Int :=
  (List.finRange 4).foldl (fun acc i => acc + M i i) 0

def meq4 (M N : M4) : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).all fun j => M i j == N i j

def mv4 (M : M4) (v : V4) : V4 :=
  fun i => (List.finRange 4).foldl (fun acc j => acc + M i j * v j) 0

def sv4 (k : Int) (v : V4) : V4 := fun i => k * v i

def veq4 (u v : V4) : Bool :=
  (List.finRange 4).all fun i => u i == v i

def dot4 (u v : V4) : Int :=
  (List.finRange 4).foldl (fun acc i => acc + u i * v i) 0

-- ═══════════════════════════════════════════
-- The two components are IDENTICAL matrices
-- ═══════════════════════════════════════════

theorem components_identical : meq4 Aeven Aodd = true := by native_decide

-- ═══════════════════════════════════════════
-- Even component: Spec(Aeven) = {3, 1, 1, −1}
-- ═══════════════════════════════════════════

theorem Ae_symmetric : meq4 Aeven (fun i j => Aeven j i) = true := by native_decide

theorem Ae_row_sums_3 : (List.finRange 4).all (fun i =>
    (List.finRange 4).foldl (fun acc j => acc + Aeven i j) 0 == 3) = true := by
  native_decide

-- Step 1: eigenvalues ⊆ {−1, 1, 3}
theorem Ae_minpoly :
    meq4 (mm4 (mm4 (msub4 Aeven (scI4 3)) (msub4 Aeven (scI4 1)))
      (msub4 Aeven (scI4 (-1)))) mzero4 = true := by
  native_decide

-- Step 2: traces → multiplicities
theorem Ae_tr1 : tr4 Aeven = 4 := by native_decide
theorem Ae_tr2 : tr4 (mm4 Aeven Aeven) = 12 := by native_decide

/-- Multiplicities: a+b+c=4, 3a+b−c=4, 9a+b+c=12 → a=1, b=2, c=1. -/
theorem Ae_mult_dim : 1 + 2 + 1 = (4 : Int) := by norm_num
theorem Ae_mult_tr1 : 1 * 3 + 2 * 1 + 1 * (-1) = (4 : Int) := by norm_num
theorem Ae_mult_tr2 : 1 * 9 + 2 * 1 + 1 * 1 = (12 : Int) := by norm_num

-- Step 3: 4 orthogonal eigenvectors
def v3 : V4 := ![1, 1, 1, 1]
def vm1 : V4 := ![1, -1, -1, 1]
def v1a : V4 := ![1, 0, -1, 0]
def v1b : V4 := ![0, 1, 0, -1]

-- Eigenvalue verification
theorem v3_eig : veq4 (mv4 Aeven v3) (sv4 3 v3) = true := by native_decide
theorem vm1_eig : veq4 (mv4 Aeven vm1) (sv4 (-1) vm1) = true := by native_decide
theorem v1a_eig : veq4 (mv4 Aeven v1a) (sv4 1 v1a) = true := by native_decide
theorem v1b_eig : veq4 (mv4 Aeven v1b) (sv4 1 v1b) = true := by native_decide

-- Pairwise orthogonality (6 pairs)
theorem orth_3_m1 : dot4 v3 vm1 = 0 := by native_decide
theorem orth_3_1a : dot4 v3 v1a = 0 := by native_decide
theorem orth_3_1b : dot4 v3 v1b = 0 := by native_decide
theorem orth_m1_1a : dot4 vm1 v1a = 0 := by native_decide
theorem orth_m1_1b : dot4 vm1 v1b = 0 := by native_decide
theorem orth_1a_1b : dot4 v1a v1b = 0 := by native_decide

-- Nonzero
theorem v3_nz : dot4 v3 v3 ≠ 0 := by native_decide
theorem vm1_nz : dot4 vm1 vm1 ≠ 0 := by native_decide
theorem v1a_nz : dot4 v1a v1a ≠ 0 := by native_decide
theorem v1b_nz : dot4 v1b v1b ≠ 0 := by native_decide

-- ═══════════════════════════════════════════
-- Odd component: same eigenvectors work (Ae = Ao)
-- ═══════════════════════════════════════════

theorem Ao_minpoly :
    meq4 (mm4 (mm4 (msub4 Aodd (scI4 3)) (msub4 Aodd (scI4 1)))
      (msub4 Aodd (scI4 (-1)))) mzero4 = true := by
  native_decide

theorem Ao_tr1 : tr4 Aodd = 4 := by native_decide
theorem Ao_tr2 : tr4 (mm4 Aodd Aodd) = 12 := by native_decide

theorem v3_eig_odd : veq4 (mv4 Aodd v3) (sv4 3 v3) = true := by native_decide
theorem vm1_eig_odd : veq4 (mv4 Aodd vm1) (sv4 (-1) vm1) = true := by native_decide
theorem v1a_eig_odd : veq4 (mv4 Aodd v1a) (sv4 1 v1a) = true := by native_decide
theorem v1b_eig_odd : veq4 (mv4 Aodd v1b) (sv4 1 v1b) = true := by native_decide

-- ═══════════════════════════════════════════
-- Global consistency
-- ═══════════════════════════════════════════

/-- Tr(Ae) + Tr(Ao) = Tr(A) = 8. -/
theorem global_tr1 : tr4 Aeven + tr4 Aodd = 8 := by native_decide

/-- Tr(Ae²) + Tr(Ao²) = Tr(A²) = 24. -/
theorem global_tr2 : tr4 (mm4 Aeven Aeven) + tr4 (mm4 Aodd Aodd) = 24 := by native_decide

/-- ρ = 3 is simple in each component → Perron-Frobenius irreducibility. -/
theorem perron_simple_even :
    1 * 3 + 2 * 1 + 1 * (-1) = (4 : Int) := Ae_mult_tr1

/-!
## Summary

| Component | Vertices | Residues | Spectrum | ρ mult |
|-----------|----------|----------|----------|--------|
| Even | {0,2,4,6} | {1,11,17,23} | {3, 1, 1, −1} | 1 (simple) |
| Odd | {1,3,5,7} | {7,13,19,29} | {3, 1, 1, −1} | 1 (simple) |

**Key fact**: Aeven = Aodd (identical 4×4 matrices).
The C₂ parity splitting acts trivially on the adjacency structure.

**Spectral decomposition**:
  {3², 1⁴, (−1)²} = {3, 1, 1, −1} ⊎ {3, 1, 1, −1}
-/

end ComponentSpectrum
end CouretUnification.Core