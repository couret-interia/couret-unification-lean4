import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
open Matrix
open Finset

namespace CouretUnification
namespace FiniteCore

abbrev Idx := Fin 8
abbrev Vec := Idx → ℝ
abbrev Mat := Matrix Idx Idx ℝ

/-- The 8 units of (Z/30Z)^x in natural order. -/
def unitsMod30 : Idx → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 11
  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17
  | ⟨5, _⟩ => 19
  | ⟨6, _⟩ => 23
  | ⟨7, _⟩ => 29

/-- CRT coordinates on C2 × C4. -/
def toCRT : Idx → Fin 2 × Fin 4
  | ⟨0, _⟩ => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | ⟨1, _⟩ => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | ⟨2, _⟩ => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | ⟨3, _⟩ => (⟨0, by decide⟩, ⟨3, by decide⟩)
  | ⟨4, _⟩ => (⟨1, by decide⟩, ⟨0, by decide⟩)
  | ⟨5, _⟩ => (⟨1, by decide⟩, ⟨1, by decide⟩)
  | ⟨6, _⟩ => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | ⟨7, _⟩ => (⟨1, by decide⟩, ⟨3, by decide⟩)

/-- The Couret triplet in CRT coordinates. -/
def inTCrt : (Fin 2 × Fin 4) → Prop
  | (u, v) =>
      (u = ⟨0, by decide⟩ ∧ v = ⟨0, by decide⟩) ∨
      (u = ⟨1, by decide⟩ ∧ v = ⟨0, by decide⟩) ∨
      (u = ⟨1, by decide⟩ ∧ v = ⟨2, by decide⟩)

/-- Exact Cayley adjacency matrix for T_C = {(0,0),(1,0),(1,2)}. -/
def cayleyMatrix : Mat :=
  !![
    1, 0, 0, 0, 1, 0, 1, 0;
    0, 1, 0, 0, 0, 1, 0, 1;
    0, 0, 1, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 0, 1;
    1, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0;
    0, 1, 0, 1, 0, 0, 0, 1
  ]

theorem cayleyMatrix_symm :
    cayleyMatrixᵀ = cayleyMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cayleyMatrix]

theorem cayleyMatrix_rowSum (i : Idx) :
    ∑ j : Idx, cayleyMatrix i j = 3 := by
  fin_cases i <;>
    rw [Fin.sum_univ_eight] <;>
    simp [cayleyMatrix, Matrix.cons_val_zero] <;>
    norm_num

/-- Constant vector. -/
def oneVec : Vec := fun _ => 1

/-- The non-trivial centered 3-eigenvector. -/
def altVec : Vec
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => -1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => -1

/-- Matrix action. -/
def applyM (x : Vec) : Vec :=
  fun i => ∑ j, cayleyMatrix i j * x j

/-- Centered operator L = 3I - M. -/
def centeredOp : Mat :=
  (3 : ℝ) • (1 : Mat) - cayleyMatrix

/-- Action of the centered operator. -/
def applyL (x : Vec) : Vec :=
  fun i => ∑ j, centeredOp i j * x j

/-- Euclidean dot product. -/
def dot (x y : Vec) : ℝ :=
  ∑ i, x i * y i

/-- Euclidean norm squared. -/
def normSq (x : Vec) : ℝ :=
  dot x x

/-- Quadratic form Q(x) = <Lx, x>. -/
def quadratic (x : Vec) : ℝ :=
  dot x (applyL x)

theorem normSq_nonneg (x : Vec) : 0 ≤ normSq x := by
  unfold normSq dot
  refine Finset.sum_nonneg ?_
  intro i hi
  nlinarith

/-- Centered hyperplane H°. -/
def Centered8 : Type :=
  { x : Vec // ∑ i, x i = 0 }

namespace Centered8

def normSq (x : Centered8) : ℝ := FiniteCore.normSq x.1

theorem sum_zero (x : Centered8) : ∑ i, x.1 i = 0 := x.2

theorem normSq_nonneg (x : Centered8) : 0 ≤ x.normSq := by
  exact FiniteCore.normSq_nonneg x.1

end Centered8

theorem altVec_centered : ∑ i, altVec i = 0 := by
  rw [Fin.sum_univ_eight]
  norm_num [altVec]

theorem applyM_oneVec_0 : applyM oneVec 0 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_1 : applyM oneVec 1 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_2 : applyM oneVec 2 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_3 : applyM oneVec 3 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_4 : applyM oneVec 4 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_5 : applyM oneVec 5 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_6 : applyM oneVec 6 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec_7 : applyM oneVec 7 = 3 := by
  unfold applyM oneVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix]
  norm_num

theorem applyM_oneVec :
    applyM oneVec = fun _ => 3 := by
  funext i
  fin_cases i
  · simpa using applyM_oneVec_0
  · simpa using applyM_oneVec_1
  · simpa using applyM_oneVec_2
  · simpa using applyM_oneVec_3
  · simpa using applyM_oneVec_4
  · simpa using applyM_oneVec_5
  · simpa using applyM_oneVec_6
  · simpa using applyM_oneVec_7

theorem applyL_eq (x : Vec) :
    applyL x = fun i => 3 * x i - applyM x i := by
  funext i
  unfold applyL centeredOp applyM
  calc
    (∑ j : Idx, ((((3 : ℝ) • (1 : Mat)) - cayleyMatrix) i j * x j))
        =
      (∑ j : Idx, ((((3 : ℝ) • (1 : Mat)) i j - cayleyMatrix i j) * x j)) := by
          rfl
    _ =
      (∑ j : Idx, ((((3 : ℝ) • (1 : Mat)) i j) * x j - cayleyMatrix i j * x j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [sub_mul]
    _ =
      (∑ j : Idx, (((3 : ℝ) • (1 : Mat)) i j * x j)) - (∑ j : Idx, cayleyMatrix i j * x j) := by
          rw [Finset.sum_sub_distrib]
    _ =
      3 * x i - (∑ j : Idx, cayleyMatrix i j * x j) := by
          simp [Matrix.one_apply]

theorem applyL_oneVec :
    applyL oneVec = fun _ => 0 := by
  funext i
  rw [applyL_eq, applyM_oneVec]
  simp [oneVec]

theorem applyM_altVec_0 : applyM altVec 0 = 3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_1 : applyM altVec 1 = -3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_2 : applyM altVec 2 = 3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_3 : applyM altVec 3 = -3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_4 : applyM altVec 4 = 3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_5 : applyM altVec 5 = -3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_6 : applyM altVec 6 = 3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec_7 : applyM altVec 7 = -3 := by
  unfold applyM altVec
  rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  norm_num

theorem applyM_altVec :
    applyM altVec = fun i => 3 * altVec i := by
  funext i
  fin_cases i
  · simpa [altVec] using applyM_altVec_0
  · simpa [altVec] using applyM_altVec_1
  · simpa [altVec] using applyM_altVec_2
  · simpa [altVec] using applyM_altVec_3
  · simpa [altVec] using applyM_altVec_4
  · simpa [altVec] using applyM_altVec_5
  · simpa [altVec] using applyM_altVec_6
  · simpa [altVec] using applyM_altVec_7

theorem applyL_altVec :
    applyL altVec = fun _ => 0 := by
  funext i
  rw [applyL_eq, applyM_altVec]
  fin_cases i <;> simp [altVec] -- <;> ring_nf

theorem altVec_normSq_eq_eight : normSq altVec = 8 := by
  unfold normSq dot
  rw [Fin.sum_univ_eight]
  norm_num [altVec]

theorem oneVec_normSq_eq_eight : normSq oneVec = 8 := by
  unfold normSq dot oneVec
  rw [Fin.sum_univ_eight]
  norm_num

theorem applyL_oneVec_zero_at (i : Idx) :
    applyL oneVec i = 0 := by
  simpa using congrFun applyL_oneVec i

theorem applyL_altVec_zero_at (i : Idx) :
    applyL altVec i = 0 := by
  simpa using congrFun applyL_altVec i

theorem oneVec_in_kernel_applyL : applyL oneVec = 0 := by
  simpa using applyL_oneVec

theorem oneVec_eigenvalue_three : applyM oneVec = fun _ => 3 := by
  funext i
  simpa [applyM, oneVec] using cayleyMatrix_rowSum i

theorem altVec_eigenvalue_three : applyM altVec = fun i => 3 * altVec i := by
  simpa using applyM_altVec

theorem oneVec_eigenvalue_zero_for_L : applyL oneVec = 0 := by
  simpa using oneVec_in_kernel_applyL

theorem altVec_in_kernel_applyL : applyL altVec = 0 := by
  simpa using applyL_altVec

theorem altVec_eigenvalue_zero_for_L : applyL altVec = 0 := by
  simpa using altVec_in_kernel_applyL

theorem oneVec_and_altVec_in_kernel_applyL :
    applyL oneVec = 0 ∧ applyL altVec = 0 := by
  exact ⟨oneVec_in_kernel_applyL, altVec_in_kernel_applyL⟩

/-- Explicit coercive-sector condition. -/
def GoodSubspace (x : Centered8) : Prop :=
  dot x.1 altVec = 0

/-- Four block sums adapted to the Cayley pattern. -/
def aSum (x : Vec) : ℝ := x 0 + x 2
def bSum (x : Vec) : ℝ := x 1 + x 3
def cSum (x : Vec) : ℝ := x 4 + x 6
def dSum (x : Vec) : ℝ := x 5 + x 7

theorem goodSubspace_iff_dot_altVec_zero (x : Centered8) :
    GoodSubspace x ↔ dot x.1 altVec = 0 := by
  rfl

theorem dot_altVec_explicit (x : Vec) :
    dot x altVec = aSum x - bSum x + cSum x - dSum x := by
  unfold dot aSum bSum cSum dSum altVec
  rw [Fin.sum_univ_eight]
  ring

theorem goodSubspace_blocks (x : Centered8) :
    GoodSubspace x ↔ aSum x.1 - bSum x.1 + cSum x.1 - dSum x.1 = 0 := by
  rw [goodSubspace_iff_dot_altVec_zero]
  simp [dot_altVec_explicit]

theorem centered_blocks (x : Centered8) :
    aSum x.1 + bSum x.1 + cSum x.1 + dSum x.1 = 0 := by
  have hx : ∑ i : Idx, x.1 i = 0 := x.2
  rw [Fin.sum_univ_eight] at hx
  unfold aSum bSum cSum dSum
  linarith

theorem goodSubspace_centered_blocks (x : Centered8) (hx : GoodSubspace x) :
    aSum x.1 + cSum x.1 = 0 ∧ bSum x.1 + dSum x.1 = 0 := by
  have h1 : aSum x.1 - bSum x.1 + cSum x.1 - dSum x.1 = 0 :=
    (goodSubspace_blocks x).1 hx
  have h2 : aSum x.1 + bSum x.1 + cSum x.1 + dSum x.1 = 0 :=
    centered_blocks x
  constructor <;> linarith

/-- Expanded explicit formula for Q(x). -/
theorem quadratic_explicit_raw (x : Vec) :
    quadratic x
      = 2 * (x 0)^2 + 2 * (x 1)^2 + 2 * (x 2)^2 + 2 * (x 3)^2
      + 2 * (x 4)^2 + 2 * (x 5)^2 + 2 * (x 6)^2 + 2 * (x 7)^2
      - 2 * x 0 * x 4 - 2 * x 0 * x 6
      - 2 * x 1 * x 5 - 2 * x 1 * x 7
      - 2 * x 2 * x 4 - 2 * x 2 * x 6
      - 2 * x 3 * x 5 - 2 * x 3 * x 7 := by
  unfold quadratic dot
  rw [applyL_eq]
  unfold applyM
  rw [Fin.sum_univ_eight]
  simp_rw [Fin.sum_univ_eight]
  simp [cayleyMatrix, Matrix.cons_val_zero]
  ring_nf

theorem quadratic_explicit (x : Vec) :
    quadratic x
      = 2 * normSq x
      - 2 * (aSum x * cSum x + bSum x * dSum x) := by
  rw [quadratic_explicit_raw]
  unfold normSq dot aSum bSum cSum dSum
  rw [Fin.sum_univ_eight]
  ring_nf

theorem quadratic_lower_bound_on_goodSubspace (x : Centered8)
    (hx : GoodSubspace x) :
    2 * x.normSq ≤ quadratic x.1 := by
  rcases goodSubspace_centered_blocks x hx with ⟨hAC, hBD⟩
  rw [quadratic_explicit x.1]
  have hc : cSum x.1 = - aSum x.1 := by
    linarith
  have hd : dSum x.1 = - bSum x.1 := by
    linarith
  rw [hc, hd]
  have hsq :
      2 * normSq x.1 - 2 * (aSum x.1 * (-aSum x.1) + bSum x.1 * (-bSum x.1))
        =
      2 * normSq x.1 + 2 * ((aSum x.1)^2 + (bSum x.1)^2) := by
    ring
  rw [hsq]
  have hxnorm : x.normSq = normSq x.1 := by
    rfl
  rw [hxnorm]
  have ha : 0 ≤ (aSum x.1)^2 := sq_nonneg (aSum x.1)
  have hb : 0 ≤ (bSum x.1)^2 := sq_nonneg (bSum x.1)
  nlinarith

theorem quadratic_on_goodSubspace_ge_twice_normSq
    (x : Centered8) (hx : GoodSubspace x) :
    quadratic x.1 >= 2 * x.normSq := by
  simpa [ge_iff_le] using quadratic_lower_bound_on_goodSubspace x hx

/-- Short alias for the exact coercive gap on the good subspace. -/
theorem hasGapTwo
    (x : Centered8) (hx : GoodSubspace x) :
    2 * x.normSq ≤ quadratic x.1 := by
  simpa using quadratic_lower_bound_on_goodSubspace x hx

/-- Packaged finite-core coercive statement. -/
def HasGapTwo : Prop :=
  ∀ x : Centered8, GoodSubspace x → 2 * x.normSq ≤ quadratic x.1

theorem HasGapTwo_proved : HasGapTwo := by
  intro x hx
  exact hasGapTwo x hx

/-- Exact finite coercive gap on the good subspace. -/
theorem finite_exact_gap_kappa_two
    (x : Centered8) (hx : GoodSubspace x) :
    2 * x.normSq ≤ quadratic x.1 := by
  simpa using hasGapTwo x hx

/-- Canonical geometric scale from dim(H°)=7. -/
theorem lambda_sq_eq_one_seventh :
    (1 / Real.sqrt 7)^2 = (1 : ℝ) / 7 := by
  have hs : Real.sqrt 7 ≠ 0 := by
    have h : 0 < Real.sqrt 7 := by
      apply Real.sqrt_pos.2
      norm_num
    linarith
  field_simp [hs]
  have hsq : Real.sqrt 7 ^ 2 = (7 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  nlinarith

/-!
## Finite spectral doctrine (publication layer)

This block gathers the core structural statements of the finite Couret operator.

It isolates:
- the global kernel witness (`oneVec`),
- the centered kernel witness (`altVec`),
- the block factorization of the quadratic form,
- the exact coercive gap on the reduced centered sector.
-/

/-- The constant vector is a global kernel witness of `L = 3I - M`. -/
theorem oneVec_global_kernel_witness :
    applyL oneVec = 0 := by
  simpa using oneVec_in_kernel_applyL

/-- The alternating vector is a centered kernel witness of `L`. -/
theorem altVec_centered_kernel_witness :
    applyL altVec = 0 ∧ (∑ i, altVec i = 0) := by
  exact ⟨altVec_in_kernel_applyL, altVec_centered⟩

/-- Exact block factorization of the quadratic form. -/
theorem quadratic_block_factorization (x : Vec) :
    quadratic x =
      2 * normSq x - 2 * (aSum x * cSum x + bSum x * dSum x) := by
  simpa using quadratic_explicit x

/-- Finite coercive doctrine on the reduced centered sector. -/
theorem finite_doctrine_coercive_sector
    (x : Centered8) (hx : GoodSubspace x) :
    2 * x.normSq ≤ quadratic x.1 := by
  simpa using quadratic_lower_bound_on_goodSubspace x hx

/-- Finite exact spectral structure of the centered operator. -/
theorem finite_spectral_structure_summary :
    applyL oneVec = 0 ∧
    applyL altVec = 0 ∧
    (∑ i, altVec i = 0) := by
  exact ⟨
    oneVec_in_kernel_applyL,
    altVec_in_kernel_applyL,
    altVec_centered
  ⟩

namespace FiniteDoctrine

theorem kernel_structure :
    applyL oneVec = 0 ∧ applyL altVec = 0 := by
  exact ⟨oneVec_in_kernel_applyL, altVec_in_kernel_applyL⟩

theorem coercive_gap :
    ∀ x : Centered8, GoodSubspace x → 2 * x.normSq ≤ quadratic x.1 :=
  HasGapTwo_proved

end FiniteDoctrine

end FiniteCore
end CouretUnification
