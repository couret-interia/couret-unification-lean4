/-
  CouretUnification/Core/Characters30Bridge.lean — v35.1
  0 sorry. RHClaimed = false.
  NOTE : ne doit PAS importer CRTEquiv.
-/
import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharacterLemmas
open scoped BigOperators
namespace CouretUnification.Core

def g30ToIdx (u : G30) : Idx :=
  if (u : ZMod 30) = 1  then ⟨0, by omega⟩
  else if (u : ZMod 30) = 7  then ⟨1, by omega⟩
  else if (u : ZMod 30) = 11 then ⟨2, by omega⟩
  else if (u : ZMod 30) = 13 then ⟨3, by omega⟩
  else if (u : ZMod 30) = 17 then ⟨4, by omega⟩
  else if (u : ZMod 30) = 19 then ⟨5, by omega⟩
  else if (u : ZMod 30) = 23 then ⟨6, by omega⟩
  else ⟨7, by omega⟩

def charOnG30 (χ : CharIdx) : FunG30 := fun g => characterEval χ (g30ToIdx g)
noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹
def g30Coord (g : G30) : Fin 2 × Fin 4 := residueCoord (g30ToIdx g)
def addCoord (p q : Fin 2 × Fin 4) : Fin 2 × Fin 4 := (p.1 + q.1, p.2 + q.2)

-- Force l'évaluation de l'addition dans Fin n (simp/norm_num ne le font pas)
@[simp] private lemma fin4_add_eval (a b : Fin 4) :
    (a + b : Fin 4) = ⟨(a.val + b.val) % 4, Nat.mod_lt _ (by decide)⟩ := by ext; rfl
@[simp] private lemma fin2_add_eval (a b : Fin 2) :
    (a + b : Fin 2) = ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩ := by ext; rfl

-- Puissances de I (ring ne sait pas I² = -1)
private lemma Ip3  : Complex.I ^ (3:ℕ)  = -Complex.I := by
  have : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  rw [this, Complex.I_sq]; ring
private lemma Ip4  : Complex.I ^ (4:ℕ)  = 1 := by
  have : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip6  : Complex.I ^ (6:ℕ)  = -1 := by
  have : Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip7  : Complex.I ^ (7:ℕ)  = -Complex.I := by
  have : Complex.I ^ 7 = (Complex.I ^ 2) ^ 3 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip9  : Complex.I ^ (9:ℕ)  = Complex.I := by
  have : Complex.I ^ 9 = (Complex.I ^ 2) ^ 4 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip10 : Complex.I ^ (10:ℕ) = -1 := by
  have : Complex.I ^ 10 = (Complex.I ^ 2) ^ 5 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip12 : Complex.I ^ (12:ℕ) = 1  := by
  have : Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip15 : Complex.I ^ (15:ℕ) = -Complex.I := by
  have : Complex.I ^ 15 = (Complex.I ^ 2) ^ 7 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip18 : Complex.I ^ (18:ℕ) = -1 := by
  have : Complex.I ^ 18 = (Complex.I ^ 2) ^ 9 := by ring
  rw [this, Complex.I_sq]; norm_num
-- Inégalités concrètes dans ℂ
private lemma I_ne_one : Complex.I ≠ 1 := by
  intro h; have := congr_arg Complex.im h; simp at this
private lemma neg_I_ne_one : -Complex.I ≠ 1 := by
  intro h; have := congr_arg Complex.im h; simp at this
private lemma neg_one_ne_one_C : (-1 : ℂ) ≠ 1 := by norm_num

set_option maxHeartbeats 800000 in
theorem g30Coord_mul (a b : G30) :
    g30Coord (a * b) = addCoord (g30Coord a) (g30Coord b) := by
  fin_cases a <;> fin_cases b <;>
    simp [g30Coord, g30ToIdx, residueCoord, addCoord] <;> decide

theorem charOnG30_factor (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

theorem c2Phase_mul_right (m : Fin 2) (e₁ e₂ : Fin 2) :
    c2Phase m (e₁ + e₂) = c2Phase m e₁ * c2Phase m e₂ := by
  fin_cases m <;> fin_cases e₁ <;> fin_cases e₂ <;> simp [c2Phase] <;> ring

private lemma I_mul_I : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]

set_option maxHeartbeats 1600000 in
theorem c4Phase_mul_right (n : Fin 4) (k₁ k₂ : Fin 4) :
    c4Phase n (k₁ + k₂) = c4Phase n k₁ * c4Phase n k₂ := by
  fin_cases n <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp only [c4Phase, fin4_add_eval] <;>
    first | ring | (simp only [Complex.I_sq, I_mul_I, Ip3, Ip4, Ip6, Ip9,
                               neg_neg, neg_mul, mul_neg, one_mul, mul_one,
                               pow_zero, pow_one]; ring)

theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  simp only [charOnG30_factor]
  rw [g30Coord_mul]
  simp only [addCoord]
  rw [c2Phase_mul_right, c4Phase_mul_right]
  ring

def charOnG30AsHom (χ : CharIdx) : G30 →* ℂ where
  toFun := charOnG30 χ
  map_one' := by
    fin_cases χ <;>
      simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]
  map_mul' := charOnG30_mul χ

set_option maxHeartbeats 800000 in
theorem charOnG30AsHom_ne_one (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    charOnG30AsHom χ ≠ 1 := by
  intro h; apply hχ
  fin_cases χ
  · rfl
  all_goals (
    exfalso
    have h7 := DFunLike.congr_fun h (⟨7, 13, by decide, by decide⟩ : G30)
    simp only [charOnG30AsHom, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply] at h7
    -- Precompute g30ToIdx 7 = ⟨1,_⟩ (ZMod needs decide)
    have hidx : g30ToIdx (⟨7, 13, by decide, by decide⟩ : G30) = ⟨1, by omega⟩ := by
      simp [g30ToIdx]; decide
    -- Evaluate character at index 1
    simp only [charOnG30, hidx, characterEval, charCoord, residueCoord,
               c2Phase, c4Phase] at h7
    -- Normalize I-powers
    simp only [Complex.I_sq, I_mul_I, Ip3, pow_zero, pow_one,
               one_mul, mul_one, neg_neg] at h7
    -- h7 is now I = 1, -I = 1, or -1 = 1
    first
      | exact absurd h7 I_ne_one | exact absurd h7 neg_I_ne_one
      | exact absurd h7 neg_one_ne_one_C
      | exact absurd h7.symm I_ne_one | exact absurd h7.symm neg_I_ne_one
      | exact absurd h7.symm neg_one_ne_one_C
  )

theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  have hne := charOnG30AsHom_ne_one χ hχ
  have key := sum_char_eq_zero_of_ne_one (charOnG30AsHom χ) hne
  convert key using 1; apply Finset.sum_congr rfl; intro g _; rfl

theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

theorem charOnG30_ne_zero (χ : CharIdx) : charOnG30 χ ≠ 0 := by
  intro h; have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase] at h1

private lemma sum_reindex_mul_inv' (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by have := mul_left_cancel h; exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  calc ∑ y : G30, K (x * y⁻¹) * charOnG30 χ y
      = ∑ g : G30, K g * charOnG30 χ (g⁻¹ * x) := by
          rw [← sum_reindex_mul_inv' x (fun g => K g * charOnG30 χ (g⁻¹ * x))]
          apply Finset.sum_congr rfl; intro y _; congr 1; congr 1; group
    _ = ∑ g : G30, K g * (charOnG30 χ g⁻¹ * charOnG30 χ x) := by
          apply Finset.sum_congr rfl; intro g _; congr 1; exact charOnG30_mul χ g⁻¹ x
    _ = (∑ g : G30, K g * charOnG30 χ g⁻¹) * charOnG30 χ x := by
          simp_rw [← mul_assoc]; rw [← Finset.sum_mul]

theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x; exact convolution_diag_pointwise K χ x

end CouretUnification.Core