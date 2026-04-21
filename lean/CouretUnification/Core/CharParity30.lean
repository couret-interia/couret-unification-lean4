import CouretUnification.Core.Characters30Bridge

namespace CouretUnification.Core

def negOneG30 : G30 := -1

theorem negOneG30_sq : negOneG30 * negOneG30 = (1 : G30) := by decide

theorem charOnG30_one (χ : CharIdx) :
    charOnG30 χ (1 : G30) = 1 := by
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

theorem charOnG30_negOne_sq (χ : CharIdx) :
    charOnG30 χ negOneG30 * charOnG30 χ negOneG30 = 1 := by
  rw [← charOnG30_mul, negOneG30_sq]; exact charOnG30_one χ

theorem charOnG30_negOne_pm (χ : CharIdx) :
    charOnG30 χ negOneG30 = 1 ∨ charOnG30 χ negOneG30 = -1 := by
  have hsq := charOnG30_negOne_sq χ
  have hfac : (charOnG30 χ negOneG30 - 1) * (charOnG30 χ negOneG30 + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · left; exact sub_eq_zero.mp h1
  · right; exact eq_neg_of_add_eq_zero_left h2

noncomputable def charParity (χ : CharIdx) : Bool :=
  if charOnG30 χ negOneG30 = 1 then true else false

noncomputable def charSign (χ : CharIdx) : ℤ :=
  if charOnG30 χ negOneG30 = 1 then 1 else -1

theorem charSign_coe (χ : CharIdx) :
    ((charSign χ : ℤ) : ℂ) = charOnG30 χ negOneG30 := by
  unfold charSign; split_ifs with h
  · simp [h]
  · rcases charOnG30_negOne_pm χ with h1 | h2
    · exact absurd h1 h
    · push_cast; exact h2.symm

end CouretUnification.Core
