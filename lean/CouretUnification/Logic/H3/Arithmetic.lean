import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Arithmétique fondamentale — Couret-Unification
RHClaimed = false. Dédié à Bernard Couret (1928–1999).
-/

open scoped BigOperators

namespace CouretUnification
namespace Arithmetic

-- ═══════════════════════════════════════════════════════════
-- §1. Fonction de Möbius par division récursive
-- ═══════════════════════════════════════════════════════════

/-- Möbius function via trial division. -/
def mu : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    have h₁ : 1 < (n + 2).minFac :=
      (Nat.minFac_prime (by omega)).one_lt
    have h₂ : (n + 2) / (n + 2).minFac < n + 2 :=
      Nat.div_lt_self (by omega) h₁
    let p := (n + 2).minFac
    if p ∣ ((n + 2) / p) then 0 else -(mu ((n + 2) / p))

theorem mu_zero : mu 0 = 0 := by native_decide
theorem mu_one  : mu 1 = 1 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §2. Fonction de Mertens
-- ═══════════════════════════════════════════════════════════

/-- Mertens function M(n) = Σ_{k=0}^{n} μ(k). -/
def mertens (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) (fun k => mu k)

-- ═══════════════════════════════════════════════════════════
-- §3. Second moment restreint K(q)
-- ═══════════════════════════════════════════════════════════

/-- K(q) = Σ_{a ∈ {1..q}, (a,q)=1} M(a)². -/
noncomputable def K (q : ℕ) : ℝ :=
  Finset.sum
    ((Finset.range (q + 1)).filter (fun a => decide (0 < a ∧ Nat.Coprime a q)))
    (fun a => ((mertens a : ℤ) : ℝ) ^ 2)

/-- K(q) ≥ 0, sum of squares. -/
theorem K_nonneg (q : ℕ) : 0 ≤ K q := by
  unfold K
  apply Finset.sum_nonneg
  intro a _
  exact sq_nonneg _

-- ═══════════════════════════════════════════════════════════
-- §4. κ(q) normalisé
-- ═══════════════════════════════════════════════════════════

noncomputable def phi (q : ℕ) : ℝ := (Nat.totient q : ℝ)
noncomputable def kappaSq (q : ℕ) : ℝ := K q / phi q
noncomputable def kappa (q : ℕ) : ℝ := Real.sqrt (kappaSq q)

theorem kappa_nonneg (q : ℕ) : 0 ≤ kappa q := Real.sqrt_nonneg _

theorem kappaSq_nonneg (q : ℕ) : 0 ≤ kappaSq q := by
  unfold kappaSq phi
  apply div_nonneg (K_nonneg q)
  exact_mod_cast Nat.zero_le _

-- ═══════════════════════════════════════════════════════════
-- §5. Gouvernance
-- ═══════════════════════════════════════════════════════════

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

end Arithmetic
end CouretUnification