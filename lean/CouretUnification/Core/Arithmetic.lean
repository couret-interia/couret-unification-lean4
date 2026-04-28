import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Arithmétique fondamentale — Couret-Unification
RHClaimed = false. Dédié à Bernard Couret (1928–1999).
-/

open scoped BigOperators

namespace CouretUnification.Arithmetic

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

/-- `M(0) = 0`. -/
theorem mertens_zero : mertens 0 = 0 := by
  unfold mertens
  simp [mu_zero]

/-- Formule de récurrence de Mertens :
`M(n+1) = M(n) + μ(n+1)`. -/
theorem mertens_succ (n : ℕ) : mertens (n + 1) = mertens n + mu (n + 1) := by
  unfold mertens
  rw [Finset.sum_range_succ]

/-- Incrément de Mertens :
`M(n+1) - M(n) = μ(n+1)`. -/
theorem mertens_succ_sub (n : ℕ) :
    mertens (n + 1) - mertens n = mu (n + 1) := by
  rw [mertens_succ]
  ring

/-- Pour `n ≥ 2`, dépliage de la définition récursive de `mu`. -/
private lemma mu_eq_unfold {n : ℕ} (hn : 2 ≤ n) :
    mu n =
      let p := n.minFac
      if p ∣ (n / p) then 0 else -(mu (n / p)) := by
  rcases n with _ | _ | n
  · omega
  · omega
  · simp [mu]

/-- Décomposition squarefree le long de `minFac`.

Pour `n ≥ 2`, `n` est squarefree si et seulement si :
- `minFac n` ne redivise pas le quotient `n / minFac n`,
- et ce quotient est lui-même squarefree. -/
private lemma squarefree_minFac_quot_iff {n : ℕ} (hn : 2 ≤ n) :
    Squarefree n ↔
      ¬ n.minFac ∣ n / n.minFac ∧ Squarefree (n / n.minFac) := by
  let p := n.minFac
  have hp_prime : Nat.Prime p := by
    dsimp [p]
    exact Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ n := by
    dsimp [p]
    exact Nat.minFac_dvd n
  have hn_eq : n = p * (n / p) := by
    symm
    exact Nat.mul_div_cancel' hp_dvd
  have hp_sqf : Squarefree p := hp_prime.squarefree

  constructor
  · intro hsq
    have hmul : Squarefree (p * (n / p)) := by
      rw [← hn_eq]
      exact hsq
    rcases (Nat.squarefree_mul_iff).1 hmul with ⟨hcop, _, hq_sqf⟩
    refine ⟨?_, hq_sqf⟩
    intro hpq
    exact (Nat.Prime.coprime_iff_not_dvd hp_prime).mp hcop hpq

  · intro h
    rcases h with ⟨hp_ndvd, hq_sqf⟩
    have hcop : p.Coprime (n / p) := by
      exact (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hp_ndvd
    have hmul : Squarefree (p * (n / p)) := by
      exact (Nat.squarefree_mul_iff).2 ⟨hcop, hp_sqf, hq_sqf⟩
    rw [hn_eq]
    exact hmul

/-- Pont fondamental pour la `mu` récursive du dépôt :
`mu n ≠ 0` si et seulement si `n` est squarefree. -/
theorem mu_ne_zero_iff_squarefree {n : ℕ} (hn : 1 ≤ n) :
    mu n ≠ 0 ↔ Squarefree n := by
  revert hn
  induction' n using Nat.strong_induction_on with n ih
  intro hn
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          simp [mu_one]
      | succ n =>
          have hn2 : 2 ≤ n.succ.succ := by
            omega

          have hp_gt1 : 1 < (n.succ.succ).minFac := by
            exact (Nat.minFac_prime (by omega)).one_lt

          have hquot_lt :
              (n.succ.succ) / (n.succ.succ).minFac < n.succ.succ := by
            exact Nat.div_lt_self (by omega) hp_gt1

          by_cases hdiv :
              (n.succ.succ).minFac ∣ (n.succ.succ) / (n.succ.succ).minFac

          · rw [mu_eq_unfold hn2, if_pos hdiv,
                squarefree_minFac_quot_iff (n := n.succ.succ) hn2]
            simp [hdiv]

          · have hquot_pos :
                1 ≤ (n.succ.succ) / (n.succ.succ).minFac := by
              have hpos : 0 < (n.succ.succ) / (n.succ.succ).minFac := by
                by_contra hq0
                have hq :
                    (n.succ.succ) / (n.succ.succ).minFac = 0 :=
                  Nat.eq_zero_of_not_pos hq0
                have hzero : (n.succ.succ).minFac ∣ n.succ.succ / n.succ.succ.minFac := by
                  rw [hq]
                  exact dvd_zero ((n.succ.succ).minFac)
                exact hdiv hzero

              exact Nat.succ_le_of_lt hpos

            have hrec :
                mu ((n.succ.succ) / (n.succ.succ).minFac) ≠ 0
                  ↔
                Squarefree ((n.succ.succ) / (n.succ.succ).minFac) := by
              exact ih
                ((n.succ.succ) / (n.succ.succ).minFac)
                hquot_lt
                hquot_pos

            rw [mu_eq_unfold hn2, if_neg hdiv,
                squarefree_minFac_quot_iff (n := n.succ.succ) hn2]
            rw [neg_ne_zero]
            simpa [hdiv] using hrec

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

end CouretUnification.Arithmetic
