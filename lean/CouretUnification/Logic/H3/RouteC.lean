import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import CouretUnification.Logic.H3.Arithmetic

/-!
# Route C raffinée — Infrastructure formelle v32.39

Fourth refactor :
- `squarefreeCount` utilise maintenant la vraie définition Mathlib `Squarefree`
  (et non plus l'approximation via `mu ≠ 0`).
- Le verrou `squarefreeCount_linear_on_primorial` est poussé vers son vrai
  niveau minimal : `squarefreeCount_linear_global` (densité squarefree globale).

Sorry restants :
- `S1_lower_from_squarefree`      (combinatoire discret)
- `squarefreeCount_linear_global` (densité squarefree, ~6/π²)
- `routeC_error_control`          (contrôle θ < 1)

`RHClaimed = false.`
Dédié à Bernard Couret (1928–1999).
-/

open Filter
open scoped Topology

namespace CouretUnification
namespace RouteC

-- ═══════════════════════════════════════════════════════════
-- §1. Recollement avec l'arithmétique réelle
-- ═══════════════════════════════════════════════════════════

noncomputable abbrev phi : ℕ → ℝ := CouretUnification.Arithmetic.phi
noncomputable abbrev K : ℕ → ℝ := CouretUnification.Arithmetic.K
noncomputable abbrev kappaSq : ℕ → ℝ := CouretUnification.Arithmetic.kappaSq
noncomputable abbrev kappa : ℕ → ℝ := CouretUnification.Arithmetic.kappa

/-- Primorial tower. Placeholder. -/
def primorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => primorial n * (Nat.minFac (primorial n + 1))

theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  induction n with
  | zero => simp [primorial]
  | succ n ih =>
    unfold primorial
    exact Nat.mul_pos ih (Nat.minFac_pos _)

theorem phi_primorial_pos (n : ℕ) : 0 < phi (primorial n) := by
  unfold phi CouretUnification.Arithmetic.phi
  exact Nat.cast_pos.mpr ((Nat.totient_pos).mpr (primorial_pos n))

theorem phi_primorial_nonneg (n : ℕ) : 0 ≤ phi (primorial n) :=
  le_of_lt (phi_primorial_pos n)

-- ═══════════════════════════════════════════════════════════
-- §2. Décomposition analytique
-- ═══════════════════════════════════════════════════════════

noncomputable def S1 (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (q + 1))
    (fun n => if 0 < n then ((Arithmetic.mertens n : ℤ) : ℝ) ^ 2 else 0)

theorem S1_nonneg (q : ℕ) : 0 ≤ S1 q := by
  unfold S1
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

noncomputable def MainTerm (q : ℕ) : ℝ :=
  (phi q / (q : ℝ)) * S1 q

noncomputable def ErrorTerm (q : ℕ) : ℝ :=
  K q - MainTerm q

theorem K_decomposition (q : ℕ) : K q = MainTerm q + ErrorTerm q := by
  unfold ErrorTerm; ring

-- ═══════════════════════════════════════════════════════════
-- §3. Squarefree count (via la vraie définition Mathlib)
-- ═══════════════════════════════════════════════════════════

/-- Number of squarefree integers in `{1, …, q}`.
    Uses Mathlib's `Squarefree` predicate. -/
noncomputable def squarefreeCount (q : ℕ) : ℝ :=
  (((Finset.Icc 1 q).filter (fun n => Squarefree n)).card : ℕ)

theorem squarefreeCount_nonneg (q : ℕ) : 0 ≤ squarefreeCount q := by
  unfold squarefreeCount
  positivity

-- ═══════════════════════════════════════════════════════════
-- §4. Décomposition structurelle de l'erreur
-- ═══════════════════════════════════════════════════════════

def ErrorPieces (_q : ℕ) : Finset ℕ := {0}

noncomputable def E (q _d : ℕ) : ℝ := ErrorTerm q

theorem errorTerm_decomposition (q : ℕ) :
    ErrorTerm q = Finset.sum (ErrorPieces q) (fun d => E q d) := by
  simp [ErrorPieces, E]

-- ═══════════════════════════════════════════════════════════
-- §5. Verrous analytiques minimaux
-- ═══════════════════════════════════════════════════════════

/-- **Verrou combinatoire** — une fraction positive des squarefree
    contribue à `S1`. -/
theorem S1_lower_from_squarefree :
    ∃ β : ℝ, 0 < β ∧
      ∀ q : ℕ, β * squarefreeCount q ≤ S1 q := by
  sorry

/-- **Verrou analytique global** — densité linéaire des squarefree.
    Corresponds to the classical density `6/π²`; any explicit `α > 0` suffices. -/
theorem squarefreeCount_linear_global :
    ∃ α : ℝ, 0 < α ∧
      ∀ q : ℕ, α * (q : ℝ) ≤ squarefreeCount q := by
  sorry

/-- **Verrou analytique Route C** — contrôle `θ < 1`. -/
theorem routeC_error_control :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        Finset.sum (ErrorPieces (primorial n))
          (fun d => |E (primorial n) d|)
          ≤ θ * MainTerm (primorial n) := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §6. Recollements algébriques (fermés)
-- ═══════════════════════════════════════════════════════════

/-- Spécialisation triviale de la borne globale à la tour primorielle. -/
theorem squarefreeCount_linear_on_primorial :
    ∃ n₀ : ℕ, ∃ α : ℝ, 0 < α ∧
      ∀ n : ℕ, n₀ ≤ n →
        α * (primorial n : ℝ) ≤ squarefreeCount (primorial n) := by
  obtain ⟨α, hα, hsq⟩ := squarefreeCount_linear_global
  exact ⟨0, α, hα, fun n _ => hsq (primorial n)⟩

/-- Recollement Front 1 : des deux sous-verrous squarefree vers `S1 ≫ q`. -/
theorem S1_linear_on_primorial_from_squarefree
    (h1 : ∃ β : ℝ, 0 < β ∧
      ∀ q : ℕ, β * squarefreeCount q ≤ S1 q)
    (h2 : ∃ n₀ : ℕ, ∃ α : ℝ, 0 < α ∧
      ∀ n : ℕ, n₀ ≤ n →
        α * (primorial n : ℝ) ≤ squarefreeCount (primorial n)) :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * (primorial n : ℝ) ≤ S1 (primorial n) := by
  obtain ⟨β, hβ, hβq⟩ := h1
  obtain ⟨n₀, α, hα, hαn⟩ := h2
  refine ⟨n₀, α * β, mul_pos hα hβ, ?_⟩
  intro n hn
  have hsq := hαn n hn
  have hS := hβq (primorial n)
  nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hβ)]

theorem S1_linear_on_primorial :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * (primorial n : ℝ) ≤ S1 (primorial n) :=
  S1_linear_on_primorial_from_squarefree
    S1_lower_from_squarefree
    squarefreeCount_linear_on_primorial

-- ═══════════════════════════════════════════════════════════
-- §7. Verrous Route C classiques, fermés
-- ═══════════════════════════════════════════════════════════

theorem routeC_main_lower :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * phi (primorial n) ≤ MainTerm (primorial n) := by
  obtain ⟨n₀, A, hA, hS1⟩ := S1_linear_on_primorial
  refine ⟨n₀, A, hA, ?_⟩
  intro n hn
  unfold MainTerm
  have hS := hS1 n hn
  have hq : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hphi_nn : 0 ≤ phi (primorial n) := phi_primorial_nonneg n
  rw [div_mul_eq_mul_div, le_div_iff₀ hq]
  nlinarith [mul_le_mul_of_nonneg_left hS hphi_nn]

theorem routeC_error_upper :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n) := by
  obtain ⟨n₀, θ, hθlt, hθnn, hctrl⟩ := routeC_error_control
  refine ⟨n₀, θ, hθlt, hθnn, ?_⟩
  intro n hn
  rw [errorTerm_decomposition]
  calc
    |Finset.sum (ErrorPieces (primorial n)) (fun d => E (primorial n) d)|
        ≤ Finset.sum (ErrorPieces (primorial n))
            (fun d => |E (primorial n) d|) :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ θ * MainTerm (primorial n) := hctrl n hn

-- ═══════════════════════════════════════════════════════════
-- §8. Recollement Route C
-- ═══════════════════════════════════════════════════════════

theorem routeC_from_main_error
    (hmain : ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * phi (primorial n) ≤ MainTerm (primorial n))
    (herr : ∃ n₁ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₁ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n)) :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n) := by
  obtain ⟨n₀, A, hA, hmain⟩ := hmain
  obtain ⟨n₁, θ, hθ_lt, hθ_nn, herr⟩ := herr
  refine ⟨max n₀ n₁, (1 - θ) * A, mul_pos (by linarith) hA, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := le_trans (le_max_left n₀ n₁) hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_right n₀ n₁) hn
  have hM := hmain n hn₀
  have hE := herr n hn₁
  have hE_lower := (abs_le.mp hE).1
  rw [K_decomposition]
  nlinarith [mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 - θ by linarith)]

-- ═══════════════════════════════════════════════════════════
-- §9. Chaîne complète (A) → (B) → (C)
-- ═══════════════════════════════════════════════════════════

theorem routeC_explicit_core :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n) :=
  routeC_from_main_error routeC_main_lower routeC_error_upper

theorem kappa_explicit_bound
    (hmain : ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n)) :
    ∃ n₀ : ℕ, ∃ lam : ℝ, 0 < lam ∧
      ∀ n : ℕ, n₀ ≤ n → lam ≤ kappa (primorial n) := by
  obtain ⟨n₀, c, hc, hK⟩ := hmain
  refine ⟨n₀, Real.sqrt c, Real.sqrt_pos_of_pos hc, ?_⟩
  intro n hn
  unfold kappa CouretUnification.Arithmetic.kappa
  change Real.sqrt c ≤ Real.sqrt (K (primorial n) / phi (primorial n))
  apply Real.sqrt_le_sqrt
  have hphi : 0 < phi (primorial n) := phi_primorial_pos n
  exact (le_div_iff₀ hphi).mpr (hK n hn)

theorem kappa_eventually_pos
    (hmain : ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n)) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) := by
  obtain ⟨n₀, lam, hlam, hbound⟩ := kappa_explicit_bound hmain
  exact ⟨lam, hlam, Filter.eventually_atTop.mpr ⟨n₀, hbound⟩⟩

theorem kappa_pos_from_routeC :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) :=
  kappa_eventually_pos routeC_explicit_core

-- ═══════════════════════════════════════════════════════════
-- §10. Gouvernance
-- ═══════════════════════════════════════════════════════════

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

end RouteC
end CouretUnification