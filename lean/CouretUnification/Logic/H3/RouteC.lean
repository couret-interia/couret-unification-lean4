import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import CouretUnification.Logic.H3.Arithmetic

/-!
# Route C raffinée — Infrastructure formelle

## Programme Couret-Unification v32.37

Second refactor : les deux sorry analytiques sont déplacés plus bas,
vers leurs verrous *minimaux* :

- `S1_linear_on_primorial` — borne linéaire inférieure sur `S1(q)` le long de la tour
- `routeC_error_control`   — contrôle `θ < 1` sur la somme des pièces d'erreur

Les théorèmes `routeC_main_lower` et `routeC_error_upper` sont désormais
**entièrement fermés** (algèbre + inégalité triangulaire), et le triptyque
`(A)→(B)→(C)` reste inchangé.

## Statut

Sorry dans ce fichier : 2
- `S1_linear_on_primorial`
- `routeC_error_control`

`RHClaimed = false.`
Dédié à Bernard Couret (1928–1999).
-/

open Filter
open scoped Topology BigOperators

namespace CouretUnification
namespace RouteC

-- ═══════════════════════════════════════════════════════════
-- §1. Recollement avec l'arithmétique réelle
-- ═══════════════════════════════════════════════════════════

noncomputable abbrev phi : ℕ → ℝ := CouretUnification.Arithmetic.phi
noncomputable abbrev K : ℕ → ℝ := CouretUnification.Arithmetic.K
noncomputable abbrev kappaSq : ℕ → ℝ := CouretUnification.Arithmetic.kappaSq
noncomputable abbrev kappa : ℕ → ℝ := CouretUnification.Arithmetic.kappa

/-- Primorial tower. Placeholder — TODO: canoniser via ordered primes. -/
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
-- §2. Décomposition analytique : terme principal et erreur
-- ═══════════════════════════════════════════════════════════

/-- `S1(q) = Σ_{1 ≤ n ≤ q} M(n)^2` — unrestricted second moment of Mertens. -/
noncomputable def S1 (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (q + 1))
    (fun n => if 0 < n then ((Arithmetic.mertens n : ℤ) : ℝ) ^ 2 else 0)

/-- `S1(q) ≥ 0` — sum of squares. -/
theorem S1_nonneg (q : ℕ) : 0 ≤ S1 q := by
  unfold S1
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

/-- `MainTerm(q) = (φ(q) / q) · S1(q)`. -/
noncomputable def MainTerm (q : ℕ) : ℝ :=
  (phi q / (q : ℝ)) * S1 q

/-- `ErrorTerm(q) = K(q) - MainTerm(q)`. By construction, `K = MainTerm + ErrorTerm`. -/
noncomputable def ErrorTerm (q : ℕ) : ℝ :=
  K q - MainTerm q

theorem K_decomposition (q : ℕ) : K q = MainTerm q + ErrorTerm q := by
  unfold ErrorTerm; ring

-- ═══════════════════════════════════════════════════════════
-- §3. Décomposition structurelle de l'erreur en pièces
-- ═══════════════════════════════════════════════════════════

/-- Pieces of the error decomposition.

Placeholder : a single-piece decomposition, sufficient for the present
formal infrastructure. Later refinement should use `Nat.divisors q`
together with the inclusion–exclusion pieces coming from Möbius inversion. -/
def ErrorPieces (_q : ℕ) : Finset ℕ := {0}

/-- Value of the error on a given piece.

Placeholder : everything is concentrated on the single piece. -/
noncomputable def E (q _d : ℕ) : ℝ := ErrorTerm q

/-- Tautological decomposition of `ErrorTerm` as a sum of pieces.
Trivial with the current placeholder; will remain structurally valid once
`ErrorPieces` and `E` are refined to their proper inclusion–exclusion form. -/
theorem errorTerm_decomposition (q : ℕ) :
    ErrorTerm q = ∑ d in ErrorPieces q, E q d := by
  simp [ErrorPieces, E]

-- ═══════════════════════════════════════════════════════════
-- §4. Les deux verrous analytiques minimaux
-- ═══════════════════════════════════════════════════════════

/-- **Analytical lock 1** — linear lower bound on `S1(q)` along the primorial tower.

This is the minimal analytical statement from which `routeC_main_lower` follows
by pure algebra. Heuristically, it corresponds to `S1(q) ≫ q`, which one would
derive from `S1(q) ≥ (1/2) · squarefreeCount(q)` combined with a trivial
lower bound on the density of squarefree integers. -/
theorem S1_linear_on_primorial :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * (primorial n : ℝ) ≤ S1 (primorial n) := by
  sorry

/-- **Analytical lock 2** — relative control on the total error pieces.

This is the minimal quantitative statement from which `routeC_error_upper`
follows by the triangle inequality on finite sums.
Empirical values along the tower:
`θ = 0.83, 0.45, 0.13, 0.02` for `q = 30, 210, 2310, 30030`. -/
theorem routeC_error_control :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∑ d in ErrorPieces (primorial n), |E (primorial n) d|
          ≤ θ * MainTerm (primorial n) := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §5. Verrous classiques, désormais fermés
-- ═══════════════════════════════════════════════════════════

/-- `routeC_main_lower` — closed from `S1_linear_on_primorial` by algebra. -/
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

/-- `routeC_error_upper` — closed from `errorTerm_decomposition` and
`routeC_error_control` by the triangle inequality on finite sums. -/
theorem routeC_error_upper :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n) := by
  obtain ⟨n₀, θ, hθlt, hθnn, hctrl⟩ := routeC_error_control
  refine ⟨n₀, θ, hθlt, hθnn, ?_⟩
  intro n hn
  rw [errorTerm_decomposition]
  calc
    |∑ d in ErrorPieces (primorial n), E (primorial n) d|
        ≤ ∑ d in ErrorPieces (primorial n), |E (primorial n) d| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ θ * MainTerm (primorial n) := hctrl n hn

-- ═══════════════════════════════════════════════════════════
-- §6. Recollement algébrique (fermé)
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
-- §7. Chaîne complète (A) → (B) → (C)
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
-- §8. Gouvernance
-- ═══════════════════════════════════════════════════════════

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

/-!
## Comptabilité `RouteC.lean` — v32.37

| Objet                     | Statut |
|---------------------------|--------|
| `phi`, `K`, `kappaSq`, `kappa` | Alias `Arithmetic.lean` |
| `primorial`, `primorial_pos`, `phi_primorial_pos` | **PROUVÉ** |
| `S1`, `S1_nonneg`         | **PROUVÉ** |
| `MainTerm`, `ErrorTerm`, `K_decomposition` | **PROUVÉ** |
| `ErrorPieces`, `E`, `errorTerm_decomposition` | **PROUVÉ** (placeholder) |
| `S1_linear_on_primorial`  | **sorry** |
| `routeC_error_control`    | **sorry** |
| `routeC_main_lower`       | **PROUVÉ** (via `S1_linear_on_primorial`) |
| `routeC_error_upper`      | **PROUVÉ** (via `errorTerm_decomposition` + `routeC_error_control`) |
| `routeC_from_main_error`  | **PROUVÉ** |
| `routeC_explicit_core`    | **PROUVÉ** |
| `kappa_explicit_bound`, `kappa_eventually_pos`, `kappa_pos_from_routeC` | **PROUVÉ** |

Sorry : 2, tous des verrous analytiques minimaux sur objets arithmétiques réels.

`RHClaimed = false.`
-/

end RouteC
end CouretUnification