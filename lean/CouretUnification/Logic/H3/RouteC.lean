import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import CouretUnification.Logic.H3.Arithmetic

/-!
# Route C raffinée — Infrastructure formelle

## Programme Couret-Unification v32.36

Ce fichier formalise la **Route C raffinée** sous forme d'une décomposition
claire du verrou analytique en deux sous-verrous distincts :

1. `routeC_main_lower` :
   le terme principal est uniformément positif le long de la tour primorielle.

2. `routeC_error_upper` :
   le terme d'erreur reste dominé par une fraction `θ < 1` du terme principal.

Le lemme `routeC_from_main_error` est **purement algébrique** et entièrement fermé.
Le triptyque final

- `(A)` `routeC_explicit_core`
- `(B)` `kappa_explicit_bound`
- `(C)` `kappa_eventually_pos`

reste inchangé, mais son verrou central est désormais **factorisé proprement**
en deux problèmes analytiques nommés.

## Statut

Sorry dans ce fichier : 2

- `routeC_main_lower`
- `routeC_error_upper`

Ces deux `sorry` sont des **verrous analytiques réels**, formulés sur les objets
arithmétiques effectifs importés depuis `Arithmetic.lean`.
Il ne s'agit pas de `sorry` d'interface.

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

/-- Euler's totient, imported from `Arithmetic.lean`. -/
noncomputable abbrev phi : ℕ → ℝ := CouretUnification.Arithmetic.phi

/-- Restricted second moment `K(q)`, imported from `Arithmetic.lean`. -/
noncomputable abbrev K : ℕ → ℝ := CouretUnification.Arithmetic.K

/-- Normalized second moment `κ(q)^2 = K(q) / φ(q)`, imported from `Arithmetic.lean`. -/
noncomputable abbrev kappaSq : ℕ → ℝ := CouretUnification.Arithmetic.kappaSq

/-- `κ(q) = √(K(q)/φ(q))`, imported from `Arithmetic.lean`. -/
noncomputable abbrev kappa : ℕ → ℝ := CouretUnification.Arithmetic.kappa

/-- Primorial tower.

Current placeholder definition based on repeated `minFac`.
This is sufficient for the present formal infrastructure, but should later
be replaced by a canonical definition using the ordered sequence of primes. -/
def primorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => primorial n * (Nat.minFac (primorial n + 1))

/-- Positivity of the primorial tower. -/
theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  induction n with
  | zero =>
      simp [primorial]
  | succ n ih =>
      unfold primorial
      exact Nat.mul_pos ih (Nat.minFac_pos _)

/-- Positivity of `φ(primorial n)`. -/
theorem phi_primorial_pos (n : ℕ) : 0 < phi (primorial n) := by
  unfold phi CouretUnification.Arithmetic.phi
  exact Nat.cast_pos.mpr ((Nat.totient_pos).mpr (primorial_pos n))

-- ═══════════════════════════════════════════════════════════
-- §2. Décomposition analytique : terme principal et erreur
-- ═══════════════════════════════════════════════════════════

/-- `S1(q) = Σ_{1 ≤ n ≤ q} M(n)^2`.

This is the unrestricted second moment of the Mertens function. -/
noncomputable def S1 (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (q + 1))
    (fun n => if 0 < n then ((Arithmetic.mertens n : ℤ) : ℝ) ^ 2 else 0)

/-- Main term of Route C:
`MainTerm(q) = (φ(q) / q) · S1(q)`. -/
noncomputable def MainTerm (q : ℕ) : ℝ :=
  (phi q / (q : ℝ)) * S1 q

/-- Error term of Route C, defined by
`ErrorTerm(q) = K(q) - MainTerm(q)`.

By construction, `K = MainTerm + ErrorTerm`. -/
noncomputable def ErrorTerm (q : ℕ) : ℝ :=
  K q - MainTerm q

/-- Tautological decomposition of `K` into its main term and error term. -/
theorem K_decomposition (q : ℕ) : K q = MainTerm q + ErrorTerm q := by
  unfold ErrorTerm
  ring

-- ═══════════════════════════════════════════════════════════
-- §3. Les deux verrous analytiques
-- ═══════════════════════════════════════════════════════════

/-- Analytical lock 1.

Uniform positive lower bound on the main term along the primorial tower.

Heuristically, this corresponds to the asymptotic growth
`S1(q) ≫ q`, ultimately related to the classical second-moment
behavior of the Mertens function. -/
theorem routeC_main_lower :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * phi (primorial n) ≤ MainTerm (primorial n) := by
  sorry

/-- Analytical lock 2.

Relative control of the error term by the main term, with a factor `θ < 1`.

This is the central quantitative ingredient of the refined Route C.
Empirical values discussed in the project are:

- `θ = 0.83` for `q = 30`
- `θ = 0.45` for `q = 210`
- `θ = 0.13` for `q = 2310`
- `θ = 0.02` for `q = 30030`
-/
theorem routeC_error_upper :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n) := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §4. Recollement algébrique (fermé)
-- ═══════════════════════════════════════════════════════════

/-- Pure algebraic recombination:

if the main term is bounded below by `A · φ`,
and the error term is bounded by a relative factor `θ < 1`,
then `K` is bounded below by `((1 - θ)A) · φ`. -/
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
-- §5. Chaîne complète (A) → (B) → (C)
-- ═══════════════════════════════════════════════════════════

/-- Central Route C statement, assembled from the two analytical locks. -/
theorem routeC_explicit_core :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n) :=
  routeC_from_main_error routeC_main_lower routeC_error_upper

/-- Passage from a positive lower bound on `K/φ` to a positive lower bound on `κ`. -/
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

/-- Eventual positivity of `κ` along the primorial tower. -/
theorem kappa_eventually_pos
    (hmain : ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n)) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) := by
  obtain ⟨n₀, lam, hlam, hbound⟩ := kappa_explicit_bound hmain
  exact ⟨lam, hlam, Filter.eventually_atTop.mpr ⟨n₀, hbound⟩⟩

/-- Full Route C conclusion from the assembled core. -/
theorem kappa_pos_from_routeC :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) :=
  kappa_eventually_pos routeC_explicit_core

-- ═══════════════════════════════════════════════════════════
-- §6. Gouvernance
-- ═══════════════════════════════════════════════════════════

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

/-!
## Comptabilité `RouteC.lean` — v32.36

| Objet                     | Statut |
|--------------------------|--------|
| `phi`, `K`, `kappaSq`, `kappa` | Alias vers `Arithmetic.lean` |
| `primorial`             | Défini |
| `primorial_pos`         | **PROUVÉ** |
| `phi_primorial_pos`     | **PROUVÉ** |
| `S1`, `MainTerm`, `ErrorTerm` | Défini |
| `K_decomposition`       | **PROUVÉ** |
| `routeC_main_lower`     | **sorry** |
| `routeC_error_upper`    | **sorry** |
| `routeC_from_main_error`| **PROUVÉ** |
| `routeC_explicit_core`  | **PROUVÉ** (via les deux verrous ci-dessus) |
| `kappa_explicit_bound`  | **PROUVÉ** |
| `kappa_eventually_pos`  | **PROUVÉ** |
| `kappa_pos_from_routeC` | **PROUVÉ** |

Sorry dans ce fichier : 2

- `routeC_main_lower`
- `routeC_error_upper`

Ces deux `sorry` sont des verrous analytiques réels, formulés sur les objets
arithmétiques effectifs du dépôt.

`RHClaimed = false.`
-/

end RouteC
end CouretUnification