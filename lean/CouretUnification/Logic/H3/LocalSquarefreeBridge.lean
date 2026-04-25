/-
Couret-Unification — Logic/H3/LocalSquarefreeBridge.lean
Version v35.5 — 22 avril 2026

Layer     : CouretUnification.Logic.H3
Role      : Raccord entre LocalFactor (E1) et SquarefreeSupport (B).
Purpose   : Établir la version finie du pont eulérien sur la ligne critique.

Statuts épistémiques :
  [P] local_squarefree_bridge_finite   — pont local-squarefree fini
  [O] (explicite) le passage au produit infini et le recollement avec ξ

Invariant : RHClaimed = false.
Ce fichier **ne prétend pas** fermer le pont eulérien global. Il ferme
strictement la version finie du pont, sur primesBelow X, pour X fini.
Le passage à la limite X → ∞ est explicitement laissé ouvert et
appartient aux briques E3/E4 du cahier des charges EulerCompletion,
elles-mêmes équivalentes (en partie) à Lock 3 fort.
-/

import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.SquarefreeSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

namespace CouretUnification.Logic.H3

open Finset
open scoped BigOperators

/-!
## Préliminaires sur f(n)/√n

On manipule des fonctions de la forme g(n) = f(n)/√n où f est
multiplicative positive. On vérifie que g reste multiplicative si f l'est.
-/

/-- Si f est multiplicative ℕ → ℝ, alors n ↦ f(n)/√n aussi. -/
lemma multiplicative_div_sqrt
    (f : ℕ → ℝ)
    (h1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (fun n => f n / Real.sqrt n) 1 = 1 ∧
    ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      (fun n => f n / Real.sqrt n) (a * b)
        = (fun n => f n / Real.sqrt n) a * (fun n => f n / Real.sqrt n) b := by
  refine ⟨?_, ?_⟩
  · simp [h1, Real.sqrt_one]
  · intros a b ha hb hcop
    simp only
    rw [hmul a b hcop]
    -- f(a*b)/√(a*b) = (f a * f b) / (√a * √b) = (f a / √a) * (f b / √b)
    have hab_pos : 0 < a * b := Nat.mul_pos ha hb
    have ha_nn : (0 : ℝ) ≤ a := by exact_mod_cast Nat.zero_le a
    have hb_nn : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
    rw [show ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) from by push_cast; ring,
        Real.sqrt_mul ha_nn]
    field_simp

/-!
## Version finie du pont local-squarefree
-/

/-- [P] **Version finie du pont eulérien sur la ligne critique.**

Pour tout X ≥ 0 et toute fonction arithmétique f : ℕ → ℝ multiplicative
positive bornée, la somme sur les entiers squarefree n ≤ X de f(n)/√n
est bornée par le produit eulérien local sur primesBelow X.

Ceci est la conséquence directe de :
  1. `squarefree_sum_le_prod_real` (transfert combinatoire B)
  2. La multiplicativité préservée par n ↦ f(n)/√n
  3. (Optionnel) les bornes locales de `LocalFactor` si l'on veut
     raffiner par un majorant uniforme.

**Ce théorème ne dit RIEN sur :**
- La limite X → ∞ (verrou E3)
- Le recollement avec ξ (verrou E4 ≡ Lock 3 fort)
- La convergence du produit infini

Ces frontières sont documentées dans le cahier des charges EulerCompletion. -/
theorem local_squarefree_bridge_finite
    (X : ℝ) (hX : 0 ≤ X) (f : ℕ → ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (h1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ n ∈ (Finset.range (Nat.floor X + 1)).filter
            (fun n => n.Squarefree ∧ (n : ℝ) ≤ X),
      f n / Real.sqrt n)
      ≤ ∏ p ∈ primesBelow X, (1 + f p / Real.sqrt p) := by
  -- Définir g(n) = f(n) / √n
  set g : ℕ → ℝ := fun n => f n / Real.sqrt n with hg_def
  -- g est positive si f l'est
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    simp only [hg_def]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0, Real.sqrt_zero]
    · have : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
      exact div_nonneg (hf_nonneg n) this
  -- g(1) = f(1) / √1 = 1 / 1 = 1
  have hg_one : g 1 = 1 := by
    simp [hg_def, h1, Real.sqrt_one]
  -- g est multiplicative sur les coprimes positifs
  -- (on évite le cas 0 * 0 = 0 par hypothèse gcd(a,b) = 1 qui exclut a = b = 0)
  have hg_mul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b := by
    intros a b hcop
    -- Cas a = 0 : coprime 0 b ⟹ b = 1, donc g(0·1) = g(0) = 0 = g(0)·g(1) ✓
    -- Cas b = 0 : symétrique
    -- Cas a, b > 0 : application directe de la multiplicativité
    by_cases ha : a = 0
    · subst ha
      -- coprime 0 b ⟺ b = 1
      have hb : b = 1 := by
        have := Nat.coprime_zero_left.mp hcop
        exact this
      subst hb
      simp [hg_def, h1, Real.sqrt_one]
    · by_cases hb : b = 0
      · subst hb
        have ha1 : a = 1 := by
          have := Nat.coprime_zero_right.mp hcop
          exact this
        subst ha1
        simp [hg_def, h1, Real.sqrt_one]
      · -- a, b > 0
        have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
        have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
        have ha_nn : (0 : ℝ) ≤ a := by exact_mod_cast Nat.zero_le a
        have hb_nn : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
        simp only [hg_def]
        rw [hmul a b hcop]
        rw [show ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) from by push_cast; ring]
        rw [Real.sqrt_mul ha_nn]
        field_simp
  -- Application directe de squarefree_sum_le_prod_real à g
  exact squarefree_sum_le_prod_real X hX g hg_nonneg hg_one hg_mul

/-!
## Frontière avec les briques E3/E4 — explicitement ouverte

Les théorèmes qui suivraient — passage à X → ∞, convergence du produit infini,
recollement avec ξ — **n'apparaissent pas dans ce fichier**.

Les raisons sont documentées dans le cahier des charges EulerCompletion :
- E2 (minoration du dénominateur det₂) est bloquée par l'absence d'infrastructure
  Mathlib standard pour les déterminants régularisés.
- E3 (convergence du produit infini) dépend de E1 ET E2.
- E4 (identification avec ξ) ≡ Lock 3 fort.

**Toute tentative de fermer ces verrous dans ce fichier serait une violation
de l'invariant RHClaimed = false.**

La frontière est maintenue.
-/

/-!
## Lemme de raccord vers LocalFactor (optionnel, non utilisé dans la preuve principale)

Ce lemme n'est pas nécessaire pour `local_squarefree_bridge_finite`, mais il
expose explicitement le lien avec LocalFactor pour référence future.
-/

/-- [P] Cohérence : pour p premier et t ∈ ℝ, le facteur local |1 - e^(it log p)/√p|²
est borné par (1 + 1/√p)², ce qui est la borne utilisée implicitement dans
les estimations de produit eulérien local. -/
lemma local_factor_bound_for_bridge
    {p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    Complex.normSq (1 - ((Real.sqrt p)⁻¹ : ℂ) *
                      Complex.exp ((t * Real.log p : ℂ) * Complex.I))
      ≤ (1 + (Real.sqrt p)⁻¹) ^ 2 :=
  (local_factor_prime_inv_sqrt_bounds hp t).2

end CouretUnification.Logic.H3
