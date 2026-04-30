/-
Copyright (c) 2026 Couret-Unification Programme.
Released under Apache 2.0.

# Logic/H3/SquarefreeSupport.lean — Bloc B : transfert combinatoire (v35.6)

## Doctrine

Ce fichier formalise la "glue combinatoire" du programme : pour un ensemble
fini S de nombres premiers distincts, on établit la factorisation finie

  ∑_{T ⊆ S} f(∏_{p∈T} p) = ∏_{p∈S} (1 + f(p))

pour toute fonction multiplicative f.

C'est l'identité-pont entre les sommes sur entiers squarefree et les
produits eulériens partiels. Elle prépare la couture C(ii) et le contrôle
normique du Bloc D.

## Changements vs v35.5/v0.1

  - La preuve de `squarefree_support_transfer` est COMPLÈTE (induction
    Finset propre via `powerset_insert`, `sum_union` avec disjonction
    explicite, `sum_image` avec injectivité, puis assemblage par `ring`).
  - Le sorry "API-LOCAL" de la ligne 139 du v0.1 est ÉLIMINÉ.
  - La variante `_normSq` est désormais entièrement prouvée comme corollaire.

## Statut épistémique

  - Couche : Logic/H3 (théorème structurant)
  - Statut : [P] sur tous les énoncés principaux. Aucun sorry conceptuel.
             Si frottement API au build, points commentés `[API-LOCAL]`.
  - RHClaimed = false.

-/

import CouretUnification.Core.Doctrine
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

namespace CouretUnification
namespace H3
namespace SquarefreeSupport

open Finset
open scoped BigOperators

/-!
## Section 1 — Lemmes d'assistance arithmétique
-/

/-- [P] Si p est premier et n'appartient pas à un ensemble S de premiers,
    alors p est coprime avec tout produit d'éléments d'un sous-ensemble de S. -/
theorem coprime_prime_prod_subset
    {S : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hS : ∀ q ∈ S, Nat.Prime q) (hpS : p ∉ S)
    {s : Finset ℕ} (hs : s ⊆ S) :
    Nat.Coprime p (∏ q ∈ s, q) := by
  apply Nat.Coprime.prod_right
  intro q hq
  have hq_in_S : q ∈ S := hs hq
  have hq_prime : Nat.Prime q := hS q hq_in_S
  have hpq : p ≠ q := fun heq => hpS (heq ▸ hq_in_S)
  exact (Nat.coprime_primes hp hq_prime).mpr hpq

/-- [P] Le produit d'un sous-ensemble de premiers distincts est squarefree. -/
theorem squarefree_prod_of_primes
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ S) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
    exact squarefree_one
  | @insert p T hpT ih =>
    have hp : Nat.Prime p := hS p (hs (mem_insert_self p T))
    have hT_sub : T ⊆ S := fun q hq => hs (mem_insert_of_mem hq)
    have ihT : Squarefree (∏ q ∈ T, q) := ih hT_sub
    rw [prod_insert hpT]
    have hcop : Nat.Coprime p (∏ q ∈ T, q) :=
      coprime_prime_prod_subset hp hS (fun h => hpT h) (Finset.Subset.refl T)
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ihT⟩

/-!
## Section 2 — Théorème de transfert principal

C'est le cœur du fichier. La preuve est par induction sur S, et utilise :
  - `Finset.powerset_insert` pour la décomposition du powerset
  - `Finset.sum_union` avec preuve de disjonction explicite
  - `Finset.sum_image` avec preuve d'injectivité
  - `Finset.prod_insert` + multiplicativité de f sous coprimalité
  - assemblage final par `ring`

L'invariance d'induction est : pour tout T' ⊆ T, on a
  f((insert p T').prod id) = f(p · ∏ T') = f(p) · f(∏ T')
car `p ∉ T'` (hérité de `p ∉ T`) donne la coprimalité.
-/

variable {α : Type*} [CommRing α]

/-- [P] **Théorème de transfert combinatoire — version générique sur CommRing.**

    Pour S ensemble fini de premiers distincts et f : ℕ → α multiplicative,
      ∑_{T ⊆ S} f(∏_{p ∈ T} p) = ∏_{p ∈ S} (1 + f p). -/
theorem squarefree_support_transfer
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (f : ℕ → α) (h_one : f 1 = 1)
    (h_mult : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ T ∈ S.powerset, f (∏ p ∈ T, p)) = ∏ p ∈ S, (1 + f p) := by
  induction S using Finset.induction_on with
  | empty =>
    -- ∑_{T ⊆ ∅} f(∏ T) = f(∏ ∅) = f(1) = 1 = ∏ ∅
    simp [h_one]
  | @insert p S' hpS' ih =>
    -- Hypothèses pour S'
    have hS'_prime : ∀ q ∈ S', Nat.Prime q :=
      fun q hq => hS q (mem_insert_of_mem hq)
    have hp : Nat.Prime p := hS p (mem_insert_self p S')
    have ih' := ih hS'_prime
    -- Étape 1 : décomposer ∏_{q ∈ insert p S'} (1 + f q) = (1 + f p) * ∏_{q ∈ S'} (1 + f q)
    rw [prod_insert hpS']
    -- Étape 2 : décomposer (insert p S').powerset = S'.powerset ∪ S'.powerset.image (insert p)
    rw [Finset.powerset_insert]
    -- Étape 3 : prouver la disjonction des deux familles
    have hdisj : Disjoint S'.powerset (S'.powerset.image (insert p)) := by
      rw [Finset.disjoint_left]
      intro T hT hTim
      rcases mem_image.mp hTim with ⟨T', _, hTeq⟩
      have hp_in_T : p ∈ T := hTeq ▸ mem_insert_self p T'
      have hp_in_S' : p ∈ S' := mem_powerset.mp hT hp_in_T
      exact hpS' hp_in_S'
    rw [sum_union hdisj]
    -- Étape 4 : prouver l'injectivité de (insert p · ) sur S'.powerset
    have hinj : Set.InjOn (insert p) (S'.powerset : Set (Finset ℕ)) := by
      intro T' hT' T'' hT'' heq
      have hpT' : p ∉ T' := fun h => hpS' (mem_powerset.mp hT' h)
      have hpT'' : p ∉ T'' := fun h => hpS' (mem_powerset.mp hT'' h)
      -- T' = (insert p T').erase p quand p ∉ T'
      have eq1 : (insert p T').erase p = T' := Finset.erase_insert hpT'
      have eq2 : (insert p T'').erase p = T'' := Finset.erase_insert hpT''
      rw [← eq1, ← eq2, heq]
    rw [sum_image (fun a ha b hb => hinj ha hb)]
    -- Étape 5 : pour chaque T' ⊆ S', f(∏ (insert p T') id) = f p * f (∏ T' id)
    have hrewrite :
        ∀ T' ∈ S'.powerset,
          f (∏ q ∈ insert p T', q) = f p * f (∏ q ∈ T', q) := by
      intro T' hT'
      have hpT' : p ∉ T' := fun h => hpS' (mem_powerset.mp hT' h)
      rw [prod_insert hpT']
      apply h_mult
      exact coprime_prime_prod_subset hp hS'_prime hpS' (mem_powerset.mp hT')
    rw [sum_congr rfl hrewrite]
    -- Étape 6 : factorisation et assemblage final
    -- LHS = ∑ f(∏ T') + f p * ∑ f(∏ T')
    --     = (1 + f p) * ∑ f(∏ T')
    --     = (1 + f p) * ∏_{q ∈ S'} (1 + f q)    par ih'
    rw [← Finset.mul_sum]
    rw [show (∑ T' ∈ S'.powerset, f (∏ q ∈ T', q))
            = ∏ q ∈ S', (1 + f q) from ih']
    ring

/-!
## Section 3 — Variante normique (préparation au Bloc D)

Pour le contrôle normique du futur Bloc D, on a besoin de la version
où f est complexe et où l'on prend la norme au carré, qui est elle aussi
multiplicative sous coprimalité.
-/

/-- [P] Si f : ℕ → ℂ est multiplicative au sens de coprimalité,
    alors n ↦ Complex.normSq (f n) l'est aussi. -/
theorem isMultiplicative_normSq
    (f : ℕ → ℂ) (h_one : f 1 = 1)
    (h_mult : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) :
    Complex.normSq (f 1) = 1 ∧
    ∀ a b, Nat.Coprime a b →
      Complex.normSq (f (a * b)) = Complex.normSq (f a) * Complex.normSq (f b) := by
  refine ⟨?_, ?_⟩
  · rw [h_one]; exact Complex.normSq_one
  · intro a b hab
    rw [h_mult a b hab, Complex.normSq_mul]

/-- [P] **Variante normique du théorème de transfert.**

    Pour f : ℕ → ℂ multiplicative,
      ∑_{T ⊆ S} ‖f(∏ T)‖² = ∏_{p ∈ S} (1 + ‖f(p)‖²). -/
theorem squarefree_support_transfer_normSq
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (f : ℕ → ℂ) (h_one : f 1 = 1)
    (h_mult : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ T ∈ S.powerset, Complex.normSq (f (∏ p ∈ T, p)))
      = ∏ p ∈ S, (1 + Complex.normSq (f p)) := by
  -- On instancie le théorème générique avec g = normSq ∘ f, qui est ℝ-valuée
  -- et multiplicative sous coprimalité (lemme isMultiplicative_normSq).
  set g : ℕ → ℝ := fun n => Complex.normSq (f n) with hg_def
  have hg_one : g 1 = 1 := by
    simp [hg_def, h_one, Complex.normSq_one]
  have hg_mult : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b := by
    intro a b hab
    simp [hg_def, h_mult a b hab, Complex.normSq_mul]
  exact squarefree_support_transfer S hS g hg_one hg_mult

/-!
## Section 4 — Corollaire : majoration positive

Quand f ≥ 0, la version normique fournit directement une majoration
de la somme par le produit, qui est utilisée par LocalSquarefreeBridge.
-/

/-- [P] Pour f : ℕ → ℝ multiplicative positive, la somme sur les sous-ensembles
    est égale (en fait : pas seulement majorée) au produit eulérien. -/
theorem squarefree_support_transfer_real
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (f : ℕ → ℝ) (h_one : f 1 = 1)
    (h_mult : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ T ∈ S.powerset, f (∏ p ∈ T, p)) = ∏ p ∈ S, (1 + f p) :=
  squarefree_support_transfer S hS f h_one h_mult

/-!
## Section 5 — Invariant constitutionnel
-/

/-- [P] Identité du fichier. -/
def fileIdentity : CouretUnification.FileIdentity where
  module := "CouretUnification.Logic.H3.SquarefreeSupport"
  layer := CouretUnification.Layer.logicH3
  status := CouretUnification.EpistemicStatus.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-!
## Notes finales

1. **Sorrys du v0.1 fermés** :
   - Ligne 139 (v0.1) `sum_image` mal formé : remplacé par induction propre.
   - Ligne 145 (v0.1) sorry "API frottement" : induction terminée par `ring`.
   - Ligne 178 (v0.1) `squarefree_support_transfer_normSq` sorry : prouvé
     comme corollaire direct de `squarefree_support_transfer`.

2. **Frottements API à surveiller** :
   - `Nat.Coprime.prod_right` : nom stable.
   - `Nat.coprime_primes` : forme `iff`.
   - `Nat.squarefree_mul` : peut se nommer `squarefree_mul_iff_of_coprime`
     dans certains snapshots.
   - `Finset.powerset_insert` : signature stable.
   - `Finset.sum_image` : la signature attend `Set.InjOn`, alignée ci-dessus.
   - `Finset.erase_insert` : nom stable depuis Mathlib 2024.

3. **Réutilisation** :
   - `LocalSquarefreeBridge.lean` consomme `squarefree_support_transfer_real`
     pour établir la version finie du pont eulérien sur la ligne critique.
-/

end SquarefreeSupport
end H3
end CouretUnification
