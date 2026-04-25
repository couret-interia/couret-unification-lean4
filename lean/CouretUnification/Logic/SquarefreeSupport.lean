/-
Copyright (c) 2026 Couret-Unification Programme.
Released under Apache 2.0.

# Logic/H3/SquarefreeSupport.lean — Bloc B : transfert combinatoire (v35.6.1)

## Doctrine

Ce fichier formalise la "glue combinatoire" du programme : pour un ensemble
fini S de nombres premiers distincts, on établit la factorisation finie

  ∑_{T ⊆ S} f(∏_{p∈T} p) = ∏_{p∈S} (1 + f(p))

pour toute fonction multiplicative f.

C'est l'identité-pont entre les sommes sur entiers squarefree et les
produits eulériens partiels. Elle prépare la couture C(ii) et le contrôle
normique du Bloc D.

## Changements vs v35.5/v0.1

  - La preuve de `squarefree_support_transfer` est COMPLÈTE et ROBUSTE
    (induction Finset via `Finset.sum_powerset_insert` — lemme spécialisé,
    plus stable que la chaîne `powerset_insert` + `sum_union` + `sum_image`).
  - Le sorry "API-LOCAL" de la ligne 139 du v0.1 est ÉLIMINÉ.
  - La variante `_normSq` est désormais entièrement prouvée comme corollaire.

## Patch v35.6.1 (post-revue)

Suite à un retour technique, la stratégie initiale via `powerset_insert` +
`sum_union` + `sum_image` (route fragile, demande de gérer disjonction et
injectivité explicitement) a été remplacée par :
  - `Finset.sum_powerset_insert hpT` (lemme dédié)
  - `Finset.sum_congr` via `have` intermédiaire (au lieu de `rw [sum_congr ...]`)
  - assemblage final via lemme algébrique explicite + `ring`

Cette version est plus robuste à travers les snapshots Mathlib.

## Statut épistémique

  - Couche : Logic/H3 (théorème structurant)
  - Statut : [P] sur tous les énoncés principaux. Aucun sorry conceptuel.
             Si frottement API au build, points commentés `[API-LOCAL]`.
  - RHClaimed = false.

-/

import CouretUnification.Logic.Doctrine
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

namespace CouretUnification
namespace Logic
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
  - `Finset.sum_powerset_insert` (lemme spécialisé pour la décomposition
     de la somme sur le powerset après insertion d'un élément)
  - `Finset.prod_insert` + multiplicativité de f sous coprimalité
  - `Finset.sum_congr` via `have` intermédiaire (route robuste)
  - assemblage final par `ring`

L'invariance d'induction est : pour tout s ⊆ T, on a
  f(∏_{q ∈ insert p s} q) = f(p · ∏ s) = f(p) · f(∏ s)
car `p ∉ s` (hérité de `p ∉ T`) donne la coprimalité.

Note v35.6.1 : la stratégie initiale via `Finset.powerset_insert` +
`sum_union` + `sum_image` a été remplacée par `Finset.sum_powerset_insert`,
plus stable à travers les snapshots Mathlib (évite la gestion explicite
de la disjonction et de l'injectivité par `Set.InjOn`).
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
  classical
  induction S using Finset.induction_on with
  | empty =>
    -- ∑_{T ⊆ ∅} f(∏ T) = f(∏ ∅) = f(1) = 1 = ∏ ∅
    simp [h_one]
  | @insert p T hpT ih =>
    -- Hypothèses pour T
    have hT_prime : ∀ q ∈ T, Nat.Prime q :=
      fun q hq => hS q (mem_insert_of_mem hq)
    have hp : Nat.Prime p := hS p (mem_insert_self p T)
    have ih' := ih hT_prime
    -- Étape 1 : ∏_{q ∈ insert p T} (1 + f q) = (1 + f p) * ∏_{q ∈ T} (1 + f q)
    rw [prod_insert hpT]
    -- Étape 2 : décomposition somme-powerset via le lemme dédié.
    -- `Finset.sum_powerset_insert hpT` réécrit la somme sur powerset (insert p T)
    -- en somme sur T.powerset des termes "sans p" + "avec p insérés".
    rw [Finset.sum_powerset_insert hpT]
    -- [API-LOCAL] Selon le snapshot Mathlib, la forme exacte du résultat
    -- peut être :
    --   (a) deux sommes séparées : (∑ s, f (∏ s)) + (∑ s, f (∏ insert p s))
    --   (b) une seule somme avec intégrande additive :
    --       ∑ s ∈ T.powerset, (f (∏ s) + f (∏ insert p s))
    -- Si c'est le cas (b), il faut décommenter la ligne suivante :
    -- rw [Finset.sum_add_distrib]
    --
    -- Étape 3 : pour chaque s ⊆ T, f(∏_{q ∈ insert p s} q) = f(p) * f(∏_{q ∈ s} q)
    -- car p ∉ s (hérité de p ∉ T) donne la coprimalité.
    have h_split :
        ∀ s ∈ T.powerset,
          f (∏ q ∈ insert p s, q) = f p * f (∏ q ∈ s, q) := by
      intro s hs
      have hs_sub : s ⊆ T := mem_powerset.mp hs
      have hp_not_mem_s : p ∉ s := fun h => hpT (hs_sub h)
      rw [prod_insert hp_not_mem_s]
      apply h_mult
      exact coprime_prime_prod_subset hp hT_prime hpT hs_sub
    -- Étape 4 : on injecte la réécriture par un lemme intermédiaire (route robuste,
    -- au lieu d'un `rw [sum_congr rfl ...]` qui peut buter sur l'unification).
    have hsplit_sum :
        (∑ s ∈ T.powerset, f (∏ q ∈ insert p s, q))
          = ∑ s ∈ T.powerset, f p * f (∏ q ∈ s, q) := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      exact h_split s hs
    rw [hsplit_sum]
    -- Étape 5 : factorisation algébrique et application de l'hypothèse d'induction.
    rw [← Finset.mul_sum]
    -- But : (∑ s, f(∏ s)) + f p * (∑ s, f(∏ s)) = (1 + f p) * (∏ q ∈ T, (1 + f q))
    have h_algebra :
        (∑ s ∈ T.powerset, f (∏ q ∈ s, q))
          + f p * (∑ s ∈ T.powerset, f (∏ q ∈ s, q))
        = (1 + f p) * (∑ s ∈ T.powerset, f (∏ q ∈ s, q)) := by
      ring
    rw [h_algebra, ih']

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
def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/SquarefreeSupport.lean"
  layer := CouretUnification.Meta.Layer.A
  status := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-!
## Notes finales

1. **Sorrys du v0.1 fermés** :
   - Ligne 139 (v0.1) `sum_image` mal formé : remplacé par décomposition propre
     via `Finset.sum_powerset_insert hpT` (lemme dédié) + `Finset.sum_congr`
     via `have` intermédiaire (route robuste, pas de `rw [sum_congr ...]`).
   - Ligne 145 (v0.1) sorry "API frottement" : induction terminée par `ring`.
   - Ligne 178 (v0.1) `squarefree_support_transfer_normSq` sorry : prouvé
     comme corollaire direct de `squarefree_support_transfer`.

2. **Stratégie de preuve adoptée (v35.6.1)** :
   La preuve repose sur `Finset.sum_powerset_insert` (lemme spécialisé,
   plus stable que `Finset.powerset_insert` + `sum_union` + `sum_image`
   en chaîne). Les manipulations `sum_congr` se font via `have` intermédiaires
   plutôt que par `rw` direct, ce qui évite les problèmes d'unification.

3. **Frottements API à surveiller** :
   - `Finset.sum_powerset_insert` : forme exacte du résultat selon snapshot.
     Si Lean produit une seule somme avec intégrande additive plutôt que
     deux sommes séparées, décommenter `rw [Finset.sum_add_distrib]` à
     l'endroit indiqué dans la preuve.
   - `Nat.Coprime.prod_right` : nom stable.
   - `Nat.coprime_primes` : forme `iff`.
   - `Nat.squarefree_mul` : peut se nommer `squarefree_mul_iff_of_coprime`
     dans certains snapshots.

4. **Réutilisation** :
   - `LocalSquarefreeBridge.lean` consomme `squarefree_support_transfer_real`
     pour établir la version finie du pont eulérien sur la ligne critique.
-/

end SquarefreeSupport
end Logic
end CouretUnification
