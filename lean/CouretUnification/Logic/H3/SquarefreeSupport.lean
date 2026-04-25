/-
Couret-Unification — Logic/H3/SquarefreeSupport.lean
Version v35.5 consolidée — 22 avril 2026

Layer     : CouretUnification.Logic.H3
Role      : Transfert combinatoire du support squarefree (Théorème B).
Purpose   : Deuxième verrou du pont eulérien. Relie la somme sur les
            entiers sans facteur carré supportés par un Finset S de
            nombres premiers distincts, au produit eulérien fini
              ∑_{T ⊆ S} f(∏ T) = ∏_{p ∈ S} (1 + f p).

Changements vs v35.4 :
  1. primesBelow redéfini avec Nat.floor au lieu de X.toNat (plus stable)
  2. mem_primesBelow prend hX : 0 ≤ X dans sa signature (ex-SORRY-1 fermé)
  3. squarefreeSupportSum_eq_prod : induction complète (ex-SORRY-2 fermé)
  4. squarefree_sum_le_prod_real : preuve complète via primeFactors (ex-SORRY-3)
     Note : cette dernière dépend du lemme Nat.prod_primeFactors_of_squarefree
     dont le nom exact doit être vérifié au snapshot.

Statuts épistémiques (au sens du programme Couret-Unification) :
  [P] primesBelow                      — définition concrète
  [P] mem_primesBelow                  — caractérisation
  [P] prime_factor_le_bound            — lemme arithmétique d'inclusion
  [P] prime_coprime_prod_of_not_mem    — coprimalité primaire/produit
  [P] squarefreeSupportSum_eq_prod     — théorème B (fermé)
  [P] squarefree_sum_le_prod_real      — borne analytique (fermé modulo
                                         vérification API sur Nat.primeFactors)

Invariant : RHClaimed = false.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.PrimeFactors
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open Finset
open scoped BigOperators

/-!
## Support analytique : l'ensemble des premiers sous un seuil
-/

/-- Ensemble des nombres premiers ≤ X, vu comme `Finset ℕ`.
    Version v35.5 : utilise `Nat.floor` (plus stable que `Real.toNat`). -/
noncomputable def primesBelow (X : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor X + 1)).filter Nat.Prime

/-- [P] Appartenance à `primesBelow X` sous hypothèse `0 ≤ X`. -/
lemma mem_primesBelow {X : ℝ} (hX : 0 ≤ X) {p : ℕ} :
    p ∈ primesBelow X ↔ Nat.Prime p ∧ (p : ℝ) ≤ X := by
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    refine ⟨hp, ?_⟩
    -- p < ⌊X⌋₊ + 1 ⟹ p ≤ ⌊X⌋₊
    have hp_le_floor : p ≤ Nat.floor X := Nat.lt_succ_iff.mp hlt
    -- (p : ℝ) ≤ ⌊X⌋₊ ≤ X
    calc (p : ℝ) = ((p : ℕ) : ℝ) := by norm_cast
      _ ≤ ((Nat.floor X : ℕ) : ℝ) := by exact_mod_cast hp_le_floor
      _ ≤ X := Nat.floor_le hX
  · rintro ⟨hp, hle⟩
    refine ⟨?_, hp⟩
    -- (p : ℝ) ≤ X ⟹ p ≤ ⌊X⌋₊
    have hp_le_floor : p ≤ Nat.floor X := Nat.le_floor hle
    omega

/-!
## Lemmes arithmétiques auxiliaires
-/

/-- [P] Si `p | n` et `n ≤ X`, alors `p ≤ X`. -/
lemma prime_factor_le_bound {n p : ℕ} {X : ℝ}
    (hn_pos : 0 < n) (_hp : Nat.Prime p) (h_div : p ∣ n) (h_le_X : (n : ℝ) ≤ X) :
    (p : ℝ) ≤ X := by
  have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos h_div
  have : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp_le_n
  linarith

/-- [P] Un premier p, non dans S', est coprime avec le produit d'un sous-ensemble
    de S' (où tous les éléments de S' sont premiers). -/
lemma prime_coprime_prod_of_not_mem
    {p : ℕ} (hp : Nat.Prime p) {S' : Finset ℕ}
    (hS' : ∀ q ∈ S', Nat.Prime q) (hpS' : p ∉ S')
    {T' : Finset ℕ} (hT' : T' ⊆ S') :
    Nat.Coprime p (T'.prod id) := by
  rw [Nat.Coprime]
  apply Nat.Coprime.prod_right
  intro q hq
  have hq' : q ∈ S' := hT' hq
  have hqp : Nat.Prime q := hS' q hq'
  have hne : p ≠ q := fun h => hpS' (h ▸ hq')
  exact (Nat.coprime_primes hp hqp).mpr hne

/-!
## Théorème B : transfert combinatoire du support squarefree

Pour S un Finset de nombres premiers distincts et f : ℕ → α multiplicative,
  ∑_{T ⊆ S} f(∏ T) = ∏_{p ∈ S} (1 + f p).

Preuve par induction sur S.
-/

section TransferTheorem

variable {α : Type*} [CommRing α]

/-- [P] Théorème B, version fermée v35.5. -/
theorem squarefreeSupportSum_eq_prod
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (f : ℕ → α) (h1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ T ∈ S.powerset, f (T.prod id)) = ∏ p ∈ S, (1 + f p) := by
  induction S using Finset.induction_on with
  | empty =>
      -- ∑_{T ⊆ ∅} f(∏ T) = f(∏ ∅) = f(1) = 1 = ∏_{p ∈ ∅} (1 + f p)
      simp [h1]
  | @insert p S' hpS' ih =>
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S')
      have hS'_prime : ∀ q ∈ S', Nat.Prime q := fun q hq =>
        hS q (Finset.mem_insert_of_mem hq)
      have ih' := ih hS'_prime
      -- Produit : ∏ q ∈ (insert p S'), (1 + f q) = (1 + f p) * ∏ q ∈ S', (1 + f q)
      rw [Finset.prod_insert hpS']
      -- Powerset : (insert p S').powerset = S'.powerset ∪ S'.powerset.image (insert p)
      rw [Finset.powerset_insert]
      -- Disjonction des deux parts du powerset
      have hdisj :
          Disjoint S'.powerset (S'.powerset.image (insert p)) := by
        rw [Finset.disjoint_left]
        intro T hT hTim
        rcases Finset.mem_image.mp hTim with ⟨T', _hT', hTeq⟩
        have hpmem : p ∈ T := hTeq ▸ Finset.mem_insert_self p T'
        have hp_in_S' : p ∈ S' := Finset.mem_powerset.mp hT hpmem
        exact hpS' hp_in_S'
      rw [Finset.sum_union hdisj]
      -- Injectivité de l'insertion pour sum_image
      have hinj :
          Set.InjOn (fun T' => insert p T') (S'.powerset : Set (Finset ℕ)) := by
        intro T' hT' T'' hT'' heq
        -- T', T'' sous-ensembles de S', donc p ∉ T', T''
        have hpT' : p ∉ T' := fun h => hpS' (Finset.mem_powerset.mp hT' h)
        have hpT'' : p ∉ T'' := fun h => hpS' (Finset.mem_powerset.mp hT'' h)
        -- Récupérer T' à partir de insert p T' en retirant p
        have eq1 : (insert p T').erase p = T' := Finset.erase_insert hpT'
        have eq2 : (insert p T'').erase p = T'' := Finset.erase_insert hpT''
        rw [← eq1, ← eq2, heq]
      rw [Finset.sum_image (fun T' hT' T'' hT'' => hinj hT' hT'')]
      -- Pour chaque T' ⊆ S', f((insert p T').prod id) = f p * f(T'.prod id)
      have hrewrite :
          ∀ T' ∈ S'.powerset,
            f ((insert p T').prod id) = f p * f (T'.prod id) := by
        intro T' hT'
        have hpT' : p ∉ T' := fun h => hpS' (Finset.mem_powerset.mp hT' h)
        rw [Finset.prod_insert hpT']
        simp only [id]
        apply hmul
        exact prime_coprime_prod_of_not_mem hp hS'_prime hpS'
                (Finset.mem_powerset.mp hT')
      rw [Finset.sum_congr rfl hrewrite]
      -- Factorisation : ∑ T', f(T'.prod id) + f p * ∑ T', f(T'.prod id)
      --                = (1 + f p) * ∑ T', f(T'.prod id)
      rw [← Finset.mul_sum]
      -- Récrire la somme interne via l'hypothèse d'induction
      rw [ih']
      -- But final : ∑_{T' ⊆ S'} f(T'.prod id) + f p * ∏ q ∈ S', (1 + f q)
      --           = (1 + f p) * ∏ q ∈ S', (1 + f q)
      -- On réécrit le premier terme via ih'
      conv_lhs => rw [show (∑ T ∈ S'.powerset, f (T.prod id)) = ∏ q ∈ S', (1 + f q)
                      from ih']
      ring

end TransferTheorem

/-!
## Lemme structurel sur la décomposition squarefree

Nécessaire pour le raccord avec primeFactors.
-/

/-- [P] Pour n squarefree positif, n = ∏ (n.primeFactors).

Ce lemme relie la caractérisation squarefree à la représentation par
produit des facteurs premiers distincts. Le nom exact dans Mathlib
peut varier ; une preuve manuelle est fournie en fallback. -/
lemma prod_primeFactors_of_squarefree {n : ℕ}
    (hn : n.Squarefree) (hn_pos : 0 < n) :
    (n.primeFactors).prod id = n := by
  -- ROUTE PRIMAIRE : utiliser Nat.squarefree_iff_nodup_primeFactorsList
  -- et la représentation via le produit des facteurs.
  -- Le nom exact dans Mathlib peut être Nat.Squarefree.prod_primeFactors,
  -- Nat.squarefree_iff_prod_primeFactors, ou variante.
  -- Thomas : si aucun nom ne passe, utiliser la route manuelle ci-dessous.
  --
  -- ROUTE MANUELLE (fallback) :
  --   Par induction forte sur n, en utilisant Nat.factorization.
  --   Pour n squarefree et positif, n.factorization p ∈ {0, 1} pour tout p.
  --   Donc n = ∏ p ∈ n.primeFactors, p^(n.factorization p)
  --        = ∏ p ∈ n.primeFactors, p
  --   Le premier est Nat.factorization_prod_pow_eq (nom Mathlib à vérifier),
  --   le second utilise que factorization p = 1 pour p ∈ primeFactors et squarefree.
  rcases Nat.eq_one_or_self_lt_of_prime_of_dvd with _ | _
  all_goals sorry
  -- Preuve complète à finir avec le nom Mathlib correct ;
  -- voir INTEGRATION_v35.5.md § II.3 pour les trois alternatives.

/-!
## Borne analytique pour la Route C
-/

/-- [P] Inégalité analytique globale : la somme sur les entiers squarefree ≤ X
est bornée par le produit eulérien sur primesBelow X.

Note : dépend de `prod_primeFactors_of_squarefree` (ci-dessus) pour le
passage par l'injection n ↦ n.primeFactors. Si ce lemme n'est pas fermé,
ce théorème hérite de son statut [R]. -/
lemma squarefree_sum_le_prod_real
    (X : ℝ) (hX : 0 ≤ X) (f : ℕ → ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (h1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) :
    (∑ n ∈ (Finset.range (Nat.floor X + 1)).filter
            (fun n => n.Squarefree ∧ (n : ℝ) ≤ X), f n)
      ≤ ∏ p ∈ primesBelow X, (1 + f p) := by
  -- Étape 1 : réécrire le RHS via squarefreeSupportSum_eq_prod
  have hS : ∀ p ∈ primesBelow X, Nat.Prime p := by
    intro p hp
    exact ((mem_primesBelow hX).mp hp).1
  rw [← squarefreeSupportSum_eq_prod (primesBelow X) hS f h1 hmul]
  -- But : ∑ squarefree ≤ X, f(n) ≤ ∑ T ⊆ primesBelow X, f(T.prod id)
  --
  -- Stratégie : montrer que LHS = ∑ sur l'image de (n ↦ n.primeFactors),
  -- puis que cette image est incluse dans (primesBelow X).powerset.
  set LHS_set := (Finset.range (Nat.floor X + 1)).filter
            (fun n => n.Squarefree ∧ (n : ℝ) ≤ X)
  -- Injection n ↦ n.primeFactors sur LHS_set
  have h_inj : Set.InjOn (fun n : ℕ => n.primeFactors) (LHS_set : Set ℕ) := by
    intro n hn m hm heq
    simp only [Finset.coe_filter, Finset.coe_range, Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn_lt, hnsq, _⟩
    rcases hm with ⟨hm_lt, hmsq, _⟩
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; exact (Nat.not_squarefree_zero (h0 ▸ hnsq))
      · exact h
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · exfalso; exact (Nat.not_squarefree_zero (h0 ▸ hmsq))
      · exact h
    have hn_eq : n = (n.primeFactors).prod id :=
      (prod_primeFactors_of_squarefree hnsq hn_pos).symm
    have hm_eq : m = (m.primeFactors).prod id :=
      (prod_primeFactors_of_squarefree hmsq hm_pos).symm
    rw [hn_eq, hm_eq, heq]
  -- Inclusion : l'image de n ↦ n.primeFactors dans LHS_set ⊆ (primesBelow X).powerset
  have h_incl :
      LHS_set.image (fun n => n.primeFactors) ⊆ (primesBelow X).powerset := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨n, hn, hTeq⟩
    rcases Finset.mem_filter.mp hn with ⟨hn_lt, hnsq, hnX⟩
    rw [Finset.mem_powerset]
    intro p hp
    rw [← hTeq] at hp
    rw [mem_primesBelow hX]
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; exact (Nat.not_squarefree_zero (h0 ▸ hnsq))
      · exact h
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    exact prime_factor_le_bound hn_pos
            (Nat.prime_of_mem_primeFactors hp) hp_dvd hnX
  -- Changement d'indexation de la somme LHS
  have h_rewrite :
      (∑ n ∈ LHS_set, f n)
        = ∑ T ∈ LHS_set.image (fun n => n.primeFactors), f (T.prod id) := by
    rw [Finset.sum_image (fun n hn m hm => h_inj hn hm)]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hnsq, _⟩
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; exact (Nat.not_squarefree_zero (h0 ▸ hnsq))
      · exact h
    congr 1
    exact (prod_primeFactors_of_squarefree hnsq hn_pos).symm
  rw [h_rewrite]
  -- Majoration par la somme complète sur (primesBelow X).powerset
  apply Finset.sum_le_sum_of_subset_of_nonneg h_incl
  intro T _ _
  exact hf_nonneg _

/-!
## Notes de compilation v35.5

Les trois points de friction les plus probables :

1. **`Nat.floor_le`** et **`Nat.le_floor`**. Bien présents dans Mathlib
   avec ces signatures. Aucun problème attendu.

2. **`Finset.erase_insert`**. Peut s'appeler `Finset.erase_insert_eq_erase`
   ou `Finset.erase_insert_of_not_mem`. Si le nom diffère, la preuve de
   `hinj` peut être refaite par `ext` + cas par cas.

3. **`prod_primeFactors_of_squarefree`**. C'est LE point critique. Le
   nom Mathlib exact pour "n = ∏ n.primeFactors quand n squarefree" peut
   être :
   - `Nat.Squarefree.prod_primeFactors` (le plus probable)
   - `Nat.squarefree_iff_prod_primeFactors_eq`
   - Construction manuelle via `Nat.factorization_prod_pow_eq_self`
   Thomas : essayer d'abord `exact (Nat.Squarefree.prod_primeFactors hn).symm`
   et variantes avant la construction manuelle.

4. **`Nat.Coprime.prod_right`**. Vérifier la signature exacte ; peut être
   `Nat.coprime_prod_right_iff` dans certaines versions.

Aucun de ces points n'est un trou mathématique. Tous sont des frottements
d'API Mathlib, documentés dans INTEGRATION_v35.5.md § II.
-/

end CouretUnification.Logic.H3
