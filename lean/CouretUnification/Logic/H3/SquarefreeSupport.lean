/-
Couret-Unification — v35.8.6
Logic/H3/SquarefreeSupport.lean

Front B : Glue combinatoire sur support squarefree premier.
Théorème central B-04 : somme-produit fini (base d'Euler local).

Status     : B-04 fermé (sum_powerset_insert)
             B-02 sorry [OBSOLETE]     — non utilisé par B-04
Layer      : Gold (Combinatorial)
Doctrine   : C1 (Arithmetic structure → multiplicative)
RHClaimed  : false
sorryCount : 1  (B-02 powerset_prod_disjoint, non requis)

Architecture doctrinale :
  - B-00 définition squarefreeProducts
  - B-01 coprime_prime_prod_subset     [PROVED]
  - B-02 powerset_prod_disjoint        [OBSOLETE — non sur le chemin critique]
  - B-03 squarefree_mul_iff_of_coprime [PROVED]
  - B-04 squarefree_support_transfer   [PROVED via sum_powerset_insert]
  - B-05 isMultiplicative_norm_sq      [PROVED]
  - B-06 sum_normSq_squarefree_eq_prod [PROVED via B-04]

NOTE SNAPSHOT : Les hypothèses suivantes sur l'API Mathlib sont testées :
  - Finset.sum_powerset_insert : signature (h : p ∉ S) ⟶ égalité standard
  - Nat.squarefree_mul          : version produit coprime
  - Nat.Coprime.prod_right      : confirmé
Si un nom diverge, remplacer ponctuellement sans toucher à la structure.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Finset Nat ArithmeticFunction

/-- B-00. Produits squarefree associés à un support premier fini. -/
def squarefreeProducts (S : Finset ℕ) : Finset ℕ :=
  S.powerset.image (fun T => ∏ p in T, p)

/-- B-01. Lemme d'assistance : p est premier avec le produit
    de tout sous-ensemble de S' ne le contenant pas. -/
lemma coprime_prime_prod_subset
    {S' : Finset ℕ} {p : ℕ}
    (hS' : ∀ q ∈ S', q.Prime) (hp : p.Prime) (hpS' : p ∉ S')
    {s : Finset ℕ} (hs : s ⊆ S') :
    p.Coprime (s.prod id) := by
  classical
  refine Nat.Coprime.prod_right ?_
  intro q hq
  have hq_prime : q.Prime := hS' q (hs hq)
  have hpq : p ≠ q := by
    intro h
    subst h
    exact hpS' (hs hq)
  exact hp.coprime_iff_not_dvd.mpr (hq_prime.not_dvd_iff_ne.mpr hpq.symm)

/-- B-02. Disjonction combinatoire sur les images de powerset.
    [OBSOLETE — non utilisée par le chemin critique B-04,
     conservée pour documentation architecturale] -/
lemma powerset_prod_disjoint
    {S : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) :
    Disjoint
      (S.powerset.image (fun s => s.prod id))
      ((S.powerset.image (fun s => s.prod id)).image (fun n => n * p)) := by
  classical
  -- Idée : si x = ∏ s = (∏ t) * p, alors p ∣ ∏ s. Comme s ⊆ S et p ∉ S,
  -- contradiction via unicité de la factorisation première.
  -- [OBSOLETE] : B-04 passe par sum_powerset_insert, donc ce lemme
  -- n'est plus sur le chemin critique.
  sorry

/-- B-03. Squarefree sous coprimalité. -/
lemma squarefree_mul_iff_of_coprime {m n : ℕ} (h : Coprime m n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simpa [Nat.coprime_comm] using Nat.squarefree_mul h

/-- B-04. Théorème somme-produit fini sur support squarefree.

    Pour f multiplicative normalisée (f 1 = 1) et S ensemble fini de premiers :
      ∑_{T ⊆ S} f(∏ T) = ∏_{p ∈ S} (1 + f p)

    Preuve : induction sur S, appui central sur `Finset.sum_powerset_insert`. -/
theorem squarefree_support_transfer
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (f : ℕ → ℂ)
    (h_one : f 1 = 1)
    (h_mult : ∀ a b, a.Coprime b → f (a * b) = f a * f b) :
    (∑ T in S.powerset, f (∏ p in T, p)) = ∏ p in S, (1 + f p) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [h_one]
  · intro p T hpT ih
    have hp : p.Prime := hS p (Finset.mem_insert_self p T)
    have hT : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    -- 1. Expansion du produit eulérien local (côté droit)
    rw [Finset.prod_insert hpT]
    -- 2. Séparation topologique du powerset via Mathlib (côté gauche)
    rw [Finset.sum_powerset_insert hpT]
    -- 3. Traitement du produit interne et extraction de f(p)
    have h_split : ∀ s ∈ T.powerset,
        f (∏ q in insert p s, q) = f p * f (∏ q in s, q) := by
      intro s hs
      have hs_sub : s ⊆ T := Finset.mem_powerset.mp hs
      have hp_not_mem_s : p ∉ s := fun hps => hpT (hs_sub hps)
      -- Déploiement arithmétique du produit interne
      rw [Finset.prod_insert hp_not_mem_s]
      -- Application de la multiplicativité stricte
      apply h_mult
      exact coprime_prime_prod_subset hT hp hpT hs_sub
    -- Application de la réécriture ciblée sur la seconde somme
    rw [Finset.sum_congr rfl h_split]
    -- 4. Clôture algébrique et application de l'hypothèse d'induction
    rw [← Finset.mul_sum]
    have h_algebra :
        (∑ s in T.powerset, f (∏ q in s, q)) +
          f p * (∑ s in T.powerset, f (∏ q in s, q)) =
        (1 + f p) * (∑ s in T.powerset, f (∏ q in s, q)) := by
      ring
    rw [h_algebra, ih]

/-- B-05. Élévation de la multiplicativité à la norme carrée complexe. -/
lemma isMultiplicative_norm_sq
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) :
    ∀ a b, a.Coprime b → Complex.normSq (f (a * b)) =
           Complex.normSq (f a) * Complex.normSq (f b) := by
  intro a b hab
  rw [hf hab]
  simp [Complex.normSq_mul]

/-- B-06. Variante normique centrale — raccord vers le bloc D (contrôle L²).

    Pour f multiplicative arithmétique :
      ∑_{T ⊆ S} |f(∏ T)|² = ∏_{p ∈ S} (1 + |f p|²)
-/
lemma sum_normSq_squarefree_eq_prod
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) :
    (∑ T in S.powerset, Complex.normSq (f (∏ p in T, p))) =
      ∏ p in S, (1 + Complex.normSq (f p)) := by
  have h_one : Complex.normSq (f 1) = 1 := by
    simpa using congrArg Complex.normSq hf.map_one
  have h_mult :
      ∀ a b, a.Coprime b →
        Complex.normSq (f (a * b)) =
          Complex.normSq (f a) * Complex.normSq (f b) :=
    isMultiplicative_norm_sq f hf
  simpa using
    (squarefree_support_transfer (S := S) (hS := hS)
      (f := fun n => (Complex.normSq (f n) : ℂ))
      (h_one := by simpa using h_one)
      (h_mult := by
        intro a b hab
        have := h_mult a b hab
        -- transport Complex.normSq (f ·) : ℕ → ℝ → ℂ
        push_cast
        exact_mod_cast this))

end CouretUnification.Logic.H3
