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
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Finset Nat ArithmeticFunction

/-- B-00. Produits squarefree associés à un support premier fini. -/
def squarefreeProducts (S : Finset ℕ) : Finset ℕ :=
  S.powerset.image (fun T => Finset.prod T _root_.id)

/-- B-01. Lemme d'assistance : p est premier avec le produit
    de tout sous-ensemble de S' ne le contenant pas. -/
lemma coprime_prime_prod_subset
    {S' : Finset ℕ} {p : ℕ}
    (hS' : ∀ q ∈ S', q.Prime) (hp : p.Prime) (hpS' : p ∉ S')
    {s : Finset ℕ} (hs : s ⊆ S') :
    p.Coprime (s.prod _root_.id) := by
  classical
  refine Nat.Coprime.prod_right ?_
  intro q hq
  have hq_prime : q.Prime := hS' q (hs hq)
  refine hp.coprime_iff_not_dvd.mpr ?_
  intro hpq_dvd
  have hqeq : q = p := by
    rcases hq_prime.eq_one_or_self_of_dvd p hpq_dvd with h1 | hself
    · exfalso
      exact hp.ne_one h1
    · exact hself.symm
  exact hpS' (hs (hqeq ▸ hq))

/-- B-02. Disjonction combinatoire sur les images de powerset.
    [OBSOLETE — non utilisée par le chemin critique B-04,
     conservée pour documentation architecturale] -/
lemma powerset_prod_disjoint
    {S : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) :
    Disjoint
      (S.powerset.image (fun s => s.prod _root_.id))
      ((S.powerset.image (fun s => s.prod _root_.id)).image (fun n => n * p)) := by
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
    Finset.sum S.powerset (fun T => f (Finset.prod T _root_.id)) =
      Finset.prod S (fun p => (1 + f p)) := by
  classical
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro hS
    simp [h_one]
  · intro p T hpT ih hS
    have hp : p.Prime := hS p (Finset.mem_insert_self p T)
    have hT : ∀ q ∈ T, q.Prime := by
      intro q hq
      exact hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpT]
    rw [Finset.sum_powerset_insert hpT]
    have h_split : ∀ s ∈ T.powerset,
        f (Finset.prod (insert p s) _root_.id) = f p * f (Finset.prod s _root_.id) := by
      intro s hs
      have hs_sub : s ⊆ T := Finset.mem_powerset.mp hs
      have hp_not_mem_s : p ∉ s := fun hps => hpT (hs_sub hps)
      rw [Finset.prod_insert hp_not_mem_s]
      apply h_mult
      exact coprime_prime_prod_subset hT hp hpT hs_sub
    rw [Finset.sum_congr rfl h_split]
    rw [← Finset.mul_sum]
    have h_algebra :
        Finset.sum T.powerset (fun s => f (Finset.prod s _root_.id)) +
          f p * Finset.sum T.powerset (fun s => f (Finset.prod s _root_.id)) =
        (1 + f p) * Finset.sum T.powerset (fun s => f (Finset.prod s _root_.id)) := by
      ring
    rw [h_algebra, ih hT]

/-- B-05. Élévation de la multiplicativité à la norme carrée complexe. -/
lemma isMultiplicative_norm_sq
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) :
    ∀ a b, a.Coprime b → Complex.normSq (f (a * b)) =
           Complex.normSq (f a) * Complex.normSq (f b) := by
  intro a b hab
  rw [hf.map_mul_of_coprime hab]
  simp [Complex.normSq_mul]

/-- B-06. Variante normique centrale — raccord vers le bloc D (contrôle L²).

    Pour f multiplicative arithmétique :
      ∑_{T ⊆ S} |f(∏ T)|² = ∏_{p ∈ S} (1 + |f p|²)
-/
lemma sum_normSq_squarefree_eq_prod
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative) :
    Finset.sum S.powerset (fun T => Complex.normSq (f (Finset.prod T _root_.id))) =
      Finset.prod S (fun p => (1 + Complex.normSq (f p))) := by
  have h_one : (fun n => (Complex.normSq (f n) : ℂ)) 1 = 1 := by
    simpa using congrArg (fun z => (Complex.normSq z : ℂ)) hf.map_one

  have h_mult :
      ∀ a b, a.Coprime b →
        (fun n => (Complex.normSq (f n) : ℂ)) (a * b) =
          (fun n => (Complex.normSq (f n) : ℂ)) a *
          (fun n => (Complex.normSq (f n) : ℂ)) b := by
    intro a b hab
    have hm : f (a * b) = f a * f b := hf.map_mul_of_coprime hab
    have hm' :
        (Complex.normSq (f (a * b)) : ℂ) =
          (Complex.normSq (f a * f b) : ℂ) := by
      exact congrArg (fun z => (Complex.normSq z : ℂ)) hm
    calc
      (fun n => (Complex.normSq (f n) : ℂ)) (a * b)
          = (Complex.normSq (f a * f b) : ℂ) := hm'
      _ = (fun n => (Complex.normSq (f n) : ℂ)) a *
            (fun n => (Complex.normSq (f n) : ℂ)) b := by
            simp [Complex.normSq_mul]

  have hC :
      Finset.sum S.powerset (fun T => ((Complex.normSq (f (Finset.prod T _root_.id)) : ℝ) : ℂ)) =
        Finset.prod S (fun p => (1 + ((Complex.normSq (f p) : ℝ) : ℂ))) := by
    simpa using
      (squarefree_support_transfer (S := S) (hS := hS)
        (f := fun n => (Complex.normSq (f n) : ℂ))
        (h_one := h_one)
        (h_mult := h_mult))

  have hR := congrArg Complex.re hC

  have hprod_ofReal_aux :
      ∀ U : Finset ℕ,
        Finset.prod U (fun p => (1 + ((Complex.normSq (f p) : ℝ) : ℂ))) =
          (((Finset.prod U (fun p => (1 + Complex.normSq (f p))) : ℝ) : ℂ)) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        simp
    | insert p T hpT ih =>
        rw [Finset.prod_insert hpT, Finset.prod_insert hpT, ih]
        simp [Complex.ofReal_add, Complex.ofReal_mul]

  have hprod_re :
      (Finset.prod S (fun p => (1 + ((Complex.normSq (f p) : ℝ) : ℂ)))).re =
        Finset.prod S (fun p => (1 + Complex.normSq (f p))) := by
    convert congrArg Complex.re (hprod_ofReal_aux S) using 1

  have hsum_re :
      (Finset.sum S.powerset
        (fun T => ((Complex.normSq (f (Finset.prod T _root_.id)) : ℝ) : ℂ))).re =
        Finset.sum S.powerset
          (fun T => Complex.normSq (f (Finset.prod T _root_.id))) := by
    simp

  exact hsum_re.symm.trans (hR.trans hprod_re)

end CouretUnification.Logic.H3
