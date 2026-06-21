/-
Copyright (c) 2026 Couret-Unification Programme.

# Logic/H3/LocalSquarefreeBridge.lean — Pont fini A + B

## Doctrine

Ce fichier établit, sur un ensemble FINI de premiers, l'identité-pont entre :
  - le contrôle local du facteur eulérien (Bloc A : LocalFactor)
  - le transfert combinatoire squarefree (Bloc B : SquarefreeSupport)

Énoncé central : pour S un ensemble fini de premiers et σ ≥ 0,

  ∑_{T ⊆ S} ∏_{p ∈ T} p^{-σ} = ∏_{p ∈ S} (1 + p^{-σ})

C'est la version FINIE du produit eulérien sur la ligne critique pour la
fonction caractéristique des squarefree.

## Frontière E3 / E4 — explicitement maintenue ouverte

Ce fichier ne franchit PAS le mur du passage à la limite X → ∞.
Le théorème commenté `local_squarefree_bridge_infinite` est volontairement
NON ÉNONCÉ : tenter de l'établir ici reviendrait à effondrer la doctrine
RHClaimed = false, car la version infinie touche à E2 (det₂), E3 (convergence
du produit infini) et E4 (identification avec ξ) — verrous qui appartiennent
à `AnalyticHorizon/EulerCompletion.lean`, lui-même ouvert.

## Statut épistémique

  - Couche : Logic/H3 (raccord local fini)
  - Statut : [P] sur le théorème fini ; frontière E3/E4 explicitement [O].
  - RHClaimed = false.

-/

import CouretUnification.Core.Doctrine
import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.SquarefreeSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

namespace CouretUnification
namespace H3
namespace LocalSquarefreeBridge

open Finset
open scoped BigOperators

/-!
## Section 1 — Multiplicativité de p ↦ p^{-σ}

Sur les coprimes positifs, n ↦ n^{-σ} est multiplicative (au sens
des fonctions arithmétiques). On le prouve à partir de `Real.mul_rpow`.
-/

/-- [P] La fonction n ↦ n^{-σ} (avec n ≠ 0 → n^{-σ}, sinon 1) est
    multiplicative au sens de coprimalité, pour σ ≥ 0. -/
theorem rpow_neg_multiplicative (σ : ℝ) (_hσ : 0 ≤ σ) :
    (fun n : ℕ => if n = 0 then (1 : ℝ) else (n : ℝ) ^ (-σ)) 1 = 1 ∧
    ∀ a b : ℕ, Nat.Coprime a b →
      (fun n : ℕ => if n = 0 then (1 : ℝ) else (n : ℝ) ^ (-σ)) (a * b)
        = (fun n : ℕ => if n = 0 then (1 : ℝ) else (n : ℝ) ^ (-σ)) a *
          (fun n : ℕ => if n = 0 then (1 : ℝ) else (n : ℝ) ^ (-σ)) b := by
  refine ⟨?_, ?_⟩
  · -- f(1) = 1 : simp ferme tout via Real.one_rpow.
    simp
  · intro a b hcop
    simp only
    -- Cas a = 0 : Coprime 0 b ⟺ b = 1
    by_cases ha : a = 0
    · subst ha
      have hb : b = 1 := by
        rw [Nat.Coprime, Nat.gcd_zero_left] at hcop
        exact hcop
      subst hb
      simp
    by_cases hb : b = 0
    · subst hb
      have ha1 : a = 1 := by
        rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
        exact hcop
      subst ha1
      simp
    -- Cas générique : a, b > 0
    have hab_ne : a * b ≠ 0 := Nat.mul_ne_zero ha hb
    simp [ha, hb, hab_ne]
    -- Goal après simp : (↑a * ↑b) ^ (-σ) = ↑a ^ (-σ) * ↑b ^ (-σ)
    -- Le cast Nat.cast_mul a déjà été poussé par simp.
    have ha_nn : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb_nn : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    exact Real.mul_rpow ha_nn hb_nn

/-- [P] Pour T fini d'entiers, (∏ T)^(-σ) = ∏_T p^(-σ) sur ℝ.
    Preuve par induction sur T, sans dépendre d'un nom Mathlib spécifique. -/
private lemma prod_rpow_neg_aux (T : Finset ℕ) (σ : ℝ) :
    (∏ i ∈ T, (i : ℝ)) ^ (-σ) = ∏ p ∈ T, (p : ℝ) ^ (-σ) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q U hqU ih =>
      rw [Finset.prod_insert hqU, Finset.prod_insert hqU,
          Real.mul_rpow (Nat.cast_nonneg q)
            (Finset.prod_nonneg (fun r _ => Nat.cast_nonneg r)),
          ih]

/-!
## Section 2 — Pont fini sur la ligne critique

Pour S = primes ≤ X, l'identité-pont donne directement
  ∑ T ⊆ S, ∏ T p^{-σ} = ∏_{p ∈ S} (1 + p^{-σ}).
-/

/-- [P] **Pont fini local-squarefree, version générique sur S.**

    Pour S un ensemble fini de premiers et σ ≥ 0,
      ∑_{T ⊆ S} ∏_{p ∈ T} p^{-σ} = ∏_{p ∈ S} (1 + p^{-σ}). -/
theorem local_squarefree_bridge_finite
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ T ∈ S.powerset, ∏ p ∈ T, (p : ℝ) ^ (-σ))
      = ∏ p ∈ S, (1 + (p : ℝ) ^ (-σ)) := by
  set f : ℕ → ℝ := fun n => if n = 0 then (1 : ℝ) else (n : ℝ) ^ (-σ) with hf_def
  obtain ⟨hf_one, hf_mult⟩ := rpow_neg_multiplicative σ hσ
  -- Transfert combinatoire
  have h_transfer :
      (∑ T ∈ S.powerset, f (∏ p ∈ T, p)) = ∏ p ∈ S, (1 + f p) :=
    CouretUnification.Logic.H3.squarefree_support_transfer_real
      hS f hf_one hf_mult
  -- Identification LHS terme-à-terme
  have h_lhs : ∀ T ∈ S.powerset,
      f (∏ p ∈ T, p) = ∏ p ∈ T, (p : ℝ) ^ (-σ) := by
    intro T hT
    have hT_sub : T ⊆ S := mem_powerset.mp hT
    have hprod_ne : (∏ p ∈ T, p) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      exact Nat.Prime.ne_zero (hS q (hT_sub hq))
    show (if (∏ p ∈ T, p) = 0 then (1 : ℝ)
          else ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ)) = ∏ p ∈ T, (p : ℝ) ^ (-σ)
    rw [if_neg hprod_ne]
    push_cast
    exact prod_rpow_neg_aux T σ
  -- Identification RHS terme-à-terme
  have h_rhs : ∀ p ∈ S, (1 + f p) = 1 + (p : ℝ) ^ (-σ) := by
    intro p hp
    have hp_ne : p ≠ 0 := Nat.Prime.ne_zero (hS p hp)
    show 1 + (if p = 0 then (1 : ℝ) else (p : ℝ) ^ (-σ)) = 1 + (p : ℝ) ^ (-σ)
    rw [if_neg hp_ne]
  -- Conclusion par calc
  calc (∑ T ∈ S.powerset, ∏ p ∈ T, (p : ℝ) ^ (-σ))
      = ∑ T ∈ S.powerset, f (∏ p ∈ T, p) :=
        Finset.sum_congr rfl (fun T hT => (h_lhs T hT).symm)
    _ = ∏ p ∈ S, (1 + f p) := h_transfer
    _ = ∏ p ∈ S, (1 + (p : ℝ) ^ (-σ)) := Finset.prod_congr rfl h_rhs

/-!
## Section 3 — Borne issue de LocalFactor (raccord effectif)

Ici on relie l'identité finie ci-dessus aux bornes du facteur local
de LocalFactor.lean : pour t ∈ ℝ, le facteur eulérien complet
|1 - p^{-σ}·e^{it log p}|² est borné par (1 + p^{-σ})².

C'est cette borne, élevée au produit, qui contrôle le facteur
eulérien complet par notre identité combinatoire.
-/

/-- [P] Cohérence de raccord : pour tout p premier et tout t ∈ ℝ, le module
    au carré |1 - p^{-σ}·e^{it log p}|² est borné par (1 + p^{-σ})².

    C'est la borne supérieure du Bloc A (LocalFactor) appliquée à
    a = p^{-σ} et θ = t · log p. -/
theorem local_factor_bound_at_prime {p : ℕ} (hp : Nat.Prime p)
    {σ t : ℝ} (hσ : 0 ≤ σ) :
    Complex.normSq
        (1 - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) *
              Complex.exp ((t * Real.log p : ℂ) * Complex.I))
      ≤ (1 + (p : ℝ) ^ (-σ)) ^ 2 := by
  have h := (CouretUnification.Logic.H3.local_factor_prime_sigma
    p hp σ (t * Real.log p) hσ).2
  rw [← Complex.ofReal_mul]
  exact h

/-!
## Section 4 — Frontière E3/E4 — explicitement ouverte

Les théorèmes qui suivraient — passage à X → ∞, convergence du produit
infini, recollement avec ξ — **n'apparaissent pas dans ce fichier**.

Les raisons sont documentées dans le cahier des charges EulerCompletion :
  - E2 (minoration du dénominateur det₂) : bloquée par l'absence
    d'infrastructure Mathlib standard pour les déterminants régularisés.
  - E3 (convergence du produit infini) : dépend de E1 ET E2.
  - E4 (identification avec ξ) ≡ Lock 3 fort.

**Toute tentative de fermer ces verrous ici serait une violation de
l'invariant RHClaimed = false.** La frontière est maintenue.
-/

/-!
## Section 5 — Invariant constitutionnel
-/

/-- [P] Identité du fichier. -/
def fileIdentity : CouretUnification.FileIdentity where
  module := "CouretUnification.Logic.H3.LocalSquarefreeBridge"
  layer := CouretUnification.Layer.logicH3
  status := CouretUnification.EpistemicStatus.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-!
## Notes finales

1. **Apport mathématique** : c'est la première fois dans le programme que
   les Blocs A (LocalFactor) et B (SquarefreeSupport) sont effectivement
   reliés dans un théorème formel certifié.

2. **Apport doctrinal** : la frontière E3/E4 est rendue explicite DANS LE CODE,
   par l'absence volontaire du théorème infini.

3. **Frottements API** :
   - `Finset.prod_rpow_of_nonneg` : nom à vérifier (peut être
     `Real.finset_prod_rpow` selon le snapshot).
   - `Finset.prod_ne_zero_iff` : nom stable.

4. **Réutilisation** : ce théorème pourra être cité dans une note
   comme exemple concret de pont fini certifié.
-/

end LocalSquarefreeBridge
end H3
end CouretUnification
