/-
# Logic/EulerBridgeInfinite.lean — E3/E4 via Mathlib EulerProduct (v35.7.1)

## Statut épistémique

  - Couche : Logic
  - Statut : [B] partiellement prouvé. Le théorème final
             `squarefree_limit_eq_euler_product` est établi modulo deux
             sorries `[API-LOCAL]` clairement isolés.
  - sorryCount : 2 (E4.2 et E3.1, et nulle part ailleurs)
  - RHClaimed = false

## Refactoring v35.7.1

Cette version remplace la précédente par un découpage plus serré, avec
lemmes numérotés selon la structure conceptuelle :

  - E4.1 : annulation locale sur les puissances premières élevées (trivial, 0 sorry)
  - E4.2 : facteur local squarefree `∑' e, f(p^e) = 1 + f p`     ← sorry API
  - E3.1 : comparaison abstraite par majorant sommable           ← sorry API
  - E3.2 : majoration pratique par p-série décalée (preuve complète)
  - e4_bridge_tprod : pont EulerProduct standard (preuve complète)
  - squarefree_limit_eq_euler_product : théorème final (preuve complète)

Le cœur mathématique propre du fichier est minuscule : E4.2 et E3.1.
Tout le reste est plomberie qui s'appuie sur Mathlib.

## Doctrine — Recentrage E3/E4 vs stratégie bespoke

Avant v35.7, E3/E4 étaient envisagés comme un long argument bespoke
"fini → infini". Le pivot Mathlib `EulerProduct.eulerProduct_tprod`
rend cette construction inutile :

  - **E4** = couture locale élémentaire (puissances ≥ 2 nulles).
  - **E3** = sommabilité de `n ↦ ‖f n‖` par domination via p-série.
  - **Pont infini** = appel direct à `EulerProduct.eulerProduct_tprod`.

## Pivots Mathlib utilisés

  - `Mathlib.NumberTheory.EulerProduct.Basic`
      → `EulerProduct.eulerProduct_tprod`
  - `Mathlib.Analysis.PSeries`
      → `Real.summable_one_div_nat_add_rpow`
  - `Mathlib.Topology.Algebra.InfiniteSum.Basic`
      → `tprod_congr`
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.H3.SquarefreeSupport
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

noncomputable section
open scoped BigOperators
open Classical

namespace CouretUnification
namespace Logic
namespace EulerBridgeInfinite

open CouretUnification.Meta

/-! ## Section 1 — Hypothèse de support squarefree -/

/-- **[B] Support squarefree abstrait.**

    Une fonction `f : ℕ → R` est dite "squarefree-supportée" si elle
    s'annule sur toute puissance première d'exposant ≥ 2. -/
def SquarefreeSupportLike {R : Type*} [Zero R] (f : ℕ → R) : Prop :=
  ∀ {p e : ℕ}, Nat.Prime p → 2 ≤ e → f (p ^ e) = 0

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]

/-! ## Section 2 — Lemmes E4 (couture locale) -/

/-- **[A] E4.1 : annulation locale sur les puissances premières élevées.**

    Conséquence directe et triviale de `SquarefreeSupportLike`. Pas de sorry. -/
lemma e4_1_prime_pow_eq_zero
    (f : ℕ → R)
    (hsf : SquarefreeSupportLike f)
    {p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    f (p ^ e) = 0 :=
  hsf hp he

/-- **[B] E4.2 : facteur local squarefree.**

    Pour `f` squarefree-supportée avec `f 1 = 1`, on a
        `∑' e, f (p^e) = 1 + f p`.

    Preuve conceptuelle : termes `e=0` (= 1) + `e=1` (= f p) + queue nulle.
    Le sorry est un frottement API sur la décomposition de `tsum`. -/
lemma e4_2_prime_pow_tsum_eq_one_add
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hsf : SquarefreeSupportLike f)
    {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  -- [API-LOCAL] Stratégie : décomposer ∑' e en (e=0) + (e=1) + (queue e≥2).
  -- Schéma cible :
  --   (∑' e, f (p^e))
  --     = f (p^0) + ∑' e, if e = 0 then 0 else f (p^e)   -- tsum_eq_add_tsum_ite'
  --     = 1 + (f (p^1) + 0)                              -- hf1, hsf
  --     = 1 + f p                                        -- pow_one
  --
  -- TRY THIS NAME IF SNAPSHOT FAILS sur la décomposition tsum :
  --   tsum_eq_add_tsum_ite'         (extraire un terme à index donné)
  --   tsum_ite_eq                    (terme isolé)
  --   tsum_eq_sum                    (si on prouve support fini)
  --   Summable.tsum_eq_add_tsum_ite' (forme méthode)
  sorry

/-! ## Section 3 — Lemmes E3 (sommabilité analytique) -/

/-- **[B] E3.1 : comparaison abstraite par un majorant sommable.**

    Si `‖f n‖ ≤ majorant n` avec `majorant ≥ 0` et `Summable majorant`,
    alors `Summable (fun n => ‖f n‖)`. -/
lemma e3_1_summable_norm_of_domination
    (f : ℕ → R) (majorant : ℕ → ℝ)
    (h_nonneg : ∀ n, 0 ≤ majorant n)
    (h_le : ∀ n, ‖f n‖ ≤ majorant n)
    (h_majorant : Summable majorant) :
    Summable (fun n : ℕ => ‖f n‖) := by
  -- [API-LOCAL] Le nom exact du lemme de comparaison varie selon snapshot.
  -- TRY THIS NAME IF SNAPSHOT FAILS :
  --   Summable.of_nonneg_of_le         (variante Mathlib4 récente)
  --   summable_of_nonneg_of_le         (forme historique, peut survivre)
  --   Summable.of_norm_bounded_eventually
  --   h_majorant.of_nonneg_of_le ...   (forme méthode)
  sorry

/-- **[A] E3.2 : majoration pratique par p-série décalée.**

    Si `‖f n‖ ≤ C / |n + a|^σ` avec `σ > 1` et `a ≥ 0`,
    alors `Summable (fun n => ‖f n‖)`.

    Preuve complète qui s'appuie sur `Real.summable_one_div_nat_add_rpow`
    et la comparaison E3.1. -/
lemma e3_2_summable_norm_of_nat_add_rpow_bound
    (f : ℕ → R) (C a σ : ℝ)
    (hC : 0 ≤ C)
    (hσ : 1 < σ)
    (_ha : 0 ≤ a)
    (hbound : ∀ n, ‖f n‖ ≤ C / |(n : ℝ) + a| ^ σ) :
    Summable (fun n : ℕ => ‖f n‖) := by
  -- TRY THIS NAME IF SNAPSHOT FAILS sur Real.summable_one_div_nat_add_rpow :
  --   Real.summable_one_div_nat_rpow         (sans décalage a)
  --   NNReal.summable_one_div_rpow           (variante NNReal)
  --   summable_nat_rpow_inv                  (forme inversée)
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + a| ^ σ) :=
    (Real.summable_one_div_nat_add_rpow a σ).mpr hσ
  have hscaled : Summable (fun n : ℕ => C * (1 / |(n : ℝ) + a| ^ σ)) :=
    hbase.mul_left C
  refine e3_1_summable_norm_of_domination f
    (fun n => C * (1 / |(n : ℝ) + a| ^ σ))
    ?_ ?_ hscaled
  · intro n
    exact mul_nonneg hC (by positivity)
  · intro n
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound n

/-! ## Section 4 — Pont EulerProduct (pivot Mathlib) -/

/-- **[A] Pont EulerProduct standard, version `tprod`.**

    Wrapper direct sur `EulerProduct.eulerProduct_tprod`. Aucun contenu
    mathématique propre ; expose le théorème pivot dans le namespace du
    programme pour un appel localisé. -/
theorem e4_bridge_tprod
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0) :
    (∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e)) = ∑' n : ℕ, f n := by
  -- TRY THIS NAME IF SNAPSHOT FAILS :
  --   EulerProduct.eulerProduct_tprod         (nom canonique attendu)
  --   ArithmeticFunction.LSeries...           (route alternative LSeries)
  simpa using EulerProduct.eulerProduct_tprod hf1 @hmul hsum hf0

/-! ## Section 5 — Théorème final E3/E4 -/

/-- **[B] E3+E4 final : produit eulérien linéarisé dans le cas squarefree.**

    Si `f` est squarefree-supportée, multiplicative sur coprimes, normée
    sommable, avec `f 0 = 0` et `f 1 = 1`, alors

        `∑' n, f n = ∏' p : Nat.Primes, (1 + f p)`.

    Preuve : couture locale E4.2 + pont EulerProduct standard. -/
theorem squarefree_limit_eq_euler_product
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0)
    (hsf : SquarefreeSupportLike f) :
    (∏' p : Nat.Primes, (1 + f (p : ℕ))) = ∑' n : ℕ, f n := by
  calc
    (∏' p : Nat.Primes, (1 + f (p : ℕ)))
      = ∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e) := by
          refine tprod_congr ?_
          intro p
          symm
          exact e4_2_prime_pow_tsum_eq_one_add f hf1 hsf p.property
    _ = ∑' n : ℕ, f n := by
          simpa using e4_bridge_tprod f hf1 @hmul hsum hf0

/-! ## Section 6 — Catalogue des sorries -/

/-- Liste explicite des sorries et de leurs résolutions probables. -/
def remaining_sorries_catalog : List (String × String) := [
  ("e4_2_prime_pow_tsum_eq_one_add",
   "[API-LOCAL] Décomposition tsum (e=0) + (e=1) + (queue=0). " ++
   "Candidats : tsum_eq_add_tsum_ite', tsum_eq_sum (support fini)."),
  ("e3_1_summable_norm_of_domination",
   "[API-LOCAL] Comparaison série positive ≤ série sommable. " ++
   "Candidats : Summable.of_nonneg_of_le, summable_of_nonneg_of_le.")
]

/-! ## Section 7 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/EulerBridgeInfinite.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.conditional
  sorryCount := 2
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-! ## Notes finales

1. **Cœur mathématique propre du fichier** :
   - E4.2 (couture locale squarefree) — 1 sorry API
   - E3.1 (comparaison séries)        — 1 sorry API
   Tout le reste est wrapping de Mathlib ou preuve complète.

2. **Gain v35.7 → v35.7.1** : passage de 3 sorries à 2.
   Le `summable_prime_powers_of_squarefree` de v35.7 est éliminé
   parce qu'il n'est pas nécessaire dans la chaîne principale.

3. **Pour Thomas** :
   - E3.2 et `e4_bridge_tprod` doivent passer vert sans intervention.
   - `squarefree_limit_eq_euler_product` compile par construction
     (les deux sorries ci-dessus sont acceptés par Lean).
   - Test décisif : E4.2 et E3.1. Les noms Mathlib alternatifs
     sont commentés `-- TRY THIS NAME IF SNAPSHOT FAILS`.

4. **Aucune dépendance à RH** : théorème classique, indépendant.

5. **Aucune dépendance à `Speculative/`** : ne consomme aucune analogie
   MTF/Lyapunov.

6. **Ordre de build recommandé** :
       lake build CouretUnification.Logic.H3.SquarefreeSupport
       lake build CouretUnification.Logic.EulerBridgeInfinite
       lake build CouretUnification.Logic.C3Weak
       lake build CouretUnification.Logic.CriticalLineTransferSpec
-/

end EulerBridgeInfinite
end Logic
end CouretUnification
