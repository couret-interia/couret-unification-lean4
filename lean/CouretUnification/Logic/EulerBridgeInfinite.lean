/-
# Logic/EulerBridgeInfinite.lean — E3/E4 via Mathlib EulerProduct (v35.7)

## Statut épistémique

  - Couche : Logic
  - Statut : [B] partiellement prouvé. Les théorèmes structurants reposent
             sur des pivots Mathlib dont l'existence est documentée
             (EulerProduct.eulerProduct, EulerProduct.eulerProduct_tprod,
             Real.summable_one_div_nat_add_rpow). Trois sorries analytiques
             explicites restent à fermer au build (voir Section 6).
  - sorryCount : 3 (tous documentés, aucun caché)
  - RHClaimed = false

## Doctrine — Recentrage stratégique E3/E4

Avant v35.7, E3 et E4 étaient envisagés comme un long argument bespoke
établissant le passage du pont eulérien fini vers la version infinie sur
la ligne critique. Ce fichier abandonne cette stratégie au profit de
l'utilisation du théorème pivot de Mathlib :

  `EulerProduct.eulerProduct_tprod` : pour f : ℕ → R multiplicative sur
  coprimes, avec f 0 = 0, f 1 = 1 et `Summable (fun n => ‖f n‖)`,

      ∏' p : Nat.Primes, ∑' e, f (p^e)  =  ∑' n, f n

E3 et E4 deviennent alors :

  - **E3** : fournir `Summable (fun n => ‖f n‖)`. C'est le seul vrai travail
    analytique restant. On le traite par domination via une p-série, en
    s'appuyant sur `Real.summable_one_div_nat_add_rpow`.
  - **E4** : identifier le facteur local `∑' e, f (p^e)` avec `1 + f p`
    dans le cas squarefree-supporté. C'est une couture locale élémentaire
    (les puissances ≥ 2 sont nulles).

## Lien avec le bloc B fini

Le bloc B fini (`SquarefreeSupport.lean`) a établi l'identité finie

    ∑_{T ⊆ S} f(∏ T) = ∏_{p ∈ S} (1 + f p)

pour S Finset de premiers. Ce fichier établit l'identité infinie

    ∑' n, f n = ∏' p : Nat.Primes, (1 + f p)

dans le cas squarefree-supporté. Le pont entre les deux niveaux
finis/infinis est la couture analytique dont E3 fournit l'hypothèse de
sommabilité.

## Sorries documentés

Trois sorries explicites subsistent. Ils sont localisés et attendent
soit un build-test côté Thomas, soit des compléments analytiques :

  1. `prime_pow_tsum_eq_one_add` : la couture E4 elle-même. Conceptuellement
     triviale (deux termes non nuls + queue nulle), mais la manipulation
     via `tsum_eq_add_tsum_ite'` ou équivalent demande une vérification
     de l'API Mathlib courante.
  2. `summable_prime_powers_of_squarefree` : sommabilité de la série
     locale, avec arguments de support fini.
  3. `summable_norm_of_domination` : la comparaison
     `Summable.of_nonneg_of_le` peut s'appeler autrement selon le snapshot.

Aucun de ces sorries ne masque un trou conceptuel. Tous sont des
frottements API attendus.

## Pivots Mathlib utilisés

  - `Mathlib.NumberTheory.EulerProduct.Basic` :
      EulerProduct.eulerProduct_hasProd
      EulerProduct.eulerProduct_tprod
  - `Mathlib.Analysis.PSeries` :
      Real.summable_one_div_nat_add_rpow
  - `Mathlib.Topology.Algebra.InfiniteSum.Basic` :
      tprod_congr, Summable.of_norm
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.SquarefreeSupport
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

    Une fonction f : ℕ → R est dite "squarefree-supportée" si elle s'annule
    sur toute puissance première d'exposant ≥ 2. C'est l'hypothèse-clé qui
    permet de réduire le facteur local du produit eulérien à la forme
    linéaire `1 + f p`. -/
def SquarefreeSupportLike {R : Type*} [Zero R] (f : ℕ → R) : Prop :=
  ∀ {p e : ℕ}, Nat.Prime p → 2 ≤ e → f (p ^ e) = 0

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]

/-! ## Section 2 — E4 : couture locale sur les puissances premières -/

/-- **[B] Sommabilité locale dans le cas squarefree.**

    Pour f squarefree-supportée et p premier, la série `∑' e, ‖f (p^e)‖`
    est trivialement sommable car son support est inclus dans `{0, 1}`. -/
lemma summable_prime_powers_of_squarefree
    (f : ℕ → R)
    (hsf : SquarefreeSupportLike f)
    {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖f (p ^ e)‖) := by
  -- [API-LOCAL] Stratégie : montrer que la fonction est nulle hors {0,1}.
  -- La preuve passe par `Summable.of_finset` ou par la décomposition
  -- en série à support fini. Selon le snapshot, le nom exact peut varier.
  sorry

/-- **[B] Facteur local E4 — version squarefree.**

    Pour f squarefree-supportée avec f 1 = 1, on a
        ∑' e, f (p^e) = 1 + f p.

    La preuve est conceptuellement triviale (e=0 → 1, e=1 → f p, e≥2 → 0)
    mais demande une manipulation de `tsum` via `tsum_eq_add_tsum_ite'`
    ou décomposition en série à support fini. -/
lemma prime_pow_tsum_eq_one_add
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hsf : SquarefreeSupportLike f)
    {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  -- [API-LOCAL] Stratégie de preuve :
  --   1. Établir Summable (fun e => f (p^e)) via Summable.of_norm + lemme précédent.
  --   2. Décomposer la somme en (e=0) + (e=1) + (queue e≥2).
  --   3. Identifier f (p^0) = f 1 = 1, f (p^1) = f p, queue = 0.
  -- La manipulation exacte dépend de l'API tsum_eq_add_tsum_ite' du snapshot.
  sorry

/-! ## Section 3 — Application directe du théorème EulerProduct de Mathlib -/

/-- **[A] Version `HasProd` du pont eulérien infini — pivot Mathlib.**

    Application directe de `EulerProduct.eulerProduct_hasProd`. Cette ligne
    n'ajoute aucun contenu mathématique propre ; elle expose le théorème
    pivot dans le namespace du programme. -/
theorem eulerProduct_hasProd
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0) :
    HasProd
      ({p : ℕ | Nat.Prime p}.mulIndicator (fun p : ℕ => ∑' e : ℕ, f (p ^ e)))
      (∑' n : ℕ, f n) :=
  EulerProduct.eulerProduct_hasProd hf1 @hmul hsum hf0

/-- **[A] Version `tprod` du pont eulérien infini — pivot Mathlib.** -/
theorem eulerProduct_tprod
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0) :
    (∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e)) = ∑' n : ℕ, f n := by
  simpa using EulerProduct.eulerProduct_tprod hf1 @hmul hsum hf0

/-! ## Section 4 — E4 final : identité squarefree → produit linéaire -/

/-- **[B] E4 final — identité produit infini squarefree.**

    Si f est squarefree-supportée, multiplicative sur coprimes, normée
    sommable, avec f 0 = 0 et f 1 = 1, alors

        ∑' n, f n = ∏' p : Nat.Primes, (1 + f p).

    Preuve : on combine `prime_pow_tsum_eq_one_add` (qui réduit le facteur
    local) avec `eulerProduct_tprod` (qui fournit le pont eulérien). -/
theorem squarefree_eulerProduct_tprod
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0)
    (hsf : SquarefreeSupportLike f) :
    (∏' p : Nat.Primes, (1 + f (p : ℕ))) = ∑' n : ℕ, f n := by
  calc (∏' p : Nat.Primes, (1 + f (p : ℕ)))
      = ∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e) := by
          refine tprod_congr ?_
          intro p
          symm
          exact prime_pow_tsum_eq_one_add f hf1 hsf p.property
    _ = ∑' n : ℕ, f n := eulerProduct_tprod f hf1 @hmul hsum hf0

/-! ## Section 5 — E3 : sommabilité par domination -/

/-- **[B] E3 abstrait : domination par série réelle sommable.**

    Si `‖f n‖ ≤ majorant n` avec `majorant ≥ 0` et `Summable majorant`,
    alors `Summable (fun n => ‖f n‖)`.

    [API-LOCAL] Le nom exact du lemme de comparaison peut varier selon
    le snapshot Mathlib. Variantes connues :
      - `Summable.of_nonneg_of_le`
      - `summable_of_nonneg_of_le`
      - `Summable.le_of_nonneg` -/
theorem summable_norm_of_domination
    (f : ℕ → R) (majorant : ℕ → ℝ)
    (h_nonneg : ∀ n, 0 ≤ majorant n)
    (h_le : ∀ n, ‖f n‖ ≤ majorant n)
    (h_majorant : Summable majorant) :
    Summable (fun n : ℕ => ‖f n‖) := by
  -- [API-LOCAL] Selon le snapshot, c'est `Summable.of_nonneg_of_le` ou voisin.
  sorry

/-- **[B] E3 pratique : domination par p-série décalée.**

    Variante usuelle : si `‖f n‖ ≤ C / |n + a|^σ` avec `σ > 1` et `a ≥ 0`,
    alors `Summable (fun n => ‖f n‖)`.

    Repose sur `Real.summable_one_div_nat_add_rpow`, qui établit la
    sommabilité de `n ↦ 1 / |n + a|^σ` ssi `σ > 1`. -/
theorem summable_norm_of_nat_add_rpow_bound
    (f : ℕ → R) (C a σ : ℝ)
    (hC : 0 ≤ C)
    (hσ : 1 < σ)
    (ha : 0 ≤ a)
    (hbound : ∀ n, ‖f n‖ ≤ C / |(n : ℝ) + a| ^ σ) :
    Summable (fun n : ℕ => ‖f n‖) := by
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + a| ^ σ) :=
    (Real.summable_one_div_nat_add_rpow a σ).mpr hσ
  have hscaled : Summable (fun n : ℕ => C * (1 / |(n : ℝ) + a| ^ σ)) :=
    hbase.mul_left C
  refine summable_norm_of_domination f
    (fun n => C * (1 / |(n : ℝ) + a| ^ σ))
    ?_ ?_ hscaled
  · intro n; exact mul_nonneg hC (by positivity)
  · intro n
    have := hbound n
    -- C / x = C * (1 / x) — réécriture algébrique standard
    simpa [div_eq_mul_inv, one_div] using this

/-! ## Section 6 — Liste explicite des sorries restants -/

/-- Catalogue des sorries de ce fichier, pour suivi côté Thomas. -/
def remaining_sorries_catalog : List (String × String) := [
  ("summable_prime_powers_of_squarefree",
   "[API-LOCAL] Sommabilité d'une série à support fini ⊆ {0,1}. " ++
   "Fermeture attendue par Summable.of_finset ou variante."),
  ("prime_pow_tsum_eq_one_add",
   "[API-LOCAL] Identité ∑' e, f(p^e) = 1 + f p sous support squarefree. " ++
   "Fermeture par décomposition tsum_eq_add_tsum_ite' (e=0, e=1, queue=0)."),
  ("summable_norm_of_domination",
   "[API-LOCAL] Comparaison série positive ≤ série sommable. " ++
   "Le nom exact du lemme varie selon snapshot.")
]

/-! ## Section 7 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/EulerBridgeInfinite.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.conditional
  sorryCount := 3
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-! ## Notes finales

1. **Aucune dépendance à RH** : ce fichier établit (modulo les 3 sorries
   API) l'identité produit eulérien infini = somme infinie pour toute f
   squarefree-supportée multiplicative sommable. Ceci est un théorème
   classique, indépendant de RH, formalisé via le pivot Mathlib.

2. **Aucune dépendance à `Speculative/`** : ce fichier reste dans la
   couche Logic et ne consomme aucune analogie MTF/Lyapunov.

3. **Articulation avec C3Weak** : ce fichier est conceptuellement
   indépendant de C3Weak (la rigidité quadratique). Les deux blocs
   pourront être combinés ultérieurement dans un fichier d'horizon
   analytique, pas avant.

4. **Articulation avec CriticalLineTransferSpec** : ce fichier établit
   la version infinie côté Dirichlet/Euler, sans encore identifier la
   limite avec un objet L² sur la ligne critique. Cette identification
   reste l'objet de `CriticalLineTransferSpec.lean` et de la couche
   AnalyticHorizon non encore créée.

5. **Pour Thomas — ordre de build recommandé** :
       lake build CouretUnification.Logic.SquarefreeSupport
       lake build CouretUnification.Logic.EulerBridgeInfinite
       lake build CouretUnification.Logic.C3Weak
       lake build CouretUnification.Logic.CriticalLineTransferSpec
-/

end EulerBridgeInfinite
end Logic
end CouretUnification
