/-
Copyright (c) 2026 Alexandre Couret. Tous droits réservés.

# Sophie Germain Tower Lift (v38)

Formalisation du relèvement en tour des classes admissibles de Sophie Germain.

Un résidu `a` modulo `M` est admissible au sens de Sophie Germain ssi :
  * gcd(a, M) = 1
  * gcd(2a + 1, M) = 1

Cela encode le crible local au niveau M :
  * p ≡ a (mod M) potentiellement premier
  * 2p + 1 ≡ 2a + 1 (mod M) potentiellement premier

Lorsqu'un nouveau premier ℓ est ajouté à la tour primorielle, chaque classe
survivante modulo M produit exactement ℓ - 2 enfants modulo Mℓ. Les deux
enfants exclus correspondent aux deux équations `a + tM ≡ 0 mod ℓ` et
`2(a + tM) + 1 ≡ 0 mod ℓ`, qui ont des solutions distinctes pour ℓ ≥ 3.

## Chaîne numérique aux niveaux v38

  niveau 30 (= 2·3·5) :       3 classes survivantes ({11, 23, 29})
  niveau 210 (= 30·7) :       3 × 5  = 15
  niveau 2310 (= 210·11) :    15 × 9 = 135
  niveau 30030 (= 2310·13) :  135 × 11 = 1485

## Architecture

La décomposition se fait en deux couches :
  * Concrète : `native_decide` sur les petits modules (30, 210, 2310, 30030).
  * Abstraite : lemme combinatoire `TwoRemovedFiber_card` et
    `AbstractTowerLift_card`, séparant le calcul cardinal du contenu
    arithmétique.

## Statut doctrinal

Statut : `[D]` — certifié par machine. Aucun `sorry`, aucun `axiom`, aucun `admit`.

Ce fichier établit un invariant arithmétique local. Il n'établit AUCUNE
identité analytique globale. Les invariants `RHClaimed = false`,
`HilbertPolyaClaimed = false` et `L7Established = false` sont préservés.

Le tower lift de Sophie Germain est un fait [D] dans le noyau combinatoire
fini. Son articulation avec le programme spectral (opérateur Δ̃_SG,
spectre {δ̃₁, δ̃₂, δ̃₃} sur Δ⁷, signature de canal 1/√7) est une question
séparée et demeure [M]/[H] jusqu'à de nouveaux résultats analytiques.

## Référence

  * Cartographie analytique v38.1, sous-lemme Sophie Germain
  * `DOCTRINE_L7_KRUSKAL_v38.2.md` (positionnement dans la décomposition L7)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Bind
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace CouretUnification
namespace SophieGermainTowerLift

open Finset

/-! ## Section 1 : Admissibilité Sophie Germain -/

/-- Un résidu `a` modulo `M` est admissible au sens de Sophie Germain ssi
    `a` et `2a + 1` sont tous deux premiers à `M`.

    La définition utilise directement `Nat.gcd _ = 1` plutôt que
    `Nat.Coprime`, afin de garder l'inférence de décidabilité entièrement
    automatique entre versions de Mathlib. -/
def SGAdmissible (M a : Nat) : Prop :=
  Nat.gcd a M = 1 ∧ Nat.gcd (2 * a + 1) M = 1

/-- Instance explicite de décidabilité pour `SGAdmissible`.
    Elle est automatique à partir de la conjonction de deux égalités
    décidables, mais elle est donnée explicitement afin que `Finset.filter`
    fonctionne sans surprise. -/
instance instDecidableSGAdmissible (M a : Nat) : Decidable (SGAdmissible M a) := by
  unfold SGAdmissible
  infer_instance

/-- L'ensemble fini des résidus admissibles de Sophie Germain modulo `M`. -/
def SGResidues (M : Nat) : Finset Nat :=
  (Finset.range M).filter (SGAdmissible M)

/-! ## Section 2 : Calculs concrets aux niveaux primoriels

Les quatre théorèmes ci-dessous sont décidés par `native_decide`, qui compile
le prédicat en code natif et l'évalue. Pour `M ≤ 30030`, l'évaluation reste
largement inférieure à une seconde. -/

/-- Au niveau 30 = 2·3·5, exactement trois classes de résidus survivent :
    {11, 23, 29}.

    Remarque : les huit unités modulo 30 sont {1, 7, 11, 13, 17, 19, 23, 29}.
    La contrainte Sophie Germain `gcd(2a+1, 30) = 1` élimine en plus les `a`
    pour lesquels `2a + 1 ∈ {15, 30, 45, ...}` modulo 30, ne laissant que
    {11, 23, 29}. -/
theorem SGResidues_mod30 :
    SGResidues 30 = ({11, 23, 29} : Finset Nat) := by
  native_decide

theorem SGResidues_mod30_card :
    (SGResidues 30).card = 3 := by
  native_decide

/-- Au niveau 210 = 30·7, quinze classes de résidus survivent. -/
theorem SGResidues_mod210_card :
    (SGResidues 210).card = 15 := by
  native_decide

/-- Au niveau 2310 = 210·11, 135 classes de résidus survivent. -/
theorem SGResidues_mod2310_card :
    (SGResidues 2310).card = 135 := by
  native_decide

/-- Au niveau 30030 = 2310·13, 1485 classes de résidus survivent. -/
theorem SGResidues_mod30030_card :
    (SGResidues 30030).card = 1485 := by
  native_decide

/-! ## Section 3 : Lemme combinatoire abstrait

Le calcul cardinal `|R_{Mℓ}^{SG}| = (ℓ - 2)·|R_M^{SG}|` est un fait
combinatoire pur : pour chaque classe parente, les ℓ enfants indexés par
`Fin ℓ` perdent exactement deux branches par les deux équations du crible.
Nous isolons cette couche combinatoire du contenu arithmétique. -/

/-- Une fibre de ℓ enfants avec deux enfants distincts retirés. -/
def TwoRemovedFiber (ℓ : Nat) (b₀ b₁ : Fin ℓ) : Finset (Fin ℓ) :=
  ((Finset.univ : Finset (Fin ℓ)).erase b₀).erase b₁

/-- Retirer deux éléments distincts d'un univers de cardinal ℓ produit
    un finset de cardinal ℓ - 2. -/
theorem TwoRemovedFiber_card
    {ℓ : Nat} {b₀ b₁ : Fin ℓ} (h : b₀ ≠ b₁) :
    (TwoRemovedFiber ℓ b₀ b₁).card = ℓ - 2 := by
  classical
  unfold TwoRemovedFiber
  have hb₀_univ : b₀ ∈ (Finset.univ : Finset (Fin ℓ)) := by
    simp
  have hb₁_erase : b₁ ∈ (Finset.univ : Finset (Fin ℓ)).erase b₀ := by
    simp [h.symm]
  rw [Finset.card_erase_of_mem hb₁_erase]
  rw [Finset.card_erase_of_mem hb₀_univ]
  rw [Finset.card_univ, Fintype.card_fin]
  rw [Nat.sub_sub]

/-- Tower lift abstrait : chaque parent dans `Parents` est apparié avec une
    fibre de ℓ - 2 enfants survivants, une fois données deux positions
    interdites distinctes. -/
def AbstractTowerLift
    {α : Type _} [DecidableEq α]
    (Parents : Finset α) (ℓ : Nat)
    (bad₀ bad₁ : α → Fin ℓ) :
    Finset (Σ _ : α, Fin ℓ) :=
  Parents.sigma (fun x => TwoRemovedFiber ℓ (bad₀ x) (bad₁ x))

/-- Le cardinal du tower lift abstrait vaut `Parents.card * (ℓ - 2)`. -/
theorem AbstractTowerLift_card
    {α : Type _} [DecidableEq α]
    (Parents : Finset α) (ℓ : Nat)
    (bad₀ bad₁ : α → Fin ℓ)
    (hbad : ∀ x ∈ Parents, bad₀ x ≠ bad₁ x) :
    (AbstractTowerLift Parents ℓ bad₀ bad₁).card =
      Parents.card * (ℓ - 2) := by
  classical
  unfold AbstractTowerLift
  have h_sum_eq : ∀ x ∈ Parents,
      (TwoRemovedFiber ℓ (bad₀ x) (bad₁ x)).card = ℓ - 2 := by
    intro x hx
    exact TwoRemovedFiber_card (hbad x hx)
  change
    (Parents.val.sigma
      (fun x => (TwoRemovedFiber ℓ (bad₀ x) (bad₁ x)).val)).card =
      Parents.card * (ℓ - 2)
  rw [Multiset.card_sigma]
  have hmap :
      Parents.val.map
          (fun x => (TwoRemovedFiber ℓ (bad₀ x) (bad₁ x)).val.card)
        = Parents.val.map (fun _x => ℓ - 2) := by
    apply Multiset.map_congr
    · rfl
    · intro x hx
      exact h_sum_eq x hx
  rw [hmap]
  change Finset.sum Parents (fun _x => ℓ - 2) = Parents.card * (ℓ - 2)
  simp [Finset.sum_const]

/-! ## Section 4 : Témoins numériques de la chaîne

Témoins numériques directs, utiles comme lemmes autonomes et comme entrées
de `SG_tower_chain_v38`. -/

theorem SG_tower_count_30_210 :
    3 * (7 - 2) = 15 := by norm_num

theorem SG_tower_count_210_2310 :
    15 * (11 - 2) = 135 := by norm_num

theorem SG_tower_count_2310_30030 :
    135 * (13 - 2) = 1485 := by norm_num

/-! ## Section 5 : Forme compacte de la chaîne de Sophie Germain -/

/-- Forme compacte de la chaîne du tower lift de Sophie Germain aux niveaux
    v38 : les cardinaux aux modules 30, 210, 2310, 30030 simultanément. -/
theorem SG_tower_chain_v38 :
    (SGResidues 30).card = 3 ∧
    (SGResidues 210).card = 15 ∧
    (SGResidues 2310).card = 135 ∧
    (SGResidues 30030).card = 1485 :=
  ⟨SGResidues_mod30_card,
   SGResidues_mod210_card,
   SGResidues_mod2310_card,
   SGResidues_mod30030_card⟩

end SophieGermainTowerLift
end CouretUnification

/-!
## Clôture doctrinale

Ce fichier établit le tower lift de Sophie Germain aux niveaux v38.

Établi, statut `[D]` :
  * `SGResidues 30 = {11, 23, 29}` (décidé par code natif)
  * Cardinalité aux niveaux 30, 210, 2310, 30030 (décidée)
  * Lemme combinatoire abstrait `TwoRemovedFiber_card`
  * Tower lift abstrait `AbstractTowerLift_card` avec règle (ℓ - 2)
  * Chaîne numérique consolidée sous `SG_tower_chain_v38`

NON établi ici :
  * Articulation avec le programme spectral (opérateur Δ̃_SG)
  * Toute connexion à des identités analytiques globales (L7, RH)
  * La signature de canal 1/√7, qui relève du niveau spectral et non du
    tower lift combinatoire

Aucun `sorry`, aucun `axiom`, aucun `admit`.

Invariants préservés :
  * `RHClaimed = false`
  * `HilbertPolyaClaimed = false`
  * `L7Established = false`

Pour Bernard Couret (1928-1999).
-/
