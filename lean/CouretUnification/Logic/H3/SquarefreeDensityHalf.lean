/-
Couret-Unification — v38.5.12-lab
# CouretUnification/Logic/H3/SquarefreeDensityHalf.lean

## Rôle

Laboratoire de fermeture de C-04a :
  pour N ≥ 176, squarefreeCount N ≥ N / 2.

Ce premier fichier ne ferme pas encore la borne effective.
Il réduit C-04a à une majoration équivalente du nombre d'entiers
non-squarefree.

## Statut

- Couche      : Logic / H3
- Front       : C-04a — minoration effective squarefree
- C-04b       : déjà fermé via SquarefreeDensityC04bClosed
- RHClaimed   : false
- Sorry count : 0
-/

import CouretUnification.Logic.H3.SquarefreeDensityC04bClosed

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- Nombre d'entiers non-squarefree dans `[1, N]`. -/
def nonSquarefreeCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => ¬ Squarefree n)).card

/-- Décomposition exacte de `[1, N]` en squarefree et non-squarefree. -/
theorem squarefreeCount_add_nonSquarefreeCount
    (N : ℕ) :
    squarefreeCount N + nonSquarefreeCount N = N := by
  unfold squarefreeCount
  unfold nonSquarefreeCount

  calc
    ((Finset.Icc 1 N).filter Squarefree).card
        + ((Finset.Icc 1 N).filter (fun n => ¬ Squarefree n)).card
        =
      (Finset.Icc 1 N).card := by
        exact Finset.card_filter_add_card_filter_not
          (s := Finset.Icc 1 N)
          (p := Squarefree)
    _ = N := by
        rw [Nat.card_Icc]
        omega

/-- Bridge effectif équivalent à C-04a :
    au-delà de `176`, au plus la moitié des entiers `≤ N`
    sont non-squarefree. -/
def NonSquarefreeCountLeHalfBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      (nonSquarefreeCount N : ℚ) ≤ (N : ℚ) / 2

/-- Si les non-squarefree sont au plus `N/2`, alors les squarefree
    sont au moins `N/2`. -/
theorem squarefreeCountGeHalfBridge_of_nonSquarefree_le_half
    (H : NonSquarefreeCountLeHalfBridge) :
    SquarefreeCountGeHalfBridge := by
  unfold SquarefreeCountGeHalfBridge
  unfold NonSquarefreeCountLeHalfBridge at H

  intro N hN

  have h_non : (nonSquarefreeCount N : ℚ) ≤ (N : ℚ) / 2 :=
    H hN

  have hsplit_nat :
      squarefreeCount N + nonSquarefreeCount N = N :=
    squarefreeCount_add_nonSquarefreeCount N

  have hsplit_rat :
      (squarefreeCount N : ℚ) + (nonSquarefreeCount N : ℚ)
        =
      (N : ℚ) := by
    norm_num [← Nat.cast_add, hsplit_nat]

  linarith

/-- Version consommable de C-04a sous la seule borne effective
    sur les non-squarefree. -/
theorem squarefreeCount_ge_half_of_nonSquarefree_le_half
    (H : NonSquarefreeCountLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half
    (squarefreeCountGeHalfBridge_of_nonSquarefree_le_half H)
    hN

/-!
## Réduction par crible — multiples de carrés premiers

Un entier non-squarefree possède un diviseur carré premier `p²`.
On prépare donc la borne d'union :

  nonSquarefreeCount N ≤ ∑_{p ≤ √N, p premier} ⌊N / p²⌋.

Ce bloc ne ferme pas encore cette borne : il isole proprement les deux
dettes restantes de C-04a.
-/

/-- Somme supérieure naturelle pour compter les entiers `≤ N`
    divisibles par un carré premier. -/
def primeSquareMultipleUpperSum (N : ℕ) : ℕ :=
  Finset.sum
    ((Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime)
    (fun p => N / p^2)

/-- Bridge de crible :
    tout non-squarefree `≤ N` est couvert par au moins un multiple
    de carré premier `p²`, avec `p ≤ √N`. -/
def NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge : Prop :=
  ∀ N : ℕ,
    nonSquarefreeCount N ≤ primeSquareMultipleUpperSum N

/-- Bridge effectif numérique/analytique :
    la somme des multiples de carrés premiers est au plus `N/2`
    pour `N ≥ 176`. -/
def PrimeSquareMultipleUpperSumLeHalfBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      (primeSquareMultipleUpperSum N : ℚ) ≤ (N : ℚ) / 2

/-- Les deux bridges de crible ferment le bridge effectif sur
    les non-squarefree. -/
theorem nonSquarefreeCountLeHalfBridge_of_primeSquare_sum
    (Hcount : NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge)
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge) :
    NonSquarefreeCountLeHalfBridge := by
  unfold NonSquarefreeCountLeHalfBridge
  unfold NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge at Hcount
  unfold PrimeSquareMultipleUpperSumLeHalfBridge at Hsum

  intro N hN

  have hcount_nat :
      nonSquarefreeCount N ≤ primeSquareMultipleUpperSum N :=
    Hcount N

  have hcount_rat :
      (nonSquarefreeCount N : ℚ) ≤
        (primeSquareMultipleUpperSum N : ℚ) := by
    exact_mod_cast hcount_nat

  have hsum :
      (primeSquareMultipleUpperSum N : ℚ) ≤ (N : ℚ) / 2 :=
    Hsum hN

  exact le_trans hcount_rat hsum

/-- Version consommable de C-04a sous les deux bridges de crible. -/
theorem squarefreeCount_ge_half_of_primeSquare_sum
    (Hcount : NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge)
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_nonSquarefree_le_half
    (nonSquarefreeCountLeHalfBridge_of_primeSquare_sum Hcount Hsum)
    hN

/-!
## Décomposition fine du crible C-04a

La majoration

  nonSquarefreeCount N ≤ ∑_{p ≤ √N, p premier} ⌊N / p²⌋

est séparée en deux pièces :

1. une couverture combinatoire par les ensembles de multiples de `p²` ;
2. le calcul exact du cardinal de chaque ensemble de multiples.
-/

/-- Ensemble des premiers `p` utilisés dans le crible C-04a :
    `2 ≤ p ≤ √N`. -/
def primeSquareIndexSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime

/-- Ensemble des entiers `n ≤ N` divisibles par `p²`. -/
def primeSquareMultipleSet (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => p^2 ∣ n)

/-- Bridge de couverture :
    les entiers non-squarefree sont couverts par l'union sur les multiples
    des carrés premiers. On l'exprime directement sous forme de borne
    par somme des cardinaux, ce qui autorise le surcomptage. -/
def NonSquarefreeCountLePrimeSquareMultipleCardSumBridge : Prop :=
  ∀ N : ℕ,
    nonSquarefreeCount N ≤
      Finset.sum (primeSquareIndexSet N)
        (fun p => (primeSquareMultipleSet N p).card)

/-- Bridge de cardinal exact :
    pour chaque premier `p ≤ √N`, le nombre d'entiers `≤ N`
    divisibles par `p²` est `⌊N / p²⌋`. -/
def PrimeSquareMultipleSetCardBridge : Prop :=
  ∀ N p : ℕ,
    p ∈ primeSquareIndexSet N →
      (primeSquareMultipleSet N p).card = N / p^2

/-- Les deux bridges fins reconstruisent la majoration par la somme
    `primeSquareMultipleUpperSum`. -/
theorem nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_card_sum
    (Hcover : NonSquarefreeCountLePrimeSquareMultipleCardSumBridge)
    (Hcard : PrimeSquareMultipleSetCardBridge) :
    NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge := by
  unfold NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge
  unfold NonSquarefreeCountLePrimeSquareMultipleCardSumBridge at Hcover
  unfold PrimeSquareMultipleSetCardBridge at Hcard

  intro N

  have hcover :
      nonSquarefreeCount N ≤
        Finset.sum (primeSquareIndexSet N)
          (fun p => (primeSquareMultipleSet N p).card) :=
    Hcover N

  have hsum :
      Finset.sum (primeSquareIndexSet N)
          (fun p => (primeSquareMultipleSet N p).card)
        =
      primeSquareMultipleUpperSum N := by
    unfold primeSquareIndexSet
    unfold primeSquareMultipleUpperSum
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact Hcard N p (by
      unfold primeSquareIndexSet
      exact hp)

  simpa [hsum] using hcover

/-- Version consommable de C-04a sous :
    - la couverture par les multiples de carrés premiers ;
    - le cardinal exact de ces multiples ;
    - la borne effective sur la somme. -/
theorem squarefreeCount_ge_half_of_primeSquare_card_sum
    (Hcover : NonSquarefreeCountLePrimeSquareMultipleCardSumBridge)
    (Hcard : PrimeSquareMultipleSetCardBridge)
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_primeSquare_sum
    (nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_card_sum
      Hcover
      Hcard)
    Hsum
    hN

/-!
## Cardinal exact des multiples de carrés premiers

On ferme maintenant le second morceau combinatoire du crible :
le cardinal de `{n ≤ N | p² ∣ n}` est exactement `⌊N / p²⌋`.

La preuve réutilise le lemme général déjà fermé dans
`SquarefreeDensityAsymptotic.lean`.
-/

/-- Fermeture du cardinal exact des multiples de `p²`.

    Le fait général `countMultiplesSquareNatBridge_proved` a déjà été
    fermé dans le laboratoire C-04b. Ici, on l'applique simplement à
    `p`, après avoir extrait `1 ≤ p` de `p ∈ primeSquareIndexSet N`. -/
theorem primeSquareMultipleSetCardBridge_proved :
    PrimeSquareMultipleSetCardBridge := by
  unfold PrimeSquareMultipleSetCardBridge

  intro N p hp

  unfold primeSquareIndexSet at hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpIcc, _hp_prime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp_two, _hp_sqrt⟩

  have hp_one : 1 ≤ p := by
    exact le_trans (by norm_num : (1 : ℕ) ≤ 2) hp_two

  unfold primeSquareMultipleSet

  exact countMultiplesSquareNatBridge_proved N p hp_one

/-- Version de la majoration de crible où seul reste ouvert
    le bridge de couverture. -/
theorem nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_cover
    (Hcover : NonSquarefreeCountLePrimeSquareMultipleCardSumBridge) :
    NonSquarefreeCountLePrimeSquareMultipleUpperSumBridge :=
  nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_card_sum
    Hcover
    primeSquareMultipleSetCardBridge_proved

/-- Version consommable de C-04a sous :
    - la couverture des non-squarefree par les carrés premiers ;
    - la borne effective sur la somme des multiples.

    Le cardinal exact des fibres est maintenant fermé. -/
theorem squarefreeCount_ge_half_of_primeSquare_cover_sum
    (Hcover : NonSquarefreeCountLePrimeSquareMultipleCardSumBridge)
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_primeSquare_sum
    (nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_cover Hcover)
    Hsum
    hN

/-!
## Couverture par union finie

On raffine le bridge de couverture :

1. les non-squarefree forment un sous-ensemble de l'union des multiples
   de carrés premiers ;
2. le cardinal d'une union finie est majoré par la somme des cardinaux.

Le point non trivial restant devient donc une inclusion élémentaire :
un entier non-squarefree `n ≤ N` possède un diviseur carré premier `p²`
avec `p ≤ √N`.
-/

/-- Union finie des ensembles de multiples de carrés premiers. -/
def primeSquareMultipleUnion (N : ℕ) : Finset ℕ :=
  (primeSquareIndexSet N).biUnion
    (fun p => primeSquareMultipleSet N p)

/-- Bridge d'inclusion :
    les entiers non-squarefree `≤ N` sont contenus dans l'union
    des multiples de carrés premiers. -/
def NonSquarefreeSubsetPrimeSquareMultipleUnionBridge : Prop :=
  ∀ N : ℕ,
    ((Finset.Icc 1 N).filter (fun n => ¬ Squarefree n))
      ⊆
    primeSquareMultipleUnion N

/-- Bridge cardinal-union :
    le cardinal de l'union finie est majoré par la somme des cardinaux. -/
def PrimeSquareMultipleUnionCardLeSumBridge : Prop :=
  ∀ N : ℕ,
    (primeSquareMultipleUnion N).card
      ≤
    Finset.sum (primeSquareIndexSet N)
      (fun p => (primeSquareMultipleSet N p).card)

/-- Fermeture du bridge cardinal-union par le lemme standard `Finset.card_biUnion_le`. -/
theorem primeSquareMultipleUnionCardLeSumBridge_proved :
    PrimeSquareMultipleUnionCardLeSumBridge := by
  unfold PrimeSquareMultipleUnionCardLeSumBridge

  intro N

  unfold primeSquareMultipleUnion

  exact Finset.card_biUnion_le

/-- L'inclusion dans l'union donne la majoration du cardinal
    des non-squarefree par le cardinal de cette union. -/
theorem nonSquarefreeCountLePrimeSquareMultipleUnion_of_subset
    (Hsubset : NonSquarefreeSubsetPrimeSquareMultipleUnionBridge) :
    ∀ N : ℕ,
      nonSquarefreeCount N ≤ (primeSquareMultipleUnion N).card := by
  unfold NonSquarefreeSubsetPrimeSquareMultipleUnionBridge at Hsubset

  intro N

  unfold nonSquarefreeCount

  exact Finset.card_le_card (Hsubset N)

/-- L'inclusion et l'inégalité union/somme ferment le bridge de couverture
    par somme des cardinaux. -/
theorem nonSquarefreeCountLePrimeSquareMultipleCardSumBridge_of_subset
    (Hsubset : NonSquarefreeSubsetPrimeSquareMultipleUnionBridge) :
    NonSquarefreeCountLePrimeSquareMultipleCardSumBridge := by
  unfold NonSquarefreeCountLePrimeSquareMultipleCardSumBridge

  intro N

  have h_union :
      nonSquarefreeCount N ≤ (primeSquareMultipleUnion N).card :=
    nonSquarefreeCountLePrimeSquareMultipleUnion_of_subset Hsubset N

  have h_sum :
      (primeSquareMultipleUnion N).card
        ≤
      Finset.sum (primeSquareIndexSet N)
        (fun p => (primeSquareMultipleSet N p).card) :=
    primeSquareMultipleUnionCardLeSumBridge_proved N

  exact le_trans h_union h_sum

/-- Version consommable de C-04a où il ne reste que :
    - l'inclusion des non-squarefree dans l'union des multiples de `p²` ;
    - la borne effective sur la somme. -/
theorem squarefreeCount_ge_half_of_primeSquare_subset_sum
    (Hsubset : NonSquarefreeSubsetPrimeSquareMultipleUnionBridge)
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_primeSquare_cover_sum
    (nonSquarefreeCountLePrimeSquareMultipleCardSumBridge_of_subset Hsubset)
    Hsum
    hN

end CouretUnification.Logic.H3
