/-
Couret-Unification — v38.5.12
# CouretUnification/Logic/H3/SquarefreeDensityHalf.lean

## Rôle

Laboratoire de fermeture de C-04a :
  pour N ≥ 176, squarefreeCount N ≥ N / 2.

Ce fichier ferme la borne effective C-04a.
Il réduit puis prouve la minoration via le comptage des entiers
non-squarefree, la couverture par carrés premiers, la séparation
petits premiers / queue, et une borne télescopique rationnelle.

## Statut

- Status      : proved [D]
- Front       : C-04a — minoration effective squarefree
- Couche      : Logic / H3
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

/-!
## Fermeture de l'inclusion combinatoire

On ferme l'inclusion :
  non-squarefree ≤ union des multiples de carrés premiers.

Le seul ingrédient arithmétique est déjà fermé dans le lab C-04b :
`primeSquareDivisorOfNonSquarefreeBridge_proved`.
-/

/-- Fermeture de l'inclusion des non-squarefree dans l'union
    des multiples de carrés premiers. -/
theorem nonSquarefreeSubsetPrimeSquareMultipleUnionBridge_proved :
    NonSquarefreeSubsetPrimeSquareMultipleUnionBridge := by
  unfold NonSquarefreeSubsetPrimeSquareMultipleUnionBridge

  intro N n hn

  rw [Finset.mem_filter] at hn
  rcases hn with ⟨hnIcc, hnsf⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn_one, hn_le_N⟩

  rcases primeSquareDivisorOfNonSquarefreeBridge_proved n hnsf with
    ⟨p, hp_prime, hp_square_dvd_n⟩

  have hn_pos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one hn_one

  have hp_square_le_n : p^2 ≤ n :=
    Nat.le_of_dvd hn_pos hp_square_dvd_n

  have hp_square_le_N : p^2 ≤ N :=
    le_trans hp_square_le_n hn_le_N

  have hp_le_sqrt_N : p ≤ Nat.sqrt N :=
    Nat.le_sqrt'.2 hp_square_le_N

  have hp_two : 2 ≤ p :=
    hp_prime.two_le

  have hp_index : p ∈ primeSquareIndexSet N := by
    unfold primeSquareIndexSet
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hp_two, hp_le_sqrt_N⟩
    · exact hp_prime

  have hn_multiple : n ∈ primeSquareMultipleSet N p := by
    unfold primeSquareMultipleSet
    rw [Finset.mem_filter]
    exact ⟨hnIcc, hp_square_dvd_n⟩

  unfold primeSquareMultipleUnion

  exact Finset.mem_biUnion.mpr ⟨p, hp_index, hn_multiple⟩

/-- Version consommable de C-04a où il ne reste plus que
    la borne effective sur la somme des multiples de carrés premiers. -/
theorem squarefreeCount_ge_half_of_primeSquare_effective_sum
    (Hsum : PrimeSquareMultipleUpperSumLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_primeSquare_subset_sum
    nonSquarefreeSubsetPrimeSquareMultipleUnionBridge_proved
    Hsum
    hN

/-!
## Réduction effective — petits premiers + queue entière

Le dernier verrou de C-04a est :

  ∑_{p ≤ √N, p premier} ⌊N / p²⌋ ≤ N / 2.

On le prépare en séparant :
- les petits premiers explicites `2, 3, 5, 7, 11, 13, 17` ;
- une queue entière grossière à partir de `19`.

Cette étape ne ferme pas encore l'inégalité numérique ; elle remplace
le verrou effectif par deux bridges plus lisibles.
-/

/-- Petits premiers traités explicitement dans la borne C-04a. -/
def smallPrimeSquareIndexSet : Finset ℕ :=
  ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ)

/-- Contribution explicite des petits premiers. -/
def smallPrimeSquareMultipleUpperSum (N : ℕ) : ℕ :=
  Finset.sum smallPrimeSquareIndexSet
    (fun p => N / p^2)

/-- Queue entière grossière à partir de `19`.

    Elle majore la contribution des premiers `p ≥ 19` en oubliant
    la condition de primalité. -/
def largeSquareTailMultipleUpperSum (N : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 19 (Nat.sqrt N))
    (fun d => N / d^2)

/-- Bridge de séparation effective :
    la somme sur les carrés premiers est majorée par la contribution
    des petits premiers explicites plus la queue entière. -/
def PrimeSquareMultipleUpperSumLeSmallPlusTailBridge : Prop :=
  ∀ N : ℕ,
    primeSquareMultipleUpperSum N
      ≤
    smallPrimeSquareMultipleUpperSum N
      + largeSquareTailMultipleUpperSum N

/-- Bridge effectif restant :
    petits premiers + queue entière sont au plus `N/2`
    pour `N ≥ 176`. -/
def SmallPlusTailLeHalfBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        ≤
      (N : ℚ) / 2

/-- Les deux bridges effectifs ferment la borne sur la somme
    des multiples de carrés premiers. -/
theorem primeSquareMultipleUpperSumLeHalfBridge_of_small_tail
    (Hsplit : PrimeSquareMultipleUpperSumLeSmallPlusTailBridge)
    (Hhalf : SmallPlusTailLeHalfBridge) :
    PrimeSquareMultipleUpperSumLeHalfBridge := by
  unfold PrimeSquareMultipleUpperSumLeHalfBridge
  unfold PrimeSquareMultipleUpperSumLeSmallPlusTailBridge at Hsplit
  unfold SmallPlusTailLeHalfBridge at Hhalf

  intro N hN

  have hsplit_nat :
      primeSquareMultipleUpperSum N
        ≤
      smallPrimeSquareMultipleUpperSum N
        + largeSquareTailMultipleUpperSum N :=
    Hsplit N

  have hsplit_rat :
      (primeSquareMultipleUpperSum N : ℚ)
        ≤
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ) := by
    exact_mod_cast hsplit_nat

  have hhalf :
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        ≤
      (N : ℚ) / 2 :=
    Hhalf hN

  exact le_trans hsplit_rat hhalf

/-- Version consommable de C-04a sous les deux bridges effectifs
    `petits premiers + queue`. -/
theorem squarefreeCount_ge_half_of_small_tail
    (Hsplit : PrimeSquareMultipleUpperSumLeSmallPlusTailBridge)
    (Hhalf : SmallPlusTailLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_primeSquare_effective_sum
    (primeSquareMultipleUpperSumLeHalfBridge_of_small_tail Hsplit Hhalf)
    hN

/-!
## Fermeture de la séparation petits premiers + queue

On ferme maintenant `Hsplit` :
la somme sur les premiers `p ≤ √N` est majorée par la somme des petits
premiers explicites plus la queue entière `19..√N`.

Le seul point utilisé est la classification élémentaire :
un premier `p < 19` appartient à `{2,3,5,7,11,13,17}`.
-/

/-- Les indices premiers du crible sont contenus dans :
    petits premiers explicites ∪ queue entière à partir de `19`. -/
def PrimeSquareIndexSetSubsetSmallUnionTailBridge : Prop :=
  ∀ N : ℕ,
    primeSquareIndexSet N
      ⊆
    smallPrimeSquareIndexSet ∪ Finset.Icc 19 (Nat.sqrt N)

/-- Fermeture de l'inclusion des indices. -/
theorem primeSquareIndexSetSubsetSmallUnionTailBridge_proved :
    PrimeSquareIndexSetSubsetSmallUnionTailBridge := by
  unfold PrimeSquareIndexSetSubsetSmallUnionTailBridge

  intro N p hp

  unfold primeSquareIndexSet at hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpIcc, hp_prime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp_two, hp_sqrt⟩

  rw [Finset.mem_union]

  by_cases hp_lt_19 : p < 19

  · left

    have hp_cases :
        p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨
        p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨
        p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨
        p = 17 ∨ p = 18 := by
      omega

    rcases hp_cases with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl

    · exact (by decide : 2 ∈ smallPrimeSquareIndexSet)
    · exact (by decide : 3 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 4) hp_prime
    · exact (by decide : 5 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 6) hp_prime
    · exact (by decide : 7 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 8) hp_prime
    · exfalso
      exact (by decide : ¬ Nat.Prime 9) hp_prime
    · exfalso
      exact (by decide : ¬ Nat.Prime 10) hp_prime
    · exact (by decide : 11 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 12) hp_prime
    · exact (by decide : 13 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 14) hp_prime
    · exfalso
      exact (by decide : ¬ Nat.Prime 15) hp_prime
    · exfalso
      exact (by decide : ¬ Nat.Prime 16) hp_prime
    · exact (by decide : 17 ∈ smallPrimeSquareIndexSet)
    · exfalso
      exact (by decide : ¬ Nat.Prime 18) hp_prime

  · right
    rw [Finset.mem_Icc]
    exact ⟨le_of_not_gt hp_lt_19, hp_sqrt⟩

/-- Les petits premiers explicites sont disjoints de la queue `19..√N`. -/
theorem smallPrimeSquareIndexSet_disjoint_largeTail
    (N : ℕ) :
    Disjoint smallPrimeSquareIndexSet (Finset.Icc 19 (Nat.sqrt N)) := by
  rw [Finset.disjoint_left]

  intro p hp_small hp_tail

  rw [Finset.mem_Icc] at hp_tail
  have hp_ge_19 : 19 ≤ p := hp_tail.1

  unfold smallPrimeSquareIndexSet at hp_small
  simp at hp_small

  rcases hp_small with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

/-- Fermeture de la séparation :
    somme sur les premiers ≤ petits premiers + queue entière. -/
theorem primeSquareMultipleUpperSumLeSmallPlusTailBridge_proved :
    PrimeSquareMultipleUpperSumLeSmallPlusTailBridge := by
  unfold PrimeSquareMultipleUpperSumLeSmallPlusTailBridge

  intro N

  unfold primeSquareMultipleUpperSum
  unfold smallPrimeSquareMultipleUpperSum
  unfold largeSquareTailMultipleUpperSum

  have hsubset :
      ((Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime)
        ⊆
      smallPrimeSquareIndexSet ∪ Finset.Icc 19 (Nat.sqrt N) := by
    intro p hp
    exact
      (primeSquareIndexSetSubsetSmallUnionTailBridge_proved N)
        (by
          unfold primeSquareIndexSet
          exact hp)

  have hsum_subset :
      Finset.sum ((Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime)
          (fun p => N / p^2)
        ≤
      Finset.sum
          (smallPrimeSquareIndexSet ∪ Finset.Icc 19 (Nat.sqrt N))
          (fun p => N / p^2) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hsubset
      (by
        intro p hp_union hp_not_left
        exact Nat.zero_le _)

  have hsum_union :
      Finset.sum
          (smallPrimeSquareIndexSet ∪ Finset.Icc 19 (Nat.sqrt N))
          (fun p => N / p^2)
        =
      Finset.sum smallPrimeSquareIndexSet (fun p => N / p^2)
        +
      Finset.sum (Finset.Icc 19 (Nat.sqrt N)) (fun p => N / p^2) := by
    rw [Finset.sum_union (smallPrimeSquareIndexSet_disjoint_largeTail N)]

  exact le_trans hsum_subset (by
    rw [hsum_union])

/-- Version consommable de C-04a où il ne reste que
    la borne effective numérique `SmallPlusTailLeHalfBridge`. -/
theorem squarefreeCount_ge_half_of_small_tail_effective
    (Hhalf : SmallPlusTailLeHalfBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_small_tail
    primeSquareMultipleUpperSumLeSmallPlusTailBridge_proved
    Hhalf
    hN

/-!
## Réduction du verrou effectif à deux bornes de coefficients

Après fermeture de la séparation petits premiers + queue, le dernier verrou
`SmallPlusTailLeHalfBridge` est réduit à deux estimations de coefficients :

1. petits premiers :
   `∑ ⌊N / p²⌋ ≤ N * ∑ 1/p²`

2. queue :
   `∑_{19 ≤ d ≤ √N} ⌊N / d²⌋ ≤ N / 18`

Le coefficient total est alors explicitement vérifié :
  ∑_{p ∈ {2,3,5,7,11,13,17}} 1/p² + 1/18 ≤ 1/2.
-/

/-- Coefficient rationnel associé aux petits premiers explicites. -/
def smallPrimeSquareRationalCoefficient : ℚ :=
  Finset.sum smallPrimeSquareIndexSet
    (fun p => (1 : ℚ) / ((p : ℚ)^2))

/-- Coefficient rationnel grossier pour la queue `d ≥ 19`.

    Il correspond à la borne intégrale classique :
    `∑_{d ≥ 19} 1/d² ≤ ∫_{18}^{∞} dx/x² = 1/18`. -/
def largeSquareTailRationalCoefficient : ℚ :=
  1 / 18

/-- Bridge : les petits premiers sont contrôlés par leur coefficient
    rationnel explicite. -/
def SmallPrimeSquareMultipleUpperSumLeCoefficientBridge : Prop :=
  ∀ N : ℕ,
    (smallPrimeSquareMultipleUpperSum N : ℚ)
      ≤
    (N : ℚ) * smallPrimeSquareRationalCoefficient

/-- Bridge : la queue entière est contrôlée par le coefficient `1/18`. -/
def LargeSquareTailMultipleUpperSumLeCoefficientBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      (largeSquareTailMultipleUpperSum N : ℚ)
        ≤
      (N : ℚ) * largeSquareTailRationalCoefficient

/-- Bridge intermédiaire :
    petits premiers + queue sont contrôlés par la somme des coefficients. -/
def SmallPlusTailLeCoefficientBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        ≤
      (N : ℚ) *
        (smallPrimeSquareRationalCoefficient
          + largeSquareTailRationalCoefficient)

/-- Le coefficient total est au plus `1/2`. -/
def SmallTailCoefficientLeHalfBridge : Prop :=
  smallPrimeSquareRationalCoefficient
    + largeSquareTailRationalCoefficient
      ≤
    (1 : ℚ) / 2

/-- Fermeture numérique du coefficient total. -/
theorem smallTailCoefficientLeHalfBridge_proved :
    SmallTailCoefficientLeHalfBridge := by
  unfold SmallTailCoefficientLeHalfBridge
  unfold smallPrimeSquareRationalCoefficient
  unfold largeSquareTailRationalCoefficient
  unfold smallPrimeSquareIndexSet
  norm_num

/-- Les deux bornes de coefficients impliquent le bridge intermédiaire. -/
theorem smallPlusTailLeCoefficientBridge_of_parts
    (Hsmall : SmallPrimeSquareMultipleUpperSumLeCoefficientBridge)
    (Htail : LargeSquareTailMultipleUpperSumLeCoefficientBridge) :
    SmallPlusTailLeCoefficientBridge := by
  unfold SmallPlusTailLeCoefficientBridge
  unfold SmallPrimeSquareMultipleUpperSumLeCoefficientBridge at Hsmall
  unfold LargeSquareTailMultipleUpperSumLeCoefficientBridge at Htail

  intro N hN

  have hsmall :
      (smallPrimeSquareMultipleUpperSum N : ℚ)
        ≤
      (N : ℚ) * smallPrimeSquareRationalCoefficient :=
    Hsmall N

  have htail :
      (largeSquareTailMultipleUpperSum N : ℚ)
        ≤
      (N : ℚ) * largeSquareTailRationalCoefficient :=
    Htail hN

  have hcast :
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        =
      (smallPrimeSquareMultipleUpperSum N : ℚ)
        + (largeSquareTailMultipleUpperSum N : ℚ) := by
    norm_num [Nat.cast_add]

  calc
    ((smallPrimeSquareMultipleUpperSum N
        + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        =
      (smallPrimeSquareMultipleUpperSum N : ℚ)
        + (largeSquareTailMultipleUpperSum N : ℚ) := hcast
    _ ≤
      (N : ℚ) * smallPrimeSquareRationalCoefficient
        + (N : ℚ) * largeSquareTailRationalCoefficient := by
        exact add_le_add hsmall htail
    _ =
      (N : ℚ) *
        (smallPrimeSquareRationalCoefficient
          + largeSquareTailRationalCoefficient) := by
        ring

/-- Le contrôle par coefficient total ferme `SmallPlusTailLeHalfBridge`. -/
theorem smallPlusTailLeHalfBridge_of_coefficient
    (Hcoeff : SmallPlusTailLeCoefficientBridge)
    (Hhalf : SmallTailCoefficientLeHalfBridge) :
    SmallPlusTailLeHalfBridge := by
  unfold SmallPlusTailLeHalfBridge
  unfold SmallPlusTailLeCoefficientBridge at Hcoeff
  unfold SmallTailCoefficientLeHalfBridge at Hhalf

  intro N hN

  have hcoeff :
      ((smallPrimeSquareMultipleUpperSum N
          + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        ≤
      (N : ℚ) *
        (smallPrimeSquareRationalCoefficient
          + largeSquareTailRationalCoefficient) :=
    Hcoeff hN

  have hN_nonneg : (0 : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast Nat.zero_le N

  have hmul :
      (N : ℚ) *
          (smallPrimeSquareRationalCoefficient
            + largeSquareTailRationalCoefficient)
        ≤
      (N : ℚ) * ((1 : ℚ) / 2) := by
    exact mul_le_mul_of_nonneg_left Hhalf hN_nonneg

  calc
    ((smallPrimeSquareMultipleUpperSum N
        + largeSquareTailMultipleUpperSum N : ℕ) : ℚ)
        ≤
      (N : ℚ) *
        (smallPrimeSquareRationalCoefficient
          + largeSquareTailRationalCoefficient) := hcoeff
    _ ≤
      (N : ℚ) * ((1 : ℚ) / 2) := hmul
    _ =
      (N : ℚ) / 2 := by
        ring

/-- Version de `SmallPlusTailLeHalfBridge` où il ne reste que
    les deux bornes séparées : petits premiers et queue. -/
theorem smallPlusTailLeHalfBridge_of_coefficient_parts
    (Hsmall : SmallPrimeSquareMultipleUpperSumLeCoefficientBridge)
    (Htail : LargeSquareTailMultipleUpperSumLeCoefficientBridge) :
    SmallPlusTailLeHalfBridge :=
  smallPlusTailLeHalfBridge_of_coefficient
    (smallPlusTailLeCoefficientBridge_of_parts Hsmall Htail)
    smallTailCoefficientLeHalfBridge_proved

/-- Version consommable de C-04a où il reste exactement deux verrous :
    - la borne coefficientielle des petits premiers ;
    - la borne coefficientielle de la queue. -/
theorem squarefreeCount_ge_half_of_coefficient_parts
    (Hsmall : SmallPrimeSquareMultipleUpperSumLeCoefficientBridge)
    (Htail : LargeSquareTailMultipleUpperSumLeCoefficientBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_small_tail_effective
    (smallPlusTailLeHalfBridge_of_coefficient_parts Hsmall Htail)
    hN

/-!
## Fermeture de la borne coefficientielle des petits premiers

On ferme le verrou `Hsmall` :

  ∑_{p ∈ petits premiers} ⌊N / p²⌋
    ≤
  N * ∑_{p ∈ petits premiers} 1 / p².

L'ingrédient élémentaire est :
  ⌊N/q⌋ ≤ N/q
dans `ℚ`, pour `q > 0`.
-/

/-- Inégalité élémentaire : la division euclidienne est majorée
    par la division rationnelle correspondante. -/
theorem natDivCastLeRatDiv
    (N q : ℕ)
    (hq : 0 < q) :
    ((N / q : ℕ) : ℚ) ≤ (N : ℚ) / (q : ℚ) := by
  have hq_pos : (0 : ℚ) < (q : ℚ) := by
    exact_mod_cast hq

  have hmul :
      ((N / q : ℕ) : ℚ) * (q : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast Nat.div_mul_le_self N q

  rw [le_div_iff₀ hq_pos]
  exact hmul

/-- Version spécialisée à `q = p²`. -/
theorem natDivPrimeSquareCastLeRat
    (N p : ℕ)
    (hp : 0 < p) :
    ((N / p^2 : ℕ) : ℚ)
      ≤
    (N : ℚ) * ((1 : ℚ) / ((p : ℚ)^2)) := by
  have hp_sq_pos : 0 < p^2 := by
    exact pow_pos hp 2

  calc
    ((N / p^2 : ℕ) : ℚ)
        ≤
      (N : ℚ) / ((p^2 : ℕ) : ℚ) :=
        natDivCastLeRatDiv N (p^2) hp_sq_pos
    _ =
      (N : ℚ) * ((1 : ℚ) / ((p : ℚ)^2)) := by
        norm_num [div_eq_mul_inv, pow_two]

/-- Fermeture de la borne coefficientielle des petits premiers. -/
theorem smallPrimeSquareMultipleUpperSumLeCoefficientBridge_proved :
    SmallPrimeSquareMultipleUpperSumLeCoefficientBridge := by
  unfold SmallPrimeSquareMultipleUpperSumLeCoefficientBridge

  intro N

  unfold smallPrimeSquareMultipleUpperSum
  unfold smallPrimeSquareRationalCoefficient

  calc
    ((Finset.sum smallPrimeSquareIndexSet
        (fun p => N / p^2) : ℕ) : ℚ)
        =
      Finset.sum smallPrimeSquareIndexSet
        (fun p => ((N / p^2 : ℕ) : ℚ)) := by
        norm_num [Nat.cast_sum]
    _ ≤
      Finset.sum smallPrimeSquareIndexSet
        (fun p => (N : ℚ) * ((1 : ℚ) / ((p : ℚ)^2))) := by
        refine Finset.sum_le_sum ?_
        intro p hp_mem

        have hp_pos : 0 < p := by
          unfold smallPrimeSquareIndexSet at hp_mem
          simp at hp_mem
          omega

        exact natDivPrimeSquareCastLeRat N p hp_pos
    _ =
      (N : ℚ) *
        Finset.sum smallPrimeSquareIndexSet
          (fun p => (1 : ℚ) / ((p : ℚ)^2)) := by
        rw [Finset.mul_sum]

/-!
## Réduction de la queue à une borne coefficientielle finie

On traite maintenant la queue :

  ∑_{19 ≤ d ≤ √N} ⌊N / d²⌋.

Premier pas : remplacer chaque plancher par sa majoration rationnelle :

  ⌊N / d²⌋ ≤ N / d².

Il restera ensuite uniquement la borne finie :

  ∑_{19 ≤ d ≤ √N} 1 / d² ≤ 1 / 18.
-/

/-- Coefficient rationnel fini associé à la queue `19..√N`. -/
def largeSquareTailFiniteRationalCoefficient (N : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 19 (Nat.sqrt N))
    (fun d => (1 : ℚ) / ((d : ℚ)^2))

/-- Bridge : la queue des multiples est contrôlée par son coefficient fini. -/
def LargeSquareTailMultipleUpperSumLeFiniteCoefficientBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      (largeSquareTailMultipleUpperSum N : ℚ)
        ≤
      (N : ℚ) * largeSquareTailFiniteRationalCoefficient N

/-- Bridge restant : le coefficient fini de queue est borné par `1/18`. -/
def LargeSquareTailFiniteCoefficientLeBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      largeSquareTailFiniteRationalCoefficient N
        ≤
      largeSquareTailRationalCoefficient

/-- Fermeture de la majoration de la queue par son coefficient fini. -/
theorem largeSquareTailMultipleUpperSumLeFiniteCoefficientBridge_proved :
    LargeSquareTailMultipleUpperSumLeFiniteCoefficientBridge := by
  unfold LargeSquareTailMultipleUpperSumLeFiniteCoefficientBridge

  intro N hN

  unfold largeSquareTailMultipleUpperSum
  unfold largeSquareTailFiniteRationalCoefficient

  calc
    ((Finset.sum (Finset.Icc 19 (Nat.sqrt N))
        (fun d => N / d^2) : ℕ) : ℚ)
        =
      Finset.sum (Finset.Icc 19 (Nat.sqrt N))
        (fun d => ((N / d^2 : ℕ) : ℚ)) := by
        norm_num [Nat.cast_sum]
    _ ≤
      Finset.sum (Finset.Icc 19 (Nat.sqrt N))
        (fun d => (N : ℚ) * ((1 : ℚ) / ((d : ℚ)^2))) := by
        refine Finset.sum_le_sum ?_
        intro d hd

        rcases Finset.mem_Icc.mp hd with ⟨hd_ge_19, _hd_sqrt⟩

        have hd_pos : 0 < d :=
          lt_of_lt_of_le (by norm_num : 0 < 19) hd_ge_19

        exact natDivPrimeSquareCastLeRat N d hd_pos
    _ =
      (N : ℚ) *
        Finset.sum (Finset.Icc 19 (Nat.sqrt N))
          (fun d => (1 : ℚ) / ((d : ℚ)^2)) := by
        rw [Finset.mul_sum]

/-- Le coefficient fini `≤ 1/18` ferme la borne coefficientielle de queue. -/
theorem largeSquareTailMultipleUpperSumLeCoefficientBridge_of_finite
    (Hfinite : LargeSquareTailFiniteCoefficientLeBridge) :
    LargeSquareTailMultipleUpperSumLeCoefficientBridge := by
  unfold LargeSquareTailMultipleUpperSumLeCoefficientBridge
  unfold LargeSquareTailFiniteCoefficientLeBridge at Hfinite

  intro N hN

  have htail :
      (largeSquareTailMultipleUpperSum N : ℚ)
        ≤
      (N : ℚ) * largeSquareTailFiniteRationalCoefficient N :=
    largeSquareTailMultipleUpperSumLeFiniteCoefficientBridge_proved hN

  have hfinite :
      largeSquareTailFiniteRationalCoefficient N
        ≤
      largeSquareTailRationalCoefficient :=
    Hfinite hN

  have hN_nonneg : (0 : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast Nat.zero_le N

  have hmul :
      (N : ℚ) * largeSquareTailFiniteRationalCoefficient N
        ≤
      (N : ℚ) * largeSquareTailRationalCoefficient := by
    exact mul_le_mul_of_nonneg_left hfinite hN_nonneg

  exact le_trans htail hmul

/-- Version de C-04a où il ne reste plus que la borne finie
    `∑_{19 ≤ d ≤ √N} 1/d² ≤ 1/18`. -/
theorem squarefreeCount_ge_half_of_tail_finite_coefficient
    (Hfinite : LargeSquareTailFiniteCoefficientLeBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_coefficient_parts
    smallPrimeSquareMultipleUpperSumLeCoefficientBridge_proved
    (largeSquareTailMultipleUpperSumLeCoefficientBridge_of_finite Hfinite)
    hN

/-!
## Queue : réduction télescopique

On introduit la majoration terme à terme :

  1 / d² ≤ 1 / (d - 1) - 1 / d,

valable pour `d ≥ 2`.

Ainsi, le coefficient fini de queue

  ∑_{19 ≤ d ≤ √N} 1 / d²

est majoré par une somme télescopique. Il restera ensuite seulement à
fermer cette somme télescopique par `1 / 18`.
-/

/-- Coefficient télescopique associé à la queue `19..√N`. -/
def largeSquareTailTelescopingCoefficient (N : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 19 (Nat.sqrt N))
    (fun d =>
      (1 : ℚ) / (((d - 1 : ℕ) : ℚ))
        - (1 : ℚ) / (d : ℚ))

/-- Inégalité élémentaire de télescopage :
    `1/d² ≤ 1/(d-1) - 1/d`, pour `d ≥ 2`. -/
theorem ratInvSquareLeTelescopingStep
    (d : ℕ)
    (hd : 2 ≤ d) :
    (1 : ℚ) / ((d : ℚ)^2)
      ≤
    (1 : ℚ) / (((d - 1 : ℕ) : ℚ))
      - (1 : ℚ) / (d : ℚ) := by
  have hd_pos_nat : 0 < d := by
    exact lt_of_lt_of_le (by norm_num : 0 < 2) hd

  have hd_gt_one_nat : 1 < d := by
    exact lt_of_lt_of_le (by norm_num : 1 < 2) hd

  have hdm1_pos_nat : 0 < d - 1 := by
    exact Nat.sub_pos_of_lt hd_gt_one_nat

  have hdq_pos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast hd_pos_nat

  have hdm1q_pos : (0 : ℚ) < (((d - 1 : ℕ) : ℚ)) := by
    exact_mod_cast hdm1_pos_nat

  have hdq_ne : (d : ℚ) ≠ 0 :=
    ne_of_gt hdq_pos

  have hdm1q_ne : (((d - 1 : ℕ) : ℚ)) ≠ 0 :=
    ne_of_gt hdm1q_pos

  have hdm1_cast :
      (((d - 1 : ℕ) : ℚ)) = (d : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num

  rw [hdm1_cast] at hdm1q_ne ⊢

  have hdm1_expr_pos : (0 : ℚ) < (d : ℚ) - 1 := by
    rw [← hdm1_cast]
    exact hdm1q_pos

  field_simp [hdq_ne, hdm1q_ne, pow_two]
  nlinarith [hdq_pos, hdm1_expr_pos]

/-- Bridge : le coefficient fini de queue est majoré par
    le coefficient télescopique. -/
def LargeSquareTailFiniteCoefficientLeTelescopingBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      largeSquareTailFiniteRationalCoefficient N
        ≤
      largeSquareTailTelescopingCoefficient N

/-- Fermeture terme à terme de la majoration par la somme télescopique. -/
theorem largeSquareTailFiniteCoefficientLeTelescopingBridge_proved :
    LargeSquareTailFiniteCoefficientLeTelescopingBridge := by
  unfold LargeSquareTailFiniteCoefficientLeTelescopingBridge

  intro N hN

  unfold largeSquareTailFiniteRationalCoefficient
  unfold largeSquareTailTelescopingCoefficient

  refine Finset.sum_le_sum ?_

  intro d hd

  rcases Finset.mem_Icc.mp hd with ⟨hd_ge_19, _hd_sqrt⟩

  have hd_two : 2 ≤ d :=
    le_trans (by norm_num : 2 ≤ 19) hd_ge_19

  exact ratInvSquareLeTelescopingStep d hd_two

/-- Bridge restant :
    la somme télescopique de queue est bornée par `1/18`. -/
def LargeSquareTailTelescopingCoefficientLeBridge : Prop :=
  ∀ {N : ℕ},
    176 ≤ N →
      largeSquareTailTelescopingCoefficient N
        ≤
      largeSquareTailRationalCoefficient

/-- La borne télescopique ferme le coefficient fini de queue. -/
theorem largeSquareTailFiniteCoefficientLeBridge_of_telescoping
    (Htel : LargeSquareTailTelescopingCoefficientLeBridge) :
    LargeSquareTailFiniteCoefficientLeBridge := by
  unfold LargeSquareTailFiniteCoefficientLeBridge
  unfold LargeSquareTailTelescopingCoefficientLeBridge at Htel

  intro N hN

  have hfinite_tel :
      largeSquareTailFiniteRationalCoefficient N
        ≤
      largeSquareTailTelescopingCoefficient N :=
    largeSquareTailFiniteCoefficientLeTelescopingBridge_proved hN

  have htel :
      largeSquareTailTelescopingCoefficient N
        ≤
      largeSquareTailRationalCoefficient :=
    Htel hN

  exact le_trans hfinite_tel htel

/-- Version de C-04a où il ne reste plus que la borne télescopique
    `largeSquareTailTelescopingCoefficient N ≤ 1/18`. -/
theorem squarefreeCount_ge_half_of_tail_telescoping
    (Htel : LargeSquareTailTelescopingCoefficientLeBridge)
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half_of_tail_finite_coefficient
    (largeSquareTailFiniteCoefficientLeBridge_of_telescoping Htel)
    hN

/-!
## Fermeture de la somme télescopique

On ferme le dernier verrou effectif :

  ∑_{19 ≤ d ≤ √N} (1/(d-1) - 1/d) ≤ 1/18.

La preuve passe par une identité exacte sur `Icc 19 (18+k)` :
la somme vaut `1/18 - 1/(18+k)`.
-/

/-- Identité télescopique exacte sur l'intervalle `19..18+k`. -/
theorem largeSquareTailTelescopingIcc_eq
    (k : ℕ) :
    Finset.sum (Finset.Icc 19 (18 + k))
      (fun d =>
        (1 : ℚ) / (((d - 1 : ℕ) : ℚ))
          - (1 : ℚ) / (d : ℚ))
      =
    (1 : ℚ) / 18 - (1 : ℚ) / ((18 + k : ℕ) : ℚ) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hIcc :
          Finset.Icc 19 (18 + (k + 1))
            =
          insert (18 + (k + 1)) (Finset.Icc 19 (18 + k)) := by
        ext d
        simp [Finset.mem_Icc]
        omega

      have hnot :
          18 + (k + 1) ∉ Finset.Icc 19 (18 + k) := by
        simp [Finset.mem_Icc]

      rw [hIcc]
      rw [Finset.sum_insert hnot]
      rw [ih]

      have hsub :
          18 + (k + 1) - 1 = 18 + k := by
        omega

      calc
        (1 / (((18 + (k + 1) - 1 : ℕ) : ℚ))
            - 1 / (((18 + (k + 1) : ℕ) : ℚ)))
            + (1 / 18 - 1 / (((18 + k : ℕ) : ℚ)))
            =
          (1 / (((18 + k : ℕ) : ℚ))
            - 1 / (((18 + (k + 1) : ℕ) : ℚ)))
            + (1 / 18 - 1 / (((18 + k : ℕ) : ℚ))) := by
            rw [hsub]
        _ =
          1 / 18 - 1 / (((18 + (k + 1) : ℕ) : ℚ)) := by
            ring

/-- Fermeture de la borne télescopique de queue. -/
theorem largeSquareTailTelescopingCoefficientLeBridge_proved :
    LargeSquareTailTelescopingCoefficientLeBridge := by
  unfold LargeSquareTailTelescopingCoefficientLeBridge

  intro N hN

  unfold largeSquareTailTelescopingCoefficient
  unfold largeSquareTailRationalCoefficient

  by_cases hsmall : Nat.sqrt N < 19

  · have hsum_zero :
        Finset.sum (Finset.Icc 19 (Nat.sqrt N))
          (fun d =>
            (1 : ℚ) / (((d - 1 : ℕ) : ℚ))
              - (1 : ℚ) / (d : ℚ))
          =
        0 := by
      refine Finset.sum_eq_zero ?_
      intro d hd
      exfalso
      rcases Finset.mem_Icc.mp hd with ⟨hd_ge_19, hd_le_sqrt⟩
      omega

    rw [hsum_zero]
    norm_num

  · have hsqrt_ge_18 : 18 ≤ Nat.sqrt N := by
      omega

    have hrepr :
        18 + (Nat.sqrt N - 18) = Nat.sqrt N := by
      omega

    rw [← hrepr]
    rw [largeSquareTailTelescopingIcc_eq (Nat.sqrt N - 18)]

    have hnonneg :
        (0 : ℚ)
          ≤
        (1 : ℚ) / (((18 + (Nat.sqrt N - 18) : ℕ) : ℚ)) := by
      positivity

    linarith

/-- Fermeture du coefficient fini de queue. -/
theorem largeSquareTailFiniteCoefficientLeBridge_proved :
    LargeSquareTailFiniteCoefficientLeBridge :=
  largeSquareTailFiniteCoefficientLeBridge_of_telescoping
    largeSquareTailTelescopingCoefficientLeBridge_proved

/-- Fermeture de la borne coefficientielle de queue. -/
theorem largeSquareTailMultipleUpperSumLeCoefficientBridge_proved :
    LargeSquareTailMultipleUpperSumLeCoefficientBridge :=
  largeSquareTailMultipleUpperSumLeCoefficientBridge_of_finite
    largeSquareTailFiniteCoefficientLeBridge_proved

/-- Fermeture de `SmallPlusTailLeHalfBridge`. -/
theorem smallPlusTailLeHalfBridge_proved :
    SmallPlusTailLeHalfBridge :=
  smallPlusTailLeHalfBridge_of_coefficient_parts
    smallPrimeSquareMultipleUpperSumLeCoefficientBridge_proved
    largeSquareTailMultipleUpperSumLeCoefficientBridge_proved

/-- Fermeture de la borne effective sur la somme des multiples
    de carrés premiers. -/
theorem primeSquareMultipleUpperSumLeHalfBridge_proved :
    PrimeSquareMultipleUpperSumLeHalfBridge :=
  primeSquareMultipleUpperSumLeHalfBridge_of_small_tail
    primeSquareMultipleUpperSumLeSmallPlusTailBridge_proved
    smallPlusTailLeHalfBridge_proved

/-- Fermeture du bridge effectif C-04a. -/
theorem squarefreeCountGeHalfBridge_proved :
    SquarefreeCountGeHalfBridge := by
  apply squarefreeCountGeHalfBridge_of_nonSquarefree_le_half

  apply nonSquarefreeCountLeHalfBridge_of_primeSquare_sum

  · exact
      nonSquarefreeCountLePrimeSquareMultipleUpperSumBridge_of_cover
        (nonSquarefreeCountLePrimeSquareMultipleCardSumBridge_of_subset
          nonSquarefreeSubsetPrimeSquareMultipleUnionBridge_proved)

  · exact primeSquareMultipleUpperSumLeHalfBridge_proved

/-- Théorème final C-04a :
    pour `N ≥ 176`, au moins la moitié des entiers `≤ N`
    sont squarefree. -/
theorem squarefreeCount_ge_half_final
    {N : ℕ}
    (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N :=
  squarefreeCount_ge_half
    squarefreeCountGeHalfBridge_proved
    hN

end CouretUnification.Logic.H3
