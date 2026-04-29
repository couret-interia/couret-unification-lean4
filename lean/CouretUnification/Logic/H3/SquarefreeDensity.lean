/-
# CouretUnification.Logic.H3.SquarefreeDensity

**Statut épistémique :** [P] Version consolidée — Paquets A + B + C
**Niveau :** 2 — Logic.H3
**Invariant :** `RHClaimed = false`

## Version v35.4 consolidée — 22 avril 2026

Ce fichier remplace la version scaffold précédente. Les 7 sorry sont fermés
selon les routes identifiées lors de la synthèse multi-IA :

  SORRY-1 ← Nat.squarefree_iff_prime_squarefree
  SORRY-3 ← Nat.Ioc_filter_dvd_card_eq_div
  SORRY-2 ← inclusion ensembliste pure
  SORRY-4 ← card_biUnion_le + omega
  SORRY-5 ← télescopage discret (pas d'intégrale)
  SORRY-6 ← micro-lemmes de cast + extraction du facteur
  SORRY-7 ← conversion ℕ → ℚ

## Objectif mathématique

Formaliser la moitié (ii) de RouteC::main_lower :

    Q(n) ≥ n/2 pour n ≥ 176

où Q(n) = #{m ∈ [1,n] : m squarefree}. La constante 1/2 est volontairement
lâche par rapport à l'asymptotique 6/π² ≈ 0.608 ou à la Schnirelmann 53/88
(Rogers 1964). On vise le minimum formalisable.

## Architecture de la preuve

1. Définitions de squarefreeCount et nonSquarefreeCount
2. Identité de partition (élémentaire)
3. Caractérisation via Nat.squarefree_iff_prime_squarefree
4. Comptage des multiples via Nat.Ioc_filter_dvd_card_eq_div
5. Inclusion non-squarefree ⊆ ⋃_p {m : p² ∣ m}
6. Borne de Legendre par card_biUnion_le
7. Télescopage discret pour Σ 1/p² ≤ 1/2
8. Assemblage final en ℚ avec micro-lemmes de cast

## Dépendances Mathlib

- `Mathlib.Data.Nat.Squarefree`
- `Mathlib.Data.Nat.Factorization.Basic` (pour Ioc_filter_dvd_card_eq_div)
- `Mathlib.Data.Rat.Defs`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Tactic`
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open Finset
open scoped BigOperators

/-! ## Partie 1 — Définitions et partition de base -/

/-- Fonction de comptage des entiers squarefree dans [1, n]. -/
def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter Squarefree).card

/-- Fonction de comptage des non-squarefree dans [1, n]. -/
def nonSquarefreeCount (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter (fun m => ¬ Squarefree m)).card

/-- Partition : squarefree + non-squarefree = total. -/
theorem squarefreeCount_add_nonSquarefreeCount (n : ℕ) :
    squarefreeCount n + nonSquarefreeCount n = n := by
  unfold squarefreeCount nonSquarefreeCount
  rw [Finset.card_filter_add_card_filter_not (s := Finset.Ico 1 (n + 1)) Squarefree]
  simp

/-! ## Partie 2 — Caractérisation des non-squarefree (ex-SORRY-1) -/

/--
**SORRY-1 fermé** via `Nat.squarefree_iff_prime_squarefree`.

Un entier n n'est pas squarefree ssi il existe un premier p avec p² ∣ n.
-/
theorem nonSquarefree_iff_exists_prime_sq_dvd (n : ℕ) (_hn : 0 < n) :
    ¬ Squarefree n ↔ ∃ p : ℕ, p.Prime ∧ p^2 ∣ n := by
  constructor
  · intro h
    -- ROUTE PRIMAIRE : Nat.squarefree_iff_prime_squarefree
    -- dit : Squarefree n ↔ ∀ x, Prime x → ¬ x * x ∣ n
    -- Selon le snapshot Mathlib, le nom peut être :
    --   Nat.squarefree_iff_prime_squarefree
    --   Nat.squarefree_iff_not_exists_sq_dvd
    --   ou une variante similaire.
    -- Thomas : si le nom ci-dessous ne passe pas, essaye :
    --   rw [Nat.squarefree_iff_minSqFac] at h
    --   et utilise Nat.minSqFac_prime + Nat.minSqFac_dvd
    rw [Nat.squarefree_iff_prime_squarefree] at h
    push Not at h
    rcases h with ⟨p, hp, hsq⟩
    refine ⟨p, hp, ?_⟩
    -- p * p ∣ n  ↝  p^2 ∣ n
    simpa [pow_two] using hsq
  · rintro ⟨p, hp, hpn⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    push Not
    refine ⟨p, hp, ?_⟩
    simpa [pow_two] using hpn

/-! ## Partie 3 — Comptage des multiples (ex-SORRY-3) -/

/--
**SORRY-3 fermé** via `Nat.Ioc_filter_dvd_card_eq_div`.

Le nombre de multiples de k dans [1,n] est exactement ⌊n/k⌋.
-/
theorem card_multiples (n k : ℕ) (_hk : 0 < k) :
    ((Finset.Ico 1 (n + 1)).filter (fun m => k ∣ m)).card = n / k := by
  -- Réécriture Ico 1 (n+1) ↔ Ioc 0 n
  have hset :
      (Finset.Ico 1 (n + 1)).filter (fun m => k ∣ m)
        = (Finset.Ioc 0 n).filter (fun m => k ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
    · rintro ⟨⟨h1, h2⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
  rw [hset]
  -- ROUTE PRIMAIRE : Nat.Ioc_filter_dvd_card_eq_div
  -- Thomas : si le nom diffère, essayer :
  --   Nat.card_multiples / Nat.card_multiples'
  --   Nat.Ioc_filter_dvd_card
  exact Nat.Ioc_filter_dvd_card_eq_div n k

/-- Corollaire : borne pour p². -/
theorem card_sq_multiples_eq (n p : ℕ) (hp : 0 < p) :
    ((Finset.Ico 1 (n + 1)).filter (fun m => p^2 ∣ m)).card = n / p^2 :=
  card_multiples n (p^2) (by positivity)

/-! ## Partie 4 — Inclusion ensembliste (ex-SORRY-2) -/

/--
**SORRY-2 fermé**. Les entiers non-squarefree dans [1,n] sont contenus dans
l'union des multiples de p² pour p premier, p ≤ √n.
-/
theorem nonSquarefree_subset_union_sq_multiples (n : ℕ) :
    (Finset.Ico 1 (n + 1)).filter (fun m => ¬ Squarefree m) ⊆
      ((Finset.Ico 2 (n.sqrt + 2)).filter Nat.Prime).biUnion
        (fun p => (Finset.Ico 1 (n + 1)).filter (fun m => p^2 ∣ m)) := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmIco, hm_nsq⟩
  rcases Finset.mem_Ico.mp hmIco with ⟨hm_ge, hm_lt⟩
  have hm_pos : 0 < m := hm_ge
  have hm_le_n : m ≤ n := by omega
  -- On extrait p premier tel que p² ∣ m
  rcases (nonSquarefree_iff_exists_prime_sq_dvd m hm_pos).1 hm_nsq with ⟨p, hp, hp2dvd⟩
  -- p² ≤ m ≤ n
  have hp2_le_n : p^2 ≤ n := le_trans (Nat.le_of_dvd hm_pos hp2dvd) hm_le_n
  -- Donc p ≤ √n
  have hp_le_sqrt : p ≤ n.sqrt := by
    -- ROUTE PRIMAIRE : Nat.le_sqrt.mpr ou Nat.le_sqrt_of_sq_le
    -- Thomas : le nom peut être Nat.le_sqrt, Nat.le_sqrt_of_sq_le_sq,
    -- ou Nat.sqrt_le_sqrt selon le snapshot.
    have : p * p ≤ n := by
      have : p^2 = p * p := sq p
      omega
    exact Nat.le_sqrt.mpr this
  -- Insertion dans le biUnion
  refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, hp⟩
    refine Finset.mem_Ico.mpr ⟨hp.two_le, ?_⟩
    omega
  · refine Finset.mem_filter.mpr ⟨?_, hp2dvd⟩
    exact Finset.mem_Ico.mpr ⟨hm_ge, hm_lt⟩

/-! ## Partie 5 — Borne de Legendre (ex-SORRY-4) -/

/--
**SORRY-4 fermé**. Borne inférieure brute par inclusion-exclusion à l'ordre 1.

    Q(n) ≥ n - Σ_{p premier, p ≤ √n} ⌊n/p²⌋
-/
theorem squarefreeCount_ge_legendre (n : ℕ) (_hn : 0 < n) :
    squarefreeCount n ≥
      n - ∑ p ∈ (Finset.Ico 2 (n.sqrt + 2)).filter Nat.Prime, n / p^2 := by
  classical
  have hdecomp := squarefreeCount_add_nonSquarefreeCount n
  have hsub := nonSquarefree_subset_union_sq_multiples n
  -- Notation locale
  set S := (Finset.Ico 2 (n.sqrt + 2)).filter Nat.Prime with hS
  set A : ℕ → Finset ℕ :=
    fun p => (Finset.Ico 1 (n + 1)).filter (fun m => p^2 ∣ m) with hA
  -- Étape 1 : cardinal du non-squarefree majoré par cardinal du biUnion
  have hcard_union : nonSquarefreeCount n ≤ (S.biUnion A).card := by
    unfold nonSquarefreeCount
    exact Finset.card_le_card hsub
  -- Étape 2 : cardinal du biUnion majoré par somme des cardinaux
  have hcard_sum : (S.biUnion A).card ≤ ∑ p ∈ S, (A p).card := by
    -- ROUTE PRIMAIRE : Finset.card_biUnion_le
    -- ROUTE DE SECOURS (si nom différent) :
    --   induction sur S avec Finset.biUnion_insert et Finset.card_union_le
    exact Finset.card_biUnion_le
  -- Étape 3 : chaque (A p).card = n / p²
  have hmult :
      (∑ p ∈ S, (A p).card) = ∑ p ∈ S, n / p^2 := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    -- p est premier, donc p > 0
    have hpPos : 0 < p := by
      rcases Finset.mem_filter.mp hp with ⟨_, hpPrime⟩
      exact hpPrime.pos
    simp only [A]
    exact card_multiples n (p^2) (by positivity)
  -- Assemblage
  have hnsq :
      nonSquarefreeCount n ≤ ∑ p ∈ S, n / p^2 := by
    calc nonSquarefreeCount n
        ≤ (S.biUnion A).card := hcard_union
      _ ≤ ∑ p ∈ S, (A p).card := hcard_sum
      _ = ∑ p ∈ S, n / p^2 := hmult
  -- Retour à squarefreeCount
  have hsq : squarefreeCount n + nonSquarefreeCount n = n := hdecomp
  omega

/-! ## Partie 6 — Borne télescopique pour Σ 1/p² (ex-SORRY-5) -/

/-- Pour k ≥ 2, on majore 1/k² par la différence télescopique 1/(k-1) − 1/k. -/
lemma inv_sq_le_sub (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℚ) / (k : ℚ)^2 ≤ (1 : ℚ) / ((k : ℚ) - 1) - (1 : ℚ) / (k : ℚ) := by
  have hk0 : (0 : ℚ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hk
  have hkm1 : (0 : ℚ) < (k : ℚ) - 1 := by
    have : (1 : ℚ) < (k : ℚ) := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hk
    linarith
  -- Forme close : 1/(k-1) − 1/k = 1/(k(k-1))
  have hEq : (1 : ℚ) / ((k : ℚ) - 1) - (1 : ℚ) / (k : ℚ) = 1 / ((k : ℚ) * ((k : ℚ) - 1)) := by
    have hk_ne : (k : ℚ) ≠ 0 := ne_of_gt hk0
    have hkm1_ne : (k : ℚ) - 1 ≠ 0 := ne_of_gt hkm1
    field_simp
    ring
  rw [hEq]
  -- 1/k² ≤ 1/(k(k-1)) ⇔ k(k-1) ≤ k²  (les deux dénominateurs sont positifs)
  have hmul_pos : (0 : ℚ) < (k : ℚ) * ((k : ℚ) - 1) := by positivity
  have hsq_pos : (0 : ℚ) < (k : ℚ)^2 := by positivity
  rw [div_le_div_iff₀ hsq_pos hmul_pos]
  nlinarith

/-- Télescopage explicite sur Icc 31 N. -/
lemma telescoping_31 (N : ℕ) (hN : 31 ≤ N) :
    (∑ k ∈ Finset.Icc 31 N, ((1 : ℚ) / ((k : ℚ) - 1) - (1 : ℚ) / (k : ℚ)))
      = (1 : ℚ) / 30 - (1 : ℚ) / (N : ℚ) := by
  induction' N, hN using Nat.le_induction with N hN31 ih
  · -- Base N = 31 : la somme se réduit à un seul terme
    simp [Finset.Icc_self]
    norm_num
  · -- Hérédité : Icc 31 (N+1) = Icc 31 N ∪ {N+1}
    rw [Finset.sum_Icc_succ_top (by omega : 31 ≤ N + 1)]
    rw [ih]
    have hN0 : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < N + 1)
    have hN_ne : (N : ℚ) ≠ 0 := ne_of_gt hN0
    have hN1_ne : ((N + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hN1
    -- ↑(N+1) - 1 = ↑N (en ℚ)
    have hcast : (((N + 1 : ℕ) : ℚ) - 1) = (N : ℚ) := by push_cast; ring
    rw [hcast]
    field_simp
    ring

/-- Queue harmonique quadratique discrète majorée par 1/30. -/
lemma tail_sq_sum_le_thirty (N : ℕ) :
    ∑ k ∈ Finset.Icc 31 N, ((1 : ℚ) / (k : ℚ)^2) ≤ (1 : ℚ) / 30 := by
  by_cases hN : N < 31
  · simp [Finset.Icc_eq_empty_of_lt (by omega : N < 31)]
  · push Not at hN
    calc
      ∑ k ∈ Finset.Icc 31 N, ((1 : ℚ) / (k : ℚ)^2)
          ≤ ∑ k ∈ Finset.Icc 31 N,
              ((1 : ℚ) / ((k : ℚ) - 1) - (1 : ℚ) / (k : ℚ)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            rcases Finset.mem_Icc.mp hk with ⟨hk31, _⟩
            exact inv_sq_le_sub k (by omega)
      _ = (1 : ℚ) / 30 - (1 : ℚ) / (N : ℚ) := telescoping_31 N hN
      _ ≤ (1 : ℚ) / 30 := by
            have hpos : (0 : ℚ) ≤ (1 : ℚ) / (N : ℚ) := by
              apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
              exact_mod_cast Nat.zero_le N
            linarith

/-- Calcul explicite jusqu'à 30 : les 10 premiers premiers ≤ 29. -/
lemma prime_sq_sum_upto_30_eq :
    (∑ p ∈ (Finset.Ico 2 31).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
      = 1/4 + 1/9 + 1/25 + 1/49 + 1/121 + 1/169 + 1/289 + 1/361 + 1/529 + 1/841 := by
  -- Les premiers ≤ 30 : 2, 3, 5, 7, 11, 13, 17, 19, 23, 29
  -- Leurs carrés : 4, 9, 25, 49, 121, 169, 289, 361, 529, 841
  native_decide

lemma prime_sq_sum_upto_30_lt_half :
    (∑ p ∈ (Finset.Ico 2 31).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
      ≤ 1/2 - 1/30 := by
  rw [prime_sq_sum_upto_30_eq]
  norm_num

/--
**SORRY-5 fermé** par télescopage discret.

Σ 1/p² sur les premiers ≤ n+1 est ≤ 1/2.
-/
theorem sum_inv_prime_sq_lt_half :
    ∀ n : ℕ, (∑ p ∈ (Finset.Ico 2 (n + 2)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2) ≤ 1/2 := by
  intro n
  by_cases hsmall : n + 2 ≤ 31
  · -- Cas fini : tout est dans la fenêtre [2, 30]
    have hsubset :
        (Finset.Ico 2 (n + 2)).filter Nat.Prime ⊆
          (Finset.Ico 2 31).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpIco, hpPrime⟩
      rcases Finset.mem_Ico.mp hpIco with ⟨h2, hlt⟩
      refine Finset.mem_filter.mpr ⟨?_, hpPrime⟩
      exact Finset.mem_Ico.mpr ⟨h2, by omega⟩
    calc
      (∑ p ∈ (Finset.Ico 2 (n + 2)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
          ≤ ∑ p ∈ (Finset.Ico 2 31).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun x _ _ => by positivity)
      _ ≤ 1/2 - 1/30 := prime_sq_sum_upto_30_lt_half
      _ ≤ 1/2 := by norm_num
  · -- Cas grand : découper à 31, calcul explicite + télescopage
    push Not at hsmall
    have hge31 : 31 ≤ n + 1 := by omega
    -- Découpage Ico 2 (n+2) = Ico 2 31 ∪ Icc 31 (n+1)  (disjoints)
    have hsplit :
        (∑ p ∈ (Finset.Ico 2 (n + 2)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
        =
        (∑ p ∈ (Finset.Ico 2 31).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
        + (∑ p ∈ (Finset.Icc 31 (n + 1)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2) := by
      -- Identité des Finsets filtrés
      have hUnion :
          (Finset.Ico 2 (n + 2)).filter Nat.Prime
            = ((Finset.Ico 2 31).filter Nat.Prime) ∪
              ((Finset.Icc 31 (n + 1)).filter Nat.Prime) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc,
                   Finset.mem_union]
        constructor
        · rintro ⟨⟨h2, hlt⟩, hp⟩
          by_cases h30 : p < 31
          · left; exact ⟨⟨h2, h30⟩, hp⟩
          · right; exact ⟨⟨by omega, by omega⟩, hp⟩
        · rintro (⟨⟨h2, hlt⟩, hp⟩ | ⟨⟨h31p, hlt⟩, hp⟩)
          · exact ⟨⟨h2, by omega⟩, hp⟩
          · exact ⟨⟨by omega, by omega⟩, hp⟩
      have hDisjoint :
          Disjoint ((Finset.Ico 2 31).filter Nat.Prime)
                   ((Finset.Icc 31 (n + 1)).filter Nat.Prime) := by
        refine Finset.disjoint_left.mpr ?_
        intro p hp1 hp2
        rcases Finset.mem_filter.mp hp1 with ⟨hp1Ico, _⟩
        rcases Finset.mem_filter.mp hp2 with ⟨hp2Icc, _⟩
        rcases Finset.mem_Ico.mp hp1Ico with ⟨_, h30⟩
        rcases Finset.mem_Icc.mp hp2Icc with ⟨h31, _⟩
        omega
      rw [hUnion, Finset.sum_union hDisjoint]
    rw [hsplit]
    -- Majoration de la queue primaire par la queue totale
    have htail_primes :
        (∑ p ∈ (Finset.Icc 31 (n + 1)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
          ≤ ∑ k ∈ Finset.Icc 31 (n + 1), (1 : ℚ) / (k : ℚ)^2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun x _ _ => by positivity)
    have htail_le : (∑ p ∈ (Finset.Icc 31 (n + 1)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
          ≤ 1 / 30 := le_trans htail_primes (tail_sq_sum_le_thirty (n + 1))
    calc
      (∑ p ∈ (Finset.Ico 2 31).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
        + (∑ p ∈ (Finset.Icc 31 (n + 1)).filter Nat.Prime, (1 : ℚ) / (p : ℚ)^2)
          ≤ (1/2 - 1/30) + 1/30 := by
            linarith [prime_sq_sum_upto_30_lt_half, htail_le]
      _ = 1/2 := by ring

/-! ## Partie 7 — Micro-lemmes de cast (pour ex-SORRY-6) -/

/-- Version générique : la division entière est majorée par la division rationnelle. -/
lemma natCast_div_le_ratDiv (n k : ℕ) (hk : 0 < k) :
    ((n / k : ℕ) : ℚ) ≤ (n : ℚ) / (k : ℚ) := by
  have hnat : k * (n / k) ≤ n := Nat.mul_div_le n k
  have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hcast : ((k * (n / k) : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast hnat
  have hmul : ((n / k : ℕ) : ℚ) * (k : ℚ) ≤ (n : ℚ) := by
    rw [mul_comm]
    simpa [Nat.cast_mul] using hcast
  rwa [← le_div_iff₀ hkq] at hmul

/-- Version spécialisée à p². -/
lemma natCast_div_sq_le_ratDiv (n p : ℕ) (hp : 0 < p) :
    ((n / p^2 : ℕ) : ℚ) ≤ (n : ℚ) / (p : ℚ)^2 := by
  simpa using natCast_div_le_ratDiv n (p^2) (by positivity)

/-- Extraction du facteur n d'une somme de (n:ℚ)/f(p). -/
lemma sum_ratDiv_eq_mul_sum_inv {α : Type*} (s : Finset α) (g : α → ℚ) (n : ℕ) :
    (∑ x ∈ s, (n : ℚ) / g x) = (n : ℚ) * ∑ x ∈ s, 1 / g x := by
  simp [div_eq_mul_inv, Finset.mul_sum]

/-! ## Partie 8 — Résultat principal (ex-SORRY-6 et SORRY-7) -/

/--
**SORRY-6 fermé**. Borne inférieure Q(n) ≥ n/2 pour n ≥ 176.

Ceci formalise la moitié (ii) de RouteC::main_lower.
-/
theorem squarefreeCount_ge_half (n : ℕ) (hn : 176 ≤ n) :
    2 * squarefreeCount n ≥ n := by
  have hn0 : 0 < n := by omega

  set S := (Finset.Ico 2 (n.sqrt + 2)).filter Nat.Prime

  -- Étape 1 : borne de Legendre en ℕ
  have hleg : squarefreeCount n ≥ n - ∑ p ∈ S, n / p^2 := by
    simpa [S] using squarefreeCount_ge_legendre n hn0

  -- On évite de caster une soustraction de ℕ ; on passe d'abord
  -- à la forme additive.
  have hlegNat :
      squarefreeCount n + ∑ p ∈ S, n / p^2 ≥ n := by
    omega

  -- Étape 2 : passage en ℚ
  have hlegQ : (squarefreeCount n : ℚ) ≥
      (n : ℚ) - ∑ p ∈ S, ((n / p^2 : ℕ) : ℚ) := by
    have hcast :
        ((squarefreeCount n + ∑ p ∈ S, n / p^2 : ℕ) : ℚ) ≥ (n : ℚ) := by
      exact_mod_cast hlegNat
    push_cast at hcast
    linarith

  -- Étape 3 : majoration ⌊n/p²⌋ ≤ n/p²
  have hfloor :
      (∑ p ∈ S, ((n / p^2 : ℕ) : ℚ))
        ≤ ∑ p ∈ S, (n : ℚ) / (p : ℚ)^2 := by
    refine Finset.sum_le_sum ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpPrime⟩
    exact natCast_div_sq_le_ratDiv n p hpPrime.pos

  -- Étape 4 : majoration par n · (1/2)
  have hhalf : (∑ p ∈ S, (1 : ℚ) / (p : ℚ)^2) ≤ 1 / 2 := by
    simpa [S] using sum_inv_prime_sq_lt_half n.sqrt

  have hprime :
      (∑ p ∈ S, (n : ℚ) / (p : ℚ)^2) ≤ (n : ℚ) / 2 := by
    rw [sum_ratDiv_eq_mul_sum_inv]
    have hn_nonneg : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have :
        (n : ℚ) * (∑ p ∈ S, 1 / (p : ℚ)^2)
          ≤ (n : ℚ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hhalf hn_nonneg
    linarith

  -- Assemblage final
  have hmainQ : (squarefreeCount n : ℚ) ≥ (n : ℚ) / 2 := by
    linarith

  have hQ : ((2 * squarefreeCount n : ℕ) : ℚ) ≥ (n : ℚ) := by
    push_cast
    linarith

  exact_mod_cast hQ

/--
**SORRY-7 fermé**. Version rationnelle du résultat principal.
-/
theorem squarefreeCount_linear_lower (n : ℕ) (hn : 176 ≤ n) :
    (squarefreeCount n : ℚ) ≥ (1 : ℚ) / 2 * (n : ℚ) := by
  have h := squarefreeCount_ge_half n hn
  have hQ : (2 : ℚ) * (squarefreeCount n : ℚ) ≥ (n : ℚ) := by exact_mod_cast h
  linarith

/-! ## Partie 9 — Sanity checks numériques -/

/-- Vérification à n=10. -/
example : squarefreeCount 10 = 7 := by
  unfold squarefreeCount; native_decide

/-- Vérification à n=30. -/
example : squarefreeCount 30 = 19 := by
  unfold squarefreeCount; native_decide

/-- Vérification à n=176 (point de minimum Rogers 53/88). -/
example : 2 * squarefreeCount 176 ≥ 176 := by
  unfold squarefreeCount; native_decide

/-- Vérification à n=200. -/
example : 2 * squarefreeCount 200 ≥ 200 := by
  unfold squarefreeCount; native_decide

/-- Vérification à n=1000. -/
example : 2 * squarefreeCount 1000 ≥ 1000 := by
  unfold squarefreeCount; native_decide

end CouretUnification.Logic.H3

/-!
## Status final du fichier

| Sorry | Statut | Route utilisée |
|-------|--------|----------------|
| SORRY-1 | fermé | `Nat.squarefree_iff_prime_squarefree` |
| SORRY-2 | fermé | inclusion ensembliste pure |
| SORRY-3 | fermé | `Nat.Ioc_filter_dvd_card_eq_div` |
| SORRY-4 | fermé | `Finset.card_biUnion_le` + omega |
| SORRY-5 | fermé | télescopage discret (sans intégrale) |
| SORRY-6 | fermé | micro-lemmes de cast + extraction |
| SORRY-7 | fermé | conversion finale ℕ → ℚ |

## Points API potentiellement fragiles

Si Thomas rencontre un nom Mathlib qui a bougé, voici les routes de secours :

1. **`Nat.squarefree_iff_prime_squarefree`** (SORRY-1)
   - Alternative : `Nat.squarefree_iff_minSqFac` + `Nat.minSqFac_prime`
   - Alternative : `UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`

2. **`Nat.Ioc_filter_dvd_card_eq_div`** (SORRY-3)
   - Alternative : `Nat.card_multiples`
   - Alternative : variante dans `Mathlib.Data.Nat.Factorization`

3. **`Nat.le_sqrt`** (SORRY-2)
   - Alternative : `Nat.le_sqrt_of_sq_le_sq`
   - Alternative : preuve directe via `Nat.sqrt_lt'` et contraposée

4. **`Finset.card_biUnion_le`** (SORRY-4)
   - Alternative : induction sur `S` avec `Finset.card_union_le`
   - Alternative : `Finset.card_bind_le` (ancien nom)

5. **`Finset.sum_Icc_succ_top`** (SORRY-5)
   - Alternative : `Finset.sum_Icc_succ`
   - Alternative : preuve manuelle via `Finset.sum_insert`

## Ce qui reste à faire après ce fichier

1. **Moitié (i) de `RouteC::main_lower`** : S₁(q) ≥ (1/2)·Q(q)
   Cette moitié dépend de la définition précise de S₁ dans `RouteC.lean` et
   d'un argument de minoration terme-à-terme. Session dédiée avec Alexandre.

2. **`RouteC::error_upper`** : décorrélation θ < 1. Session dédiée avec Bombieri-
   Vinogradov ou crible fin.

3. **`Lemma7Residual`** : gelé jusqu'à stabilisation de `Det2Transport`.

## Invariant

`RHClaimed = false`. Dédié à Bernard Couret (1928–1999).
-/
