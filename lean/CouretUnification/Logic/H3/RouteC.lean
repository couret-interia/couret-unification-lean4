import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import CouretUnification.Core.Arithmetic

/-!
# Route C raffinée — Infrastructure formelle v32.43

## Programme Couret-Unification

Ce fichier formalise la **Route C raffinée** : la réduction conditionnelle
du verrou `κ(q) ≥ λ` à des hypothèses analytiques minimales et nommées.

### Architecture

Le triptyque final est :
- `(A)` `routeC_explicit_core`
- `(B)` `kappa_explicit_bound`
- `(C)` `kappa_eventually_pos`

Les verrous analytiques sont décomposés au niveau minimal :
- `badSquareCount_le_sum_div_sq`     — couverture combinatoire
- `sum_div_sq_le_three_quarters`     — majoration télescopique (C = 3/4)
- `S1_lower_from_squarefree`         — marche discrète de Möbius
- `routeC_error_control`             — contrôle θ < 1 (Route C)

Tous les recollements algébriques entre ces verrous sont fermés.

### Sorry dans ce fichier : 1

- `routeC_error_control`

`RHClaimed = false.`
Dédié à Bernard Couret (1928–1999).
-/

open Filter
open scoped Topology

namespace CouretUnification.Logic.H3.RouteC

-- ═══════════════════════════════════════════════════════════
-- §1. Recollement avec l'arithmétique réelle
-- ═══════════════════════════════════════════════════════════

/-- Indicatrice d’Euler, importée depuis `Arithmetic.lean`. -/
noncomputable abbrev phi : ℕ → ℝ := CouretUnification.Arithmetic.phi

/-- Second moment restreint `K(q)`, importé depuis `Arithmetic.lean`. -/
noncomputable abbrev K : ℕ → ℝ := CouretUnification.Arithmetic.K

/-- Second moment normalisé `κ(q)² = K(q)/φ(q)`. -/
noncomputable abbrev kappaSq : ℕ → ℝ := CouretUnification.Arithmetic.kappaSq

/-- `κ(q) = √(K(q)/φ(q))`. -/
noncomputable abbrev kappa : ℕ → ℝ := CouretUnification.Arithmetic.kappa

/-- Tour primorielle. Placeholder — TODO : canoniser via les nombres premiers ordonnés. -/
def primorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => primorial n * (Nat.minFac (primorial n + 1))

/-- Positivité de la tour primorielle. -/
theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  induction n with
  | zero => simp [primorial]
  | succ n ih =>
    unfold primorial
    exact Nat.mul_pos ih (Nat.minFac_pos _)

/-- Positivité de `φ(primorial n)`. -/
theorem phi_primorial_pos (n : ℕ) : 0 < phi (primorial n) := by
  unfold phi CouretUnification.Arithmetic.phi
  exact Nat.cast_pos.mpr ((Nat.totient_pos).mpr (primorial_pos n))

/-- Non-négativité de `φ(primorial n)`, déduite de sa positivité. -/
theorem phi_primorial_nonneg (n : ℕ) : 0 ≤ phi (primorial n) :=
  le_of_lt (phi_primorial_pos n)

-- ═══════════════════════════════════════════════════════════
-- §2. Décomposition analytique
-- ═══════════════════════════════════════════════════════════

/-- `S1(q) = Σ_{1 ≤ n ≤ q} M(n)²` — second moment non restreint de Mertens. -/
noncomputable def S1 (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (q + 1))
    (fun n => if 0 < n then ((Arithmetic.mertens n : ℤ) : ℝ) ^ 2 else 0)

/-- `S1(q) ≥ 0` — somme de carrés. -/
theorem S1_nonneg (q : ℕ) : 0 ≤ S1 q := by
  unfold S1
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

/-- `MainTerm(q) = (φ(q)/q) · S1(q)`. -/
noncomputable def MainTerm (q : ℕ) : ℝ :=
  (phi q / (q : ℝ)) * S1 q

/-- `ErrorTerm(q) = K(q) - MainTerm(q)`. -/
noncomputable def ErrorTerm (q : ℕ) : ℝ :=
  K q - MainTerm q

/-- Décomposition tautologique : `K = MainTerm + ErrorTerm`. -/
theorem K_decomposition (q : ℕ) : K q = MainTerm q + ErrorTerm q := by
  unfold ErrorTerm; ring

-- ═══════════════════════════════════════════════════════════
-- §3. Squarefree count (via la vraie définition Mathlib)
-- ═══════════════════════════════════════════════════════════

/-- Nombre d’entiers squarefree dans `{1, …, q}`.
    Utilise le prédicat `Squarefree` de Mathlib. -/
noncomputable def squarefreeCount (q : ℕ) : ℝ :=
  (((Finset.Icc 1 q).filter (fun n => Squarefree n)).card : ℕ)

/-- Le nombre d’entiers squarefree est non négatif. -/
theorem squarefreeCount_nonneg (q : ℕ) : 0 ≤ squarefreeCount q := by
  unfold squarefreeCount
  positivity

-- ═══════════════════════════════════════════════════════════
-- §3bis. Route Mertens : badSquareCount et union bound
-- ═══════════════════════════════════════════════════════════

/-- Nombre d’entiers NON-squarefree dans `{1, …, q}`. -/
noncomputable def badSquareCount (q : ℕ) : ℝ :=
  (((Finset.Icc 1 q).filter fun n => ¬ Squarefree n).card : ℕ)

/-- Le nombre d’entiers non-squarefree est non négatif. -/
theorem badSquareCount_nonneg (q : ℕ) : 0 ≤ badSquareCount q := by
  unfold badSquareCount
  positivity

/-- Tout entier de `{1, …, q}` est soit squarefree, soit non-squarefree. -/
theorem squarefreeCount_add_badSquareCount (q : ℕ) :
    squarefreeCount q + badSquareCount q = (q : ℝ) := by
  unfold squarefreeCount badSquareCount
  have hcard :
      ((Finset.Icc 1 q).filter fun n => Squarefree n).card +
      ((Finset.Icc 1 q).filter fun n => ¬ Squarefree n).card =
      (Finset.Icc 1 q).card := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.Icc 1 q) (p := fun n => Squarefree n))
  have hicc : (Finset.Icc 1 q).card = q := by
    rw [Nat.card_Icc]
    omega
  exact_mod_cast hcard.trans hicc

-- ═══════════════════════════════════════════════════════════
-- Front 3 : contrôle combinatoire des entiers non squarefree
-- ═══════════════════════════════════════════════════════════

/-- Si `k` n'est pas squarefree, alors il existe un entier `m ≥ 2`
tel que `m² ∣ k`. -/
private lemma exists_sq_dvd_of_not_squarefree {k : ℕ} (hk : ¬ Squarefree k) :
    ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ k := by
  rw [Nat.squarefree_iff_prime_squarefree] at hk
  push Not at hk
  obtain ⟨p, hp_prime, hp_dvd⟩ := hk
  refine ⟨p, hp_prime.two_le, ?_⟩
  simpa [pow_two] using hp_dvd

/-- Si `m² ∣ k` avec `0 < k ≤ q`, alors `m ≤ q`. -/
private lemma sq_dvd_le {k q m : ℕ} (hk : k ≤ q) (hk_pos : 0 < k)
    (hdvd : m ^ 2 ∣ k) : m ≤ q := by
  have hm2_le : m ^ 2 ≤ k := Nat.le_of_dvd hk_pos hdvd
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst hm
    have : k = 0 := by
      simpa using hdvd
    omega
  have hm_le_sq : m ≤ m ^ 2 := by
    have h1 : 1 ≤ m := Nat.succ_le_of_lt hm_pos
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left m h1
  exact le_trans hm_le_sq (le_trans hm2_le hk)

/-- Ensemble des multiples de `d` dans l’intervalle `{1, ..., q}`. -/
def multiplesOf (d q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun k => d ∣ k)

/-- Le nombre de multiples de `d` dans `{1, ..., q}` est majoré par `⌊q/d⌋`. -/
private lemma card_multiplesOf_le (d q : ℕ) (hd : 0 < d) :
    (multiplesOf d q).card ≤ q / d := by
  let s := multiplesOf d q
  let t : Finset ℕ := Finset.Icc 1 (q / d)

  have hmap : Set.MapsTo (fun k : ℕ => k / d) ↑s ↑t := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    rcases Finset.mem_Icc.mp hk'.1 with ⟨hk1, hkq⟩
    have hkdiv : d ∣ k := hk'.2
    refine Finset.mem_Icc.mpr ?_
    constructor
    · rcases hkdiv with ⟨r, rfl⟩
      have hr_pos : 0 < r := by
        by_contra hr0
        have hr : r = 0 := Nat.eq_zero_of_not_pos hr0
        subst hr
        simp at hk1
      have hdiv_eq : (d * r) / d = r := by
        simpa [Nat.mul_comm] using (Nat.mul_div_right r hd)
      change 1 ≤ (d * r) / d
      rw [hdiv_eq]
      exact Nat.succ_le_of_lt hr_pos
    · rcases hkdiv with ⟨r, rfl⟩
      have hmul : r * d ≤ q := by
        simpa [Nat.mul_comm] using hkq
      have hle : r ≤ q / d := by
        exact (Nat.le_div_iff_mul_le hd).2 hmul
      have hdiv_eq : (d * r) / d = r := by
        simpa [Nat.mul_comm] using (Nat.mul_div_right r hd)
      change (d * r) / d ≤ q / d
      rw [hdiv_eq]
      exact hle

  have hinj : Set.InjOn (fun k : ℕ => k / d) ↑s := by
    intro k₁ hk₁ k₂ hk₂ hquot
    have hk₁div : d ∣ k₁ := (Finset.mem_filter.mp hk₁).2
    have hk₂div : d ∣ k₂ := (Finset.mem_filter.mp hk₂).2
    have hquot' : k₁ / d = k₂ / d := by
      simpa using hquot
    calc
      k₁ = d * (k₁ / d) := by
        symm
        exact Nat.mul_div_cancel' hk₁div
      _ = d * (k₂ / d) := by
        exact congrArg (fun x => d * x) hquot'
      _ = k₂ := Nat.mul_div_cancel' hk₂div

  have hcard : s.card ≤ t.card :=
    Finset.card_le_card_of_injOn (fun k : ℕ => k / d) hmap hinj

  have htcard : t.card = q / d := by
    unfold t
    rw [Nat.card_Icc]
    simp

  simpa [s, htcard] using hcard

/-- Sous-additivité du cardinal d’une union finie :
`card(⋃ i ∈ s, t i) ≤ ∑ i ∈ s, card(t i)`. -/
private lemma card_biUnion_le_sum {α : Type*} [DecidableEq α]
    (s : Finset ℕ) (t : ℕ → Finset α) :
    (s.biUnion t).card ≤ Finset.sum s (fun i => (t i).card) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ih _)

/-- Borne combinatoire fondamentale :
le nombre d’entiers non squarefree dans `{1, ..., q}` est majoré par
`∑_{m=2}^{q} ⌊q / m²⌋`. -/
theorem badSquareCount_le_sum_div_sq (q : ℕ) :
    badSquareCount q ≤
      Finset.sum (Finset.Icc 2 q) (fun m => ((q / (m ^ 2 : ℕ) : ℕ) : ℝ)) := by
  unfold badSquareCount

  have hsubset :
      ((Finset.Icc 1 q).filter fun k => ¬ Squarefree k)
        ⊆
      (Finset.Icc 2 q).biUnion (fun m => multiplesOf (m ^ 2) q) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    rcases Finset.mem_Icc.mp hk'.1 with ⟨hk1, hkq⟩
    obtain ⟨m, hm2, hmdiv⟩ := exists_sq_dvd_of_not_squarefree hk'.2
    have hmq : m ≤ q := sq_dvd_le hkq hk1 hmdiv
    apply Finset.mem_biUnion.mpr
    refine ⟨m, Finset.mem_Icc.mpr ⟨hm2, hmq⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkq⟩, hmdiv⟩

  have hcard_nat :
      ((Finset.Icc 1 q).filter fun k => ¬ Squarefree k).card
        ≤
      Finset.sum (Finset.Icc 2 q) (fun m => (multiplesOf (m ^ 2) q).card) := by
    have h1 :
        ((Finset.Icc 1 q).filter fun k => ¬ Squarefree k).card
          ≤
        ((Finset.Icc 2 q).biUnion (fun m => multiplesOf (m ^ 2) q)).card :=
      Finset.card_le_card hsubset
    have h2 :
        ((Finset.Icc 2 q).biUnion (fun m => multiplesOf (m ^ 2) q)).card
          ≤
        Finset.sum (Finset.Icc 2 q) (fun m => (multiplesOf (m ^ 2) q).card) :=
      card_biUnion_le_sum (Finset.Icc 2 q) (fun m => multiplesOf (m ^ 2) q)
    exact le_trans h1 h2

  have hcard_nat' :
      ((Finset.Icc 1 q).filter fun k => ¬ Squarefree k).card
        ≤
      Finset.sum (Finset.Icc 2 q) (fun m => q / (m ^ 2)) := by
    refine le_trans hcard_nat ?_
    apply Finset.sum_le_sum
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hpos : 0 < m ^ 2 := by
      have hm_pos : 0 < m := by
        omega
      positivity
    exact card_multiplesOf_le (m ^ 2) q hpos

  exact_mod_cast hcard_nat'

/-- Le cast réel de la division euclidienne est majoré par la division réelle. -/
private lemma nat_div_cast_le (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (show (0 : ℝ) < (b : ℝ) by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

/-- Pour `m ≥ 2`, on a `1 / m² ≤ 1 / (m(m-1))`. -/
private lemma inv_sq_le_inv_mul_pred (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := by
    linarith
  have hm1_pos : 0 < (m : ℝ) - 1 := by
    linarith
  have hpos : 0 < (m : ℝ) * ((m : ℝ) - 1) := by
    positivity
  have hle : (m : ℝ) * ((m : ℝ) - 1) ≤ (m : ℝ) ^ 2 := by
    nlinarith
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    (one_div_le_one_div_of_le hpos hle)

/-- Identité télescopique élémentaire :
`1 / ((q+1)q) = 1/q - 1/(q+1)` pour `q ≥ 1`. -/
private lemma telescoping_term (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / (((q + 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) - 1))
      = 1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    positivity
  have hq1 : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hsub : (((q + 1 : ℕ) : ℝ) - 1) = (q : ℝ) := by
    norm_num
  rw [hsub]
  field_simp [hq0, hq1]
  norm_num

/-- Somme télescopique fermée :
`∑_{m=3}^{q} 1 / (m(m-1)) = 1/2 - 1/q` pour `q ≥ 3`. -/
private lemma sum_telescopic_eq (q : ℕ) (hq : 3 ≤ q) :
    Finset.sum (Finset.Icc 3 q)
      (fun m => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)))
      = 1 / 2 - 1 / (q : ℝ) := by
  induction' q, hq using Nat.le_induction with q hq ih
  · norm_num
  · rw [Finset.sum_Icc_succ_top (show 3 ≤ q + 1 by omega)]
    rw [ih, telescoping_term q (by omega)]
    ring

/-- Borne uniforme :
`∑_{m=3}^{q} 1 / (m(m-1)) ≤ 1/2`. -/
private lemma sum_telescopic_le_half (q : ℕ) :
    Finset.sum (Finset.Icc 3 q)
      (fun m => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) ≤ 1 / 2 := by
  by_cases hq : q < 3
  · have hempty : Finset.Icc 3 q = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    simp [hempty]
  · have hq' : 3 ≤ q := by
      omega
    rw [sum_telescopic_eq q hq']
    have : 0 ≤ (1 : ℝ) / (q : ℝ) := by
      positivity
    linarith

/-- Le terme initial `m = 2` vaut exactement `1/4`. -/
private lemma inv_sq_two : (1 : ℝ) / ((2 : ℝ) ^ 2) = 1 / 4 := by
  norm_num

/-- Borne élémentaire sur la somme des inverses des carrés :
`∑_{m=2}^{q} 1 / m² ≤ 3/4`. -/
private lemma sum_inv_sq_Icc_le (q : ℕ) :
    Finset.sum (Finset.Icc 2 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2)) ≤ 3 / 4 := by
  by_cases hq2 : q < 2
  · have hempty : Finset.Icc 2 q = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    simp [hempty]
    norm_num
  · have hq2' : 2 ≤ q := by
      omega
    by_cases hq3 : q < 3
    · have hq : q = 2 := by
        omega
      subst hq
      simp [Finset.Icc_self]
      norm_num
    · have hq3' : 3 ≤ q := by
        omega
      have hsplit : Finset.Icc 2 q = insert 2 (Finset.Icc 3 q) := by
        ext m
        simp [Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_insert]
      · have hsumle :
            Finset.sum (Finset.Icc 3 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2))
              ≤
            Finset.sum (Finset.Icc 3 q) (fun m => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) := by
          apply Finset.sum_le_sum
          intro m hm
          exact inv_sq_le_inv_mul_pred m (le_trans (by norm_num) (Finset.mem_Icc.mp hm).1)
        calc
          (1 : ℝ) / ((2 : ℝ) ^ 2) +
              Finset.sum (Finset.Icc 3 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2))
              = (1 / 4 : ℝ) +
                  Finset.sum (Finset.Icc 3 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2)) := by
                    rw [inv_sq_two]
          _ ≤ (1 / 4 : ℝ) +
                Finset.sum (Finset.Icc 3 q)
                  (fun m => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) := by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_left hsumle (1 / 4 : ℝ)
          _ ≤ (1 / 4 : ℝ) + 1 / 2 := by
                    gcongr
                    exact sum_telescopic_le_half q
          _ = 3 / 4 := by
                    norm_num
      · simp

/-- `sum_div_sq_le_three_quarters` — FERMÉ via `nat_div_cast_le`
et `sum_inv_sq_Icc_le`. -/
theorem sum_div_sq_le_three_quarters (q : ℕ) :
    Finset.sum (Finset.Icc 2 q) (fun m => ((q / (m ^ 2 : ℕ) : ℕ) : ℝ))
      ≤ (3 / 4 : ℝ) * (q : ℝ) := by
  -- Étape 1 : borne ponctuelle ⌊q/m²⌋ ≤ q/m² via nat_div_cast_le
  have h1 : Finset.sum (Finset.Icc 2 q) (fun m => ((q / (m ^ 2 : ℕ) : ℕ) : ℝ))
      ≤ Finset.sum (Finset.Icc 2 q) (fun m => (q : ℝ) / ((m : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro m hm
    have hm_ge : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm2_pos : 0 < m ^ 2 := by positivity
    have h := nat_div_cast_le q (m ^ 2) hm2_pos
    rwa [Nat.cast_pow] at h
  -- Étape 2 : factorisation de q hors de la somme
  have h2 :
      Finset.sum (Finset.Icc 2 q) (fun m => (q : ℝ) / ((m : ℝ) ^ 2))
        =
      (q : ℝ) * Finset.sum (Finset.Icc 2 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2)) := by
    calc
      Finset.sum (Finset.Icc 2 q) (fun m => (q : ℝ) / ((m : ℝ) ^ 2))
          =
        Finset.sum (Finset.Icc 2 q) (fun m => (q : ℝ) * ((1 : ℝ) / ((m : ℝ) ^ 2))) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [div_eq_mul_one_div]
      _ =
        (q : ℝ) * Finset.sum (Finset.Icc 2 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
  -- Étape 3 : combinaison
  calc Finset.sum (Finset.Icc 2 q) (fun m => ((q / (m ^ 2 : ℕ) : ℕ) : ℝ))
      ≤ Finset.sum (Finset.Icc 2 q) (fun m => (q : ℝ) / ((m : ℝ) ^ 2)) := h1
    _ = (q : ℝ) * Finset.sum (Finset.Icc 2 q) (fun m => (1 : ℝ) / ((m : ℝ) ^ 2)) := h2
    _ ≤ (q : ℝ) * (3 / 4) := by
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le q) (by positivity : 0 ≤ (q : ℝ))
    _ = (3 / 4) * (q : ℝ) := by ring

/-- `badSquareCount_union_bound` — fermé via les deux sous-verrous ci-dessus,
avec constante explicite `C = 3/4`. -/
theorem badSquareCount_union_bound :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ q : ℕ, badSquareCount q ≤ C * (q : ℝ) := by
  refine ⟨3 / 4, by norm_num, by norm_num, ?_⟩
  intro q
  exact le_trans
    (badSquareCount_le_sum_div_sq q)
    (sum_div_sq_le_three_quarters q)

/-- Recombinaison algébrique fermée : une borne sous-linéaire de `badSquareCount`
implique une borne linéaire inférieure sur `squarefreeCount`. -/
theorem squarefreeCount_linear_global_from_union_bound
    (h : ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ q : ℕ, badSquareCount q ≤ C * (q : ℝ)) :
    ∃ α : ℝ, 0 < α ∧
      ∀ q : ℕ, α * (q : ℝ) ≤ squarefreeCount q := by
  obtain ⟨C, hC_nn, hC_lt, hbound⟩ := h
  refine ⟨1 - C, by linarith, ?_⟩
  intro q
  have hsum := squarefreeCount_add_badSquareCount q
  have hb := hbound q
  linarith

/-- `squarefreeCount_linear_global` fermé via la borne d’union. -/
theorem squarefreeCount_linear_global :
    ∃ α : ℝ, 0 < α ∧
      ∀ q : ℕ, α * (q : ℝ) ≤ squarefreeCount q :=
  squarefreeCount_linear_global_from_union_bound badSquareCount_union_bound

-- ═══════════════════════════════════════════════════════════
-- §4. Décomposition structurelle de l'erreur
-- ═══════════════════════════════════════════════════════════

/-- Décomposition placeholder en une seule pièce de l’erreur. -/
def ErrorPieces (_q : ℕ) : Finset ℕ := {0}

/-- Pièce d’erreur associée à `q` et à l’indice `_d`. -/
noncomputable def E (q _d : ℕ) : ℝ := ErrorTerm q

/-- Décomposition tautologique de `ErrorTerm` comme somme des pièces d’erreur. -/
theorem errorTerm_decomposition (q : ℕ) :
    ErrorTerm q = Finset.sum (ErrorPieces q) (fun d => E q d) := by
  simp [ErrorPieces, E]

-- ═══════════════════════════════════════════════════════════
-- §5. Verrous analytiques minimaux
-- ═══════════════════════════════════════════════════════════

/-- Une étape non nulle de la marche est contrôlée par la somme des carrés
des deux positions adjacentes. -/
private lemma step_indicator_le_sqsum_pair
    (A : ℕ → ℤ) (n : ℕ) :
    (if A (n + 1) ≠ A n then (1 : ℝ) else 0)
      ≤
    ((A (n + 1) : ℤ) : ℝ) ^ 2 + ((A n : ℤ) : ℝ) ^ 2 := by
  by_cases h : A (n + 1) = A n
  · simp [h]; positivity
  · have hnonzero : A (n + 1) ≠ 0 ∨ A n ≠ 0 := by
      by_contra h0
      push Not at h0
      exact h (by simp [h0.1, h0.2])
    have hsq :
        (1 : ℝ) ≤ ((A (n + 1) : ℤ) : ℝ) ^ 2 + ((A n : ℤ) : ℝ) ^ 2 := by
      cases hnonzero with
          | inl h1 =>
            have hzsq : (1 : ℤ) ≤ (A (n + 1)) ^ 2 := by
              have := abs_pos.mpr h1
              nlinarith [sq_abs (A (n + 1))]
            have : (1 : ℝ) ≤ ((A (n + 1) : ℤ) : ℝ) ^ 2 := by exact_mod_cast hzsq
            linarith [sq_nonneg ((A n : ℤ) : ℝ)]
          | inr h0 =>
            have hzsq : (1 : ℤ) ≤ (A n) ^ 2 := by
              have := abs_pos.mpr h0
              nlinarith [sq_abs (A n)]
            have : (1 : ℝ) ≤ ((A n : ℤ) : ℝ) ^ 2 := by exact_mod_cast hzsq
            linarith [sq_nonneg ((A (n + 1) : ℤ) : ℝ)]
    simpa [h] using hsq

/-- Réécriture du cardinal d’un filtre comme somme d’indicatrices. -/
private lemma sum_indicators_eq_card_filter
    (A : ℕ → ℤ) (q : ℕ) :
    Finset.sum (Finset.range q)
        (fun n => if A (n + 1) ≠ A n then (1 : ℝ) else 0)
      =
    (((Finset.range q).filter (fun n => A (n + 1) ≠ A n)).card : ℝ) := by
  calc
    Finset.sum (Finset.range q)
        (fun n => if A (n + 1) ≠ A n then (1 : ℝ) else 0)
      =
    Finset.sum ((Finset.range q).filter (fun n => A (n + 1) ≠ A n))
        (fun _ => (1 : ℝ)) := by
          rw [Finset.sum_filter]
    _ = (((Finset.range q).filter (fun n => A (n + 1) ≠ A n)).card : ℝ) := by
          simp

/-- Somme décalée :
`Σ_{n<q} A(n+1)² = Σ_{n=1}^{q} A(n)²`. -/
private lemma sum_shift_sq_eq
    (A : ℕ → ℤ) (q : ℕ) :
    Finset.sum (Finset.range q)
        (fun n => (((A (n + 1) : ℤ) : ℝ) ^ 2))
      =
    Finset.sum (Finset.Icc 1 q)
        (fun n => (((A n : ℤ) : ℝ) ^ 2)) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top (show 1 ≤ q + 1 by omega)]

/-- Somme non décalée :
`Σ_{n<q} A(n)² ≤ Σ_{n=1}^{q} A(n)²` si `A(0)=0`. -/
private lemma sum_unshift_sq_le
    (A : ℕ → ℤ) (hA0 : A 0 = 0) (q : ℕ) :
    Finset.sum (Finset.range q)
        (fun n => (((A n : ℤ) : ℝ) ^ 2))
      ≤
    Finset.sum (Finset.Icc 1 q)
        (fun n => (((A n : ℤ) : ℝ) ^ 2)) := by
  cases q with
  | zero =>
      simp
  | succ q =>
      have hsplit : Finset.range (q + 1) = insert 0 (Finset.Icc 1 q) := by
        ext n
        simp [Finset.mem_range, Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_insert]
      · have hA0sq : (((A 0 : ℤ) : ℝ) ^ 2) = 0 := by
          simp [hA0]
        rw [hA0sq]
        rw [Finset.sum_Icc_succ_top (show 1 ≤ q + 1 by omega)]
        have hnonneg : 0 ≤ (((A (q + 1) : ℤ) : ℝ) ^ 2) := by
          positivity
        linarith
      · simp

/-- Front combinatoire :
le nombre de pas non nuls d’une marche est majoré par
`2 ×` la somme des carrés des positions. -/
private lemma walk_stepCount_le_two_sqsum
    (A : ℕ → ℤ) (hA0 : A 0 = 0) (q : ℕ) :
    (((Finset.range q).filter (fun n => A (n + 1) ≠ A n)).card : ℝ)
      ≤
    2 * Finset.sum (Finset.Icc 1 q)
        (fun n => (((A n : ℤ) : ℝ) ^ 2)) := by
  let g : ℕ → ℝ := fun n => (((A n : ℤ) : ℝ) ^ 2)

  have hpointwise :
      Finset.sum (Finset.range q)
          (fun n => if A (n + 1) ≠ A n then (1 : ℝ) else 0)
        ≤
      Finset.sum (Finset.range q) (fun n => g (n + 1) + g n) := by
    apply Finset.sum_le_sum
    intro n hn
    simpa [g] using step_indicator_le_sqsum_pair A n

  have hshift :
      Finset.sum (Finset.range q) (fun n => g (n + 1))
        =
      Finset.sum (Finset.Icc 1 q) g := by
    simpa [g] using sum_shift_sq_eq A q

  have hcurr :
      Finset.sum (Finset.range q) g
        ≤
      Finset.sum (Finset.Icc 1 q) g := by
    simpa [g] using sum_unshift_sq_le A hA0 q

  calc
    (((Finset.range q).filter (fun n => A (n + 1) ≠ A n)).card : ℝ)
        =
      Finset.sum (Finset.range q)
        (fun n => if A (n + 1) ≠ A n then (1 : ℝ) else 0) := by
          symm
          exact sum_indicators_eq_card_filter A q
    _ ≤ Finset.sum (Finset.range q) (fun n => g (n + 1) + g n) := hpointwise
    _ = Finset.sum (Finset.range q) (fun n => g (n + 1))
          + Finset.sum (Finset.range q) g := by
          rw [Finset.sum_add_distrib]
    _ ≤ Finset.sum (Finset.Icc 1 q) g + Finset.sum (Finset.Icc 1 q) g := by
          rw [hshift]
          exact add_le_add (le_refl _) hcurr
    _ = 2 * Finset.sum (Finset.Icc 1 q) g := by
          ring

/-- Forme renversée de la borne de marche :
la somme des carrés contrôle au moins la moitié du nombre de pas non nuls. -/
private lemma walk_sqsum_lower_half
    (A : ℕ → ℤ) (hA0 : A 0 = 0) (q : ℕ) :
    (1 / 2 : ℝ) *
      (((Finset.range q).filter (fun n => A (n + 1) ≠ A n)).card : ℝ)
      ≤
    Finset.sum (Finset.Icc 1 q) (fun n => ((A n : ℤ) : ℝ) ^ 2) := by
  have h := walk_stepCount_le_two_sqsum A hA0 q
  linarith

/-- Le pas de la marche de Mertens est non nul exactement aux indices squarefree. -/
private lemma mertens_step_ne_iff_squarefree (n : ℕ) :
    Arithmetic.mertens (n + 1) ≠ Arithmetic.mertens n
      ↔ Squarefree (n + 1) := by
  have hstep := CouretUnification.Arithmetic.mertens_succ_sub n
  have hmu :
      CouretUnification.Arithmetic.mu (n + 1) ≠ 0
        ↔ Squarefree (n + 1) :=
    CouretUnification.Arithmetic.mu_ne_zero_iff_squarefree (by omega)
  constructor
  · intro hneq
    have hmu_ne : CouretUnification.Arithmetic.mu (n + 1) ≠ 0 := by
      intro h0
      have : Arithmetic.mertens (n + 1) - Arithmetic.mertens n = 0 := by
        simpa [h0] using hstep
      exact hneq (sub_eq_zero.mp this)
    exact hmu.mp hmu_ne
  · intro hsq
    have hmu_ne : CouretUnification.Arithmetic.mu (n + 1) ≠ 0 := hmu.mpr hsq
    intro heq
    have : Arithmetic.mertens (n + 1) - Arithmetic.mertens n = 0 := sub_eq_zero.mpr heq
    have hmu0 : CouretUnification.Arithmetic.mu (n + 1) = 0 := by
      simpa [hstep] using this
    exact hmu_ne hmu0

/-- Le nombre de pas non nuls de la marche de Mertens sur `range q`
coïncide avec `squarefreeCount q`. -/
private lemma stepCount_eq_squarefreeCount (q : ℕ) :
    (((Finset.range q).filter
        (fun n => Arithmetic.mertens (n + 1) ≠ Arithmetic.mertens n)).card : ℝ)
      = squarefreeCount q := by
  unfold squarefreeCount
  let s :=
    (Finset.range q).filter
      (fun n => Arithmetic.mertens (n + 1) ≠ Arithmetic.mertens n)
  let t :=
    (Finset.Icc 1 q).filter (fun n => Squarefree n)

  have hcard : s.card = t.card := by
    classical
    refine Finset.card_nbij (fun n => n + 1) ?_ ?_ ?_
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_step⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · refine Finset.mem_Icc.mpr ?_
        constructor
        · exact Nat.succ_le_succ (Nat.zero_le n)
        · exact Nat.succ_le_of_lt (Finset.mem_range.mp hn_range)
      · exact (mertens_step_ne_iff_squarefree n).mp hn_step
    · intro n₁ hn₁ n₂ hn₂ hEq
      exact Nat.succ.inj hEq
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hm_iq, hm_sqf⟩
      refine ⟨m - 1, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ?_
        constructor
        · have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_iq).1
          have hmq : m ≤ q := (Finset.mem_Icc.mp hm_iq).2
          have hm_pos : 0 < m := by
            exact Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
          have hpred : m - 1 < m := Nat.pred_lt (Nat.ne_of_gt hm_pos)
          simpa [Finset.mem_range] using (lt_of_lt_of_le hpred hmq)
        · have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_iq).1
          have hsq' : Squarefree ((m - 1) + 1) := by
            simpa [Nat.sub_add_cancel hm1] using hm_sqf
          exact (mertens_step_ne_iff_squarefree (m - 1)).mpr hsq'
      · exact Nat.sub_add_cancel ((Finset.mem_Icc.mp hm_iq).1)

  exact_mod_cast hcard

/-- Réécriture de `S1 q` comme somme des carrés de `mertens`
sur l’intervalle `Icc 1 q`. -/
private lemma S1_eq_sum_Icc (q : ℕ) :
    S1 q =
      Finset.sum (Finset.Icc 1 q)
        (fun n => (((Arithmetic.mertens n : ℤ) : ℝ) ^ 2)) := by
  unfold S1
  have hsplit : Finset.range (q + 1) = insert 0 (Finset.Icc 1 q) := by
    ext n
    simp [Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert]
  · simp
    apply Finset.sum_congr rfl
    intro n hn
    have hn_pos : 0 < n := by
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    simp [hn_pos]
  · simp

/-- Une fraction positive des indices squarefree contribue à `S1`. -/
theorem S1_lower_from_squarefree :
    ∃ β : ℝ, 0 < β ∧
      ∀ q : ℕ, β * squarefreeCount q ≤ S1 q := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro q
  have hwalk := walk_sqsum_lower_half Arithmetic.mertens
    (by simpa using CouretUnification.Arithmetic.mertens_zero) q
  rw [stepCount_eq_squarefreeCount q] at hwalk
  rw [← S1_eq_sum_Icc q] at hwalk
  exact hwalk

/-- **Verrou analytique (Route C)** — contrôle `θ < 1` des pièces d’erreur. -/
theorem routeC_error_control :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        Finset.sum (ErrorPieces (primorial n))
          (fun d => |E (primorial n) d|)
          ≤ θ * MainTerm (primorial n) := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- §6. Recollements algébriques (fermés)
-- ═══════════════════════════════════════════════════════════

/-- Spécialisation de la borne globale squarefree à la tour primorielle. -/
theorem squarefreeCount_linear_on_primorial :
    ∃ n₀ : ℕ, ∃ α : ℝ, 0 < α ∧
      ∀ n : ℕ, n₀ ≤ n →
        α * (primorial n : ℝ) ≤ squarefreeCount (primorial n) := by
  obtain ⟨α, hα, hsq⟩ := squarefreeCount_linear_global
  exact ⟨0, α, hα, fun n _ => hsq (primorial n)⟩

/-- Recombinaison Front 1 : sous-verrous squarefree → `S1 ≫ q`. -/
theorem S1_linear_on_primorial_from_squarefree
    (h1 : ∃ β : ℝ, 0 < β ∧
      ∀ q : ℕ, β * squarefreeCount q ≤ S1 q)
    (h2 : ∃ n₀ : ℕ, ∃ α : ℝ, 0 < α ∧
      ∀ n : ℕ, n₀ ≤ n →
        α * (primorial n : ℝ) ≤ squarefreeCount (primorial n)) :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * (primorial n : ℝ) ≤ S1 (primorial n) := by
  obtain ⟨β, hβ, hβq⟩ := h1
  obtain ⟨n₀, α, hα, hαn⟩ := h2
  refine ⟨n₀, α * β, mul_pos hα hβ, ?_⟩
  intro n hn
  have hsq := hαn n hn
  have hS := hβq (primorial n)
  nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hβ)]

/-- Croissance linéaire de `S1` le long de la tour primorielle. -/
theorem S1_linear_on_primorial :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * (primorial n : ℝ) ≤ S1 (primorial n) :=
  S1_linear_on_primorial_from_squarefree
    S1_lower_from_squarefree
    squarefreeCount_linear_on_primorial

-- ═══════════════════════════════════════════════════════════
-- §7. Verrous Route C classiques, fermés
-- ═══════════════════════════════════════════════════════════

/-- Borne inférieure du terme principal le long de la tour primorielle. -/
theorem routeC_main_lower :
    ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * phi (primorial n) ≤ MainTerm (primorial n) := by
  obtain ⟨n₀, A, hA, hS1⟩ := S1_linear_on_primorial
  refine ⟨n₀, A, hA, ?_⟩
  intro n hn
  unfold MainTerm
  have hS := hS1 n hn
  have hq : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hphi_nn : 0 ≤ phi (primorial n) := phi_primorial_nonneg n
  rw [div_mul_eq_mul_div, le_div_iff₀ hq]
  nlinarith [mul_le_mul_of_nonneg_left hS hphi_nn]

/-- Borne supérieure de l’erreur, obtenue depuis le verrou `routeC_error_control`. -/
theorem routeC_error_upper :
    ∃ n₀ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₀ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n) := by
  obtain ⟨n₀, θ, hθlt, hθnn, hctrl⟩ := routeC_error_control
  refine ⟨n₀, θ, hθlt, hθnn, ?_⟩
  intro n hn
  rw [errorTerm_decomposition]
  calc
    |Finset.sum (ErrorPieces (primorial n)) (fun d => E (primorial n) d)|
        ≤ Finset.sum (ErrorPieces (primorial n))
            (fun d => |E (primorial n) d|) :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ θ * MainTerm (primorial n) := hctrl n hn

-- ═══════════════════════════════════════════════════════════
-- §8. Recollement Route C
-- ═══════════════════════════════════════════════════════════

/-- Recollement Route C : borne principale positive + erreur contrôlée
impliquent une borne inférieure positive sur `K`. -/
theorem routeC_from_main_error
    (hmain : ∃ n₀ : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, n₀ ≤ n → A * phi (primorial n) ≤ MainTerm (primorial n))
    (herr : ∃ n₁ : ℕ, ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      ∀ n : ℕ, n₁ ≤ n →
        |ErrorTerm (primorial n)| ≤ θ * MainTerm (primorial n)) :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n) := by
  obtain ⟨n₀, A, hA, hmain⟩ := hmain
  obtain ⟨n₁, θ, hθ_lt, hθ_nn, herr⟩ := herr
  refine ⟨max n₀ n₁, (1 - θ) * A, mul_pos (by linarith) hA, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := le_trans (le_max_left n₀ n₁) hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_right n₀ n₁) hn
  have hM := hmain n hn₀
  have hE := herr n hn₁
  have hE_lower := (abs_le.mp hE).1
  rw [K_decomposition]
  nlinarith [mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 - θ by linarith)]

-- ═══════════════════════════════════════════════════════════
-- §9. Chaîne complète (A) → (B) → (C)
-- ═══════════════════════════════════════════════════════════

/-- (A) Énoncé central de la Route C. -/
theorem routeC_explicit_core :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n) :=
  routeC_from_main_error routeC_main_lower routeC_error_upper

/-- (B) Passage d’une borne inférieure sur K/φ à une borne inférieure sur κ. -/
theorem kappa_explicit_bound
    (hmain : ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n)) :
    ∃ n₀ : ℕ, ∃ lam : ℝ, 0 < lam ∧
      ∀ n : ℕ, n₀ ≤ n → lam ≤ kappa (primorial n) := by
  obtain ⟨n₀, c, hc, hK⟩ := hmain
  refine ⟨n₀, Real.sqrt c, Real.sqrt_pos_of_pos hc, ?_⟩
  intro n hn
  unfold kappa CouretUnification.Arithmetic.kappa
  change Real.sqrt c ≤ Real.sqrt (K (primorial n) / phi (primorial n))
  apply Real.sqrt_le_sqrt
  have hphi : 0 < phi (primorial n) := phi_primorial_pos n
  exact (le_div_iff₀ hphi).mpr (hK n hn)

/-- (C) Positivité éventuelle de κ le long de la tour primorielle. -/
theorem kappa_eventually_pos
    (hmain : ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → c * phi (primorial n) ≤ K (primorial n)) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) := by
  obtain ⟨n₀, lam, hlam, hbound⟩ := kappa_explicit_bound hmain
  exact ⟨lam, hlam, Filter.eventually_atTop.mpr ⟨n₀, hbound⟩⟩

/-- Conclusion complète de la Route C. -/
theorem kappa_pos_from_routeC :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ᶠ n in Filter.atTop, lam ≤ kappa (primorial n) :=
  kappa_eventually_pos routeC_explicit_core

-- ═══════════════════════════════════════════════════════════
-- §10. Gouvernance
-- ═══════════════════════════════════════════════════════════

/-- Drapeau doctrinal : aucune revendication RH dans ce fichier. -/
def RHClaimed : Bool := false

/-- Vérification du drapeau doctrinal. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Logic.H3.RouteC
