/-
Couret-Unification — v38.5.8
# CouretUnification/Logic/H3/SquarefreeDensity.lean

## Rôle

Bloc H3 consacré à la densité des entiers squarefree.

Le fichier sépare explicitement deux niveaux :

1. **Partie robuste déjà fermée**
   - réindexation arithmétique de type Fubini (`sum_squarefree_fubini`)
   - contrôle local de l’erreur euclidienne (`div_eucl_real_error`)

2. **Partie analytique encore ouverte**
   - majoration globale de l’erreur en `O(√N)`
   - minoration uniforme `squarefreeCount_ge_half`
   - densité asymptotique `6 / π²`

Cette séparation reflète la doctrine du dépôt :
les identités discrètes exactes sont fermées dès que possible,
tandis que les coutures asymptotiques restent isolées comme dettes analytiques explicites.

## Statut

- Couche      : Logic / H3 alias Diamond (Analytic density)
- Front       : C — densité squarefree
- RHClaimed   : false
- Sorry count : 2

### Détail des statuts

- C-00 : définition de `squarefreeCount`                              [definitional]
- C-01 : réindexation Fubini arithmétique (`sum_squarefree_fubini`)   [proved]
- C-02 : erreur locale division entière / réelle                      [proved]
- C-03 : terme d’erreur global `O(√N)`                                [proved]
- C-04a : minoration robuste `squarefreeCount_ge_half`                [analytic sorry]
- C-04b : densité asymptotique `squarefree_asymptotic_density`        [analytic sorry]

## Doctrine

Séparation stricte entre :

- **C(ii)** : bornes robustes utilisables sur le chemin critique
- **C(i)**  : asymptotique complète vers `6 / π²`, laissée comme cible projet

Autrement dit :
le fichier ferme le squelette discret/combinatoire,
mais ne prétend pas fermer la couture analytique finale.

## Notes snapshot (Mathlib v4.29.1)

Les points sensibles du snapshot sont les suivants :

- `Finset.sum_sigma'`
- `Finset.sum_bij` (ordre des sous-buts dépendant du snapshot)
- `Nat.div_add_mod`
- `Nat.le_sqrt'`
- `Nat.le_div_iff_mul_le`
- `div_le_one`
- réécritures entre `d^2` et produits commutés (`Nat.mul_comm`)

Si un snapshot futur casse C-01 ou C-02, il faut d’abord suspecter
une variation de signature des lemmes Finset/Nat avant de toucher à la structure logique.

## Invariant de lecture

Ce fichier est actuellement **mécaniquement propre** sur sa partie discrète :
les seuls `sorry` restants sont analytiques et explicitement documentés.
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs -- or .Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- C-00. Nombre d'entiers squarefree jusqu'à N. -/
def squarefreeCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Squarefree).card

/-- C-01. Réindexation Fubini arithmétique par isomorphisme Sigma.

    ∑_{n ≤ N} ∑_{d² ∣ n} f(d) = ∑_{d ≤ √N} ∑_{k ≤ N/d²} f(d)

    Preuve : aplatissement via sum_sigma + bijection (d,k) ↦ (k·d², d).
    Tactique centrale : Finset.sum_bij avec omega pour la clôture des domaines.

    [SNAPSHOT WARNING] : La signature exacte de `Finset.sum_bij` dépend du snapshot.
    La variante `Finset.sum_nbij'` peut être requise selon version. -/
lemma sum_squarefree_fubini (N : ℕ) (f : ℕ → ℤ) :
    Finset.sum (Icc 1 N) (fun n =>
      Finset.sum ((Icc 1 n).filter (fun d => d^2 ∣ n)) (fun d => f d)) =
    Finset.sum (Icc 1 (Nat.sqrt N)) (fun d =>
      Finset.sum (Icc 1 (N / d^2)) (fun _k => f d)) := by
  apply Eq.symm
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij
    (fun a _ => match a with
      | ⟨d, k⟩ => (⟨k * d^2, d⟩ : Σ _ : ℕ, ℕ))
    ?hi ?hinj ?hsurj ?hval
  · rintro ⟨d, k⟩ ha
    have hmem : d ∈ Icc 1 (Nat.sqrt N) ∧ k ∈ Icc 1 (N / d^2) := by
      simpa [Finset.mem_sigma] using ha
    rcases hmem with ⟨hd, hk⟩
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hd2⟩
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine Finset.mem_sigma.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have : 1 ≤ d^2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · calc
        k * d^2 ≤ (N / d^2) * d^2 := Nat.mul_le_mul_right _ hk2
        _ ≤ N := Nat.div_mul_le_self N (d^2)
    · refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_Icc.mpr ⟨hd1, ?_⟩, Dvd.intro_left k rfl⟩
      have hk_pos : 0 < k := hk1
      nlinarith [sq_nonneg d]

  · rintro ⟨d₁, k₁⟩ ha₁ ⟨d₂, k₂⟩ ha₂ hEq
    have hmem1 : d₁ ∈ Icc 1 (Nat.sqrt N) ∧ k₁ ∈ Icc 1 (N / d₁^2) := by
      simpa [Finset.mem_sigma] using ha₁
    simp only [Sigma.mk.injEq] at hEq
    rcases hEq with ⟨hprod, hdEq⟩
    cases hdEq
    have hdpos : 0 < d₁^2 := by
      rcases Finset.mem_Icc.mp hmem1.1 with ⟨hd1, _⟩
      positivity
    have hkEq : k₁ = k₂ := Nat.eq_of_mul_eq_mul_right hdpos hprod
    simp [hkEq]

  · rintro ⟨n, d⟩ hb
    have hmem : n ∈ Icc 1 N ∧ d ∈ (Icc 1 n).filter (fun d => d^2 ∣ n) := by
      simpa [Finset.mem_sigma] using hb
    rcases hmem with ⟨hn, hdmem⟩
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hn2⟩
    rcases Finset.mem_filter.mp hdmem with ⟨hdIcc, hdiv⟩
    rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hd2⟩
    obtain ⟨k, hk_eq⟩ := hdiv
    refine ⟨⟨d, k⟩, ?_, ?_⟩
    · refine Finset.mem_sigma.mpr ?_
      refine ⟨Finset.mem_Icc.mpr ⟨hd1, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
      · have hk_pos : 0 < k := by
          by_contra hk_not
          have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk_not
          rw [hk0, mul_zero] at hk_eq
          omega
        have hd_sq_le_n : d ^ 2 ≤ n := by
          calc
            d ^ 2 ≤ d ^ 2 * k := Nat.le_mul_of_pos_right _ hk_pos
            _ = n := by
                  simpa [Nat.mul_comm] using hk_eq.symm
        exact (Nat.le_sqrt'.2 (le_trans hd_sq_le_n hn2))
      · have hk_pos : 0 < k := by
          by_contra hk_not
          have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk_not
          rw [hk0, mul_zero] at hk_eq
          omega
        exact hk_pos
      · have hd2_pos : 0 < d^2 := by positivity
        rw [Nat.le_div_iff_mul_le hd2_pos]
        calc
          k * d^2 = d^2 * k := by ring
          _ = n := by simpa [Nat.mul_comm] using hk_eq.symm
          _ ≤ N := hn2
    · simpa [Sigma.mk.injEq, Nat.mul_comm] using hk_eq.symm

  · rintro ⟨d, k⟩ ha
    simp

/-- C-02. Erreur locale de coercition entre division entière et division réelle.

    |⌊N/d²⌋ - N/d²| ≤ 1

    Preuve : s'appuie sur Nat.div_add_mod pour injecter l'égalité stricte
    dans ℝ, puis borner le reste fractionnaire. -/
lemma div_eucl_real_error (N d : ℕ) (hd : d ≠ 0) :
    |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2| ≤ 1 := by
  have hd2_pos : 0 < d^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hd)
  have hd2R_pos : 0 < (d : ℝ)^2 := by
    exact_mod_cast hd2_pos

  have h_div_mod : (N : ℝ) = (d^2 : ℝ) * (N / d^2 : ℕ) + (N % d^2 : ℕ) := by
    have := (Nat.div_add_mod N (d^2)).symm
    exact_mod_cast this

  have h_frac :
      (N : ℝ) / (d : ℝ)^2 =
        ((N / d^2 : ℕ) : ℝ) + ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 := by
    have hne : ((d : ℝ)^2) ≠ 0 := ne_of_gt hd2R_pos
    rw [h_div_mod]
    field_simp [hne]

  rw [h_frac]

  have h_mod_lt : ((N % d^2 : ℕ) : ℝ) < (d : ℝ)^2 := by
    have := Nat.mod_lt N hd2_pos
    exact_mod_cast this

  have h_mod_nonneg : 0 ≤ ((N % d^2 : ℕ) : ℝ) := by
    positivity

  have h_ratio_nonneg : 0 ≤ ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 := by
    exact div_nonneg h_mod_nonneg hd2R_pos.le

  calc
    |((N / d^2 : ℕ) : ℝ) -
        (((N / d^2 : ℕ) : ℝ) + ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2)|
        = |((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2| := by
            have htmp :
                ((N / d^2 : ℕ) : ℝ) -
                    (((N / d^2 : ℕ) : ℝ) + ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2)
                  = -(((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2) := by
              ring
            rw [htmp, abs_neg]
    _ = ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 := by
          rw [abs_of_nonneg h_ratio_nonneg]
    _ ≤ 1 := by
          exact (div_le_one hd2R_pos).2 h_mod_lt.le

/-- C-03. Le terme d'erreur global est O(√N).

    Chaque terme est borné par 1 via C-02, et il y a au plus `Nat.sqrt N`
    termes dans `Icc 1 (Nat.sqrt N)`. Le passage vers `Real.sqrt N`
    utilise `Real.nat_sqrt_le_real_sqrt`. -/
lemma error_term_isBigO :
    IsBigO atTop
      (fun N : ℕ =>
        Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
          |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2|))
      (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  exact eventually_atTop.2 ⟨0, by
    intro N _hN

    let A : ℝ :=
      Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
        |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2|)

    change ‖A‖ ≤ (1 : ℝ) * ‖Real.sqrt (N : ℝ)‖

    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact Finset.sum_nonneg (by
        intro d _hd
        exact abs_nonneg _)

    have hA_le_card :
        A ≤ ((Finset.Icc 1 (Nat.sqrt N)).card : ℝ) := by
      dsimp [A]
      calc
        Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
            |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2|)
            ≤ Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun _d => (1 : ℝ)) := by
                refine Finset.sum_le_sum ?_
                intro d hd
                have hd_ne : d ≠ 0 := by
                  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
                  omega
                exact div_eucl_real_error N d hd_ne
        _ = ((Finset.Icc 1 (Nat.sqrt N)).card : ℝ) := by
                simp

    have hcard_le_nat_sqrt :
        ((Finset.Icc 1 (Nat.sqrt N)).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
      have hcard_nat :
          (Finset.Icc 1 (Nat.sqrt N)).card ≤ Nat.sqrt N := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hcard_nat

    have hnat_sqrt_le_real_sqrt :
        (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
      exact Real.nat_sqrt_le_real_sqrt

    have hA_le_sqrt : A ≤ Real.sqrt (N : ℝ) :=
      le_trans hA_le_card
        (le_trans hcard_le_nat_sqrt hnat_sqrt_le_real_sqrt)

    have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_nonneg _

    simpa [norm_of_nonneg hA_nonneg, norm_of_nonneg hsqrt_nonneg]
      using hA_le_sqrt
  ⟩

/-- C-04a. Version robuste prioritaire : minoration compilable.

    Au-delà d'un seuil N₀ = 176, au moins N/2 entiers sont squarefree.
    [ANALYTIC SORRY — branchement aux C-01, C-02, C-03] -/
theorem squarefreeCount_ge_half {N : ℕ} (hN : 176 ≤ N) :
    (N : ℚ) / 2 ≤ squarefreeCount N := by
  sorry

/-- C-04b. Théorème de densité asymptotique : densité 6/π².

    [ANALYTIC SORRY - CIBLE PROJET]
    Nécessite la couture complète de C-01, C-03, et la série
    ∑ μ(d)/d² = 1/ζ(2) = 6/π² (via MoebiusBridge). -/
theorem squarefree_asymptotic_density :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) := by
  sorry

end CouretUnification.Logic.H3
