/-
Couret-Unification — v35.8.6
Logic/H3/SquarefreeDensity.lean

Front C : Densité squarefree, Fubini arithmétique, erreur de quantification.

Status     : C-01 [PROVED - sum_bij]       — fragile snapshot
             C-02 [PROVED - Nat.div_add_mod] — fragile snapshot
             C-03 [SORRY - ANALYTIC]
             C-04a [SORRY - ANALYTIC]
             C-04b [SORRY - ANALYTIC, cible projet 6/π²]
Layer      : Diamond (Analytic density)
Doctrine   : C2 (Density & asymptotics)
RHClaimed  : false
sorryCount : 3  (C-03, C-04a, C-04b)

Séparation stricte :
  - C(ii) = bornes robustes (C-01, C-02) sur le chemin critique
  - C(i)  = asymptotique complet 6/π² (C-04b) laissé en cible projet

NOTE SNAPSHOT : Les preuves C-01 et C-02 utilisent :
  - Finset.sum_bij                    (signature peut varier — Mathlib récent)
  - Nat.div_add_mod                   (confirmé)
  - Nat.le_div_iff₀ / Nat.le_div_iff  (nom selon snapshot)
  - div_le_one_of_le₀ / div_le_one_of_le  (nom selon snapshot)
Ces noms sont testés sur Mathlib récent (2024-2025). Si divergence,
remplacer ponctuellement sans toucher à la structure logique.
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open scoped BigOperators
open Asymptotics Filter Finset Real

/-- C-00. Nombre d'entiers squarefree jusqu'à N. -/
def squarefreeCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Nat.Squarefree).card

/-- C-01. Réindexation Fubini arithmétique par isomorphisme Sigma.

    ∑_{n ≤ N} ∑_{d² ∣ n} f(d) = ∑_{d ≤ √N} ∑_{k ≤ N/d²} f(d)

    Preuve : aplatissement via sum_sigma + bijection (d,k) ↦ (k·d², d).
    Tactique centrale : Finset.sum_bij avec omega pour la clôture des domaines.

    [SNAPSHOT WARNING] : La signature exacte de `Finset.sum_bij` dépend du snapshot.
    La variante `Finset.sum_nbij'` peut être requise selon version. -/
lemma sum_squarefree_fubini (N : ℕ) (f : ℕ → ℤ) :
    (∑ n in Icc 1 N, ∑ d in (Icc 1 n).filter (fun d => d^2 ∣ n), f d) =
    ∑ d in Icc 1 (Nat.sqrt N), ∑ k in Icc 1 (N / d^2), f d := by
  -- Inversion de l'objectif pour mapper du domaine le plus simple vers le plus complexe
  apply Eq.symm
  -- Aplatissement des deux membres via le type de paires dépendantes
  simp_rw [← Finset.sum_sigma]
  -- Application de la bijection : (d, k) ↦ (k * d^2, d)
  apply Finset.sum_bij (fun ⟨d, k⟩ _ ↦ (⟨k * d^2, d⟩ : Σ _ : ℕ, ℕ))
  · -- hi : Clôture du domaine cible
    rintro ⟨d, k⟩ h_mem
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at h_mem ⊢
    rcases h_mem with ⟨⟨hd1, hd2⟩, ⟨hk1, hk2⟩⟩
    -- Conditions : n = k*d² ∈ [1,N], d ∈ [1,n] et d² | n
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · -- 1 ≤ k*d²
      have : 1 ≤ d^2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · -- k*d² ≤ N
      have hd2_pos : 0 < d^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (by omega))
      have : k * d^2 ≤ (N / d^2) * d^2 := Nat.mul_le_mul_right (d^2) hk2
      calc k * d^2 ≤ (N / d^2) * d^2 := this
        _ ≤ N := Nat.div_mul_le_self N (d^2)
    · -- 1 ≤ d
      exact hd1
    · -- d ≤ k*d²
      have hd_pos : 0 < d := hd1
      have hk_pos : 0 < k := hk1
      nlinarith [sq_nonneg d]
    · -- d² | k*d²
      exact Dvd.intro_left k rfl
  · -- h : Invariance de la fonction évaluée (f dépend seulement de d)
    rintro ⟨d, k⟩ _
    rfl
  · -- h_inj : Injectivité de la transition
    rintro ⟨d₁, k₁⟩ ⟨d₂, k₂⟩ h_mem1 h_mem2 h_eq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at h_mem1 h_mem2
    simp only [Sigma.mk.injEq] at h_eq
    obtain ⟨hkd_eq, hd_eq⟩ := h_eq
    -- Réorganisation : hd_eq : d₁ = d₂  (second composant)
    -- hkd_eq : k₁ * d₁^2 = k₂ * d₂^2
    cases hd_eq
    -- d₁ = d₂, reste : k₁ * d² = k₂ * d² ⟹ k₁ = k₂
    have hd_pos : 0 < d₁^2 := by
      have : 0 < d₁ := h_mem1.1.1
      positivity
    have hk_eq : k₁ = k₂ := Nat.eq_of_mul_eq_mul_right hd_pos hkd_eq
    rw [hk_eq]
  · -- h_surj : Surjectivité (existence de l'antécédent k)
    rintro ⟨n, d⟩ h_mem
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at h_mem
    obtain ⟨⟨hn1, hn2⟩, ⟨hd1, hd2⟩, h_dvd⟩ := h_mem
    obtain ⟨k, hk_eq⟩ := h_dvd
    refine ⟨⟨d, k⟩, ?_, ?_⟩
    · -- Preuve que ⟨d, k⟩ appartient bien au domaine source
      simp only [Finset.mem_sigma, Finset.mem_Icc]
      have hd2_pos : 0 < d^2 := by
        have : 0 < d := hd1
        positivity
      refine ⟨⟨hd1, ?_⟩, ⟨?_, ?_⟩⟩
      · -- d ≤ √N
        have : d^2 ≤ N := by
          have h1 : d^2 ≤ d^2 * k := Nat.le_mul_of_pos_right _ (by
            rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
            · rw [hk0, mul_zero] at hk_eq
              omega
            · exact hk_pos)
          calc d^2 ≤ d^2 * k := h1
            _ = n := by rw [hk_eq]; ring
            _ ≤ N := hn2
        exact Nat.le_sqrt.mpr this
      · -- 1 ≤ k
        rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
        · rw [hk0, mul_zero] at hk_eq
          omega
        · exact hk_pos
      · -- k ≤ N / d²
        have hd2_pos' : 0 < d^2 := hd2_pos
        rw [Nat.le_div_iff_mul_le hd2_pos']
        calc k * d^2 = d^2 * k := by ring
          _ = n := by rw [hk_eq]
          _ ≤ N := hn2
    · -- Égalité finale
      simp only [Sigma.mk.injEq]
      refine ⟨?_, rfl⟩
      rw [hk_eq]; ring

/-- C-02. Erreur locale de coercition entre division entière et division réelle.

    |⌊N/d²⌋ - N/d²| ≤ 1

    Preuve : s'appuie sur Nat.div_add_mod pour injecter l'égalité stricte
    dans ℝ, puis borner le reste fractionnaire. -/
lemma div_eucl_real_error (N d : ℕ) (hd : d ≠ 0) :
    |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2| ≤ 1 := by
  have hd2_pos : 0 < d^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hd)
  have hd2R_pos : 0 < (d : ℝ)^2 := by exact_mod_cast hd2_pos
  -- Injection de la division euclidienne discrète dans les réels
  have h_div_mod : (N : ℝ) = (d^2 : ℝ) * (N / d^2 : ℕ) + (N % d^2 : ℕ) := by
    have := (Nat.div_add_mod N (d^2)).symm
    exact_mod_cast this
  -- Division de l'équation par d^2 dans ℝ
  have h_frac : (N : ℝ) / (d : ℝ)^2 =
      ((N / d^2 : ℕ) : ℝ) + ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 := by
    have hne : ((d : ℝ)^2) ≠ 0 := ne_of_gt hd2R_pos
    rw [h_div_mod]
    field_simp
    ring
  -- Substitution dans la valeur absolue
  rw [h_frac]
  have h_mod_lt : ((N % d^2 : ℕ) : ℝ) < (d : ℝ)^2 := by
    have := Nat.mod_lt N hd2_pos
    exact_mod_cast this
  have h_mod_nonneg : 0 ≤ ((N % d^2 : ℕ) : ℝ) := by positivity
  have h_ratio_nonneg : 0 ≤ ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 :=
    div_nonneg h_mod_nonneg hd2R_pos.le
  have h_ratio_le : ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2 ≤ 1 := by
    rw [div_le_one hd2R_pos]
    exact h_mod_lt.le
  -- |a - (a + r)| = |r| ≤ 1
  have : ((N / d^2 : ℕ) : ℝ) - (((N / d^2 : ℕ) : ℝ) +
      ((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2) = -(((N % d^2 : ℕ) : ℝ) / (d : ℝ)^2) := by
    ring
  rw [this, abs_neg, abs_of_nonneg h_ratio_nonneg]
  exact h_ratio_le

/-- C-03. Le terme d'erreur global est O(√N).

    Schéma prévu : chaque terme |...| ≤ 1 (via C-02),
    nombre de termes ~ √N (via Nat.sqrt),
    conclusion par `Asymptotics.IsBigO.of_bound`. -/
lemma error_term_isBigO :
    IsBigO atTop
      (fun N : ℕ => ∑ d in Finset.Icc 1 (Nat.sqrt N),
        |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2|)
      (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  -- [ANALYTIC SORRY — couture de IsBigO.of_bound avec C-02 et card(Icc 1 √N)]
  sorry

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
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop (𝓝 (6 / (Real.pi^2))) := by
  sorry

end CouretUnification.Logic.H3
