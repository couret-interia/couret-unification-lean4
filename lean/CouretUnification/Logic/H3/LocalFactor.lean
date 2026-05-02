/-
Couret-Unification — v35.8.6
Logic/H3/LocalFactor.lean

Front A : Identité et bornes de la norme carrée du facteur local d'Euler
         |1 - a * exp(iθ)|²

Status     : proved (sous réserve de compilation contre snapshot Mathlib récent)
Layer      : Gold (Analytic)
Doctrine   : C3 (Spectral / analytic support)
RHClaimed  : false  (invariant préservé)
sorryCount : 0

Dépendances principales :
  - Complex.exp_mul_I        : exp(iθ) = cos θ + i sin θ
  - Real.neg_one_le_cos, Real.cos_le_one
  - Real.rpow_nonneg, Real.rpow_le_one_of_one_le_of_nonpos
  - Real.one_le_sqrt

NOTE SNAPSHOT : Les noms suivants sont sujets à variation selon la version
de Mathlib compilée :
  - Real.rpow_le_one_of_one_le_of_nonpos   (confirmé en Mathlib récente)
  - Real.one_le_sqrt                        (confirmé)
Si un de ces noms diverge, remplacer ponctuellement sans toucher à la structure.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace CouretUnification.Logic.H3

open Complex Real

/-- A-01. Identité locale de norme carrée.
    Cible mathématique : |1 - a * exp(iθ)|² = 1 - 2 a cos θ + a² -/
lemma local_factor_normSq (a θ : ℝ) :
    Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      1 - 2 * a * Real.cos θ + a^2 := by
  have hexp :
      Complex.exp ((θ : ℂ) * Complex.I) =
        (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using Complex.exp_mul_I (θ : ℂ)
  rw [hexp]
  simp [Complex.normSq, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  ring

/-- A-02. Bornes locales uniformes sous 0 ≤ a ≤ 1. -/
lemma local_factor_normSq_bounds (a θ : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a)^2 ≤ Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∧
    Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≤ (1 + a)^2 := by
  constructor
  · rw [local_factor_normSq]
    have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  · rw [local_factor_normSq]
    have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
    nlinarith

/-- A-03. Spécialisation arithmétique a = 1 / sqrt p. -/
lemma local_factor_prime_half (p : ℕ) (hp : Nat.Prime p) (θ : ℝ) :
    let a : ℝ := 1 / Real.sqrt (p : ℝ)
    (1 - a)^2 ≤ Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∧
    Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≤ (1 + a)^2 := by
  intro a
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hsqrt_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.pos
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have : (1 : ℝ)^2 ≤ (p : ℝ) := by nlinarith
    exact Real.one_le_sqrt this
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith
  simpa [a] using local_factor_normSq_bounds a θ ha0 ha1

/-- A-04. Version sigma ≥ 0 avec a = p^(-σ).

    Preuve fermée : utilise `Real.rpow_le_one_of_one_le_of_nonpos` (Mathlib 4 récent).
    Si ce nom diverge dans un snapshot, les alternatives voisines sont :
      - `Real.rpow_le_one` (base ≥ 0 et ≤ 1)  → mauvaise direction ici
      - preuve via `1 ≤ p^σ` puis `p^(-σ) = 1 / p^σ` avec `Real.rpow_neg`,
        et conclusion par `one_div_le_one_of_one_le`.
-/
lemma local_factor_prime_sigma (p : ℕ) (hp : Nat.Prime p) (σ θ : ℝ) (hσ : 0 ≤ σ) :
    let a : ℝ := (p : ℝ) ^ (-σ)
    (1 - a)^2 ≤ Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∧
    Complex.normSq (1 - (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≤ (1 + a)^2 := by
  intro a
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.pos
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact Real.rpow_nonneg hp_nonneg (-σ)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    -- p ≥ 1 et -σ ≤ 0 ⟹ p^(-σ) ≤ 1
    exact Real.rpow_le_one_of_one_le_of_nonpos hp_ge_one (by linarith)
  simpa [a] using local_factor_normSq_bounds a θ ha0 ha1

end CouretUnification.Logic.H3
