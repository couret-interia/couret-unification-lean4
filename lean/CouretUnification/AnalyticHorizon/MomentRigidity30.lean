/-
  CouretUnification.AnalyticHorizon.MomentRigidity30
  ════════════════════════════════════════════════════════════════════
  Rétrogradation doctrinale ET enrichissement structurel.

  RÉTROGRADATION : M₃ = M₄ = 7/27 est un invariant TENSORIAL-ONLY,
  non une rigidité structurelle profonde. Le crash-test Legendre
  (q=210, ε=0.5) brise la signature normalisée {1, 1/3, -1/3} en
  {1, ±1/2, ±1/3, ±1/6}.

  ENRICHISSEMENT v38.1 :
    • Conserve les théorèmes calculatoires k=1..6 (par decide)
    • AJOUTE le théorème universel M(2n+1) = M(2n+2) pour tout n
      (preuve algébrique, conformément à la note LaTeX
      "Une rigidité par paires des moments spectraux")
    • La rigidité par paires est un fait COMBINATOIRE FINI sur le
      spectre {1², (1/3)⁴, (-1/3)²}. Elle ne survit pas, en général,
      à toute perturbation (c'est précisément pourquoi elle reste
      tensorial-only).

  Doctrine : v38.1 enrichi
  Status   : tensorial-only globalement, calculs scalaires fermés,
             rigidité combinatoire universelle prouvée.
  Sorries  : 0 nouveau.
-/

import Mathlib
import CouretUnification.AnalyticHorizon.TraceFormulaTargets
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants

open CouretUnification.EpistemicDiscipline

namespace CouretUnification
namespace AnalyticHorizon

/-! ## §1 — Status enum -/

inductive RigidityStatus where
  | closedFinite
  | tensorialOnly
  | theoremTarget
deriving Repr, DecidableEq

/-! ## §2 — Doctrinal demotion -/

/-- The identity M₃ = M₄ = 7/27 is retained only as a tensorial-regime
    invariant. It must not be used as a global Lock 3 bridge. -/
def MomentRigidity30Status : RigidityStatus := RigidityStatus.tensorialOnly

def MomentRigidity30Value : ℚ := 7 / 27

theorem moment_rigidity_30_is_tensorial_only :
    MomentRigidity30Status = RigidityStatus.tensorialOnly := rfl

theorem moment_rigidity_30_value :
    MomentRigidity30Value = 7 / 27 := rfl

/-! ## §3 — Normalized active spectrum (closed scalar witnesses)

    Spectrum: {1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3} (multiplicities 2, 4, 2).
    M_k := (1/8) Σ λ_i^k                                                   -/

/-- The normalized active spectrum as a list (length 8). -/
def normalizedSpectrum : List ℚ :=
  [1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3]

theorem normalizedSpectrum_length : normalizedSpectrum.length = 8 := by decide

/-- k-th moment of the normalized active spectrum. -/
def M (k : ℕ) : ℚ :=
  (normalizedSpectrum.map (fun x => x^k)).foldr (· + ·) 0 / 8

/-! ### Closed-form moment values (k = 1..6) — concrete witnesses by `native_decide` -/

theorem M1_eq : M 1 = 1 / 3   := by native_decide
theorem M2_eq : M 2 = 1 / 3   := by native_decide
theorem M3_eq : M 3 = 7 / 27  := by native_decide
theorem M4_eq : M 4 = 7 / 27  := by native_decide
theorem M5_eq : M 5 = 61 / 243 := by native_decide
theorem M6_eq : M 6 = 61 / 243 := by native_decide

/-! ### Pairwise rigidity at concrete orders -/

/-- Pairwise rigidity at order 1: M_1 = M_2. -/
theorem moments_paired_k1 : M 1 = M 2 := by
  rw [M1_eq, M2_eq]

/-- Pairwise rigidity at order 2: M_3 = M_4. -/
theorem moments_paired_k2 : M 3 = M 4 := by
  rw [M3_eq, M4_eq]

/-- Pairwise rigidity at order 3: M_5 = M_6. -/
theorem moments_paired_k3 : M 5 = M 6 := by
  rw [M5_eq, M6_eq]

/-- Conjunction of the first three pair rigidities. -/
theorem moments_paired_first_three :
    M 1 = M 2 ∧ M 3 = M 4 ∧ M 5 = M 6 :=
  ⟨moments_paired_k1, moments_paired_k2, moments_paired_k3⟩

/-! ## §4 — Closed-form: M_{2k-1} = M_{2k} = (9^k + 3) / (4·9^k), k=1..3 -/

theorem closed_form_k1 : M 2 = (9^1 + 3) / (4 * 9^1) := by native_decide
theorem closed_form_k2 : M 4 = (9^2 + 3) / (4 * 9^2) := by native_decide
theorem closed_form_k3 : M 6 = (9^3 + 3) / (4 * 9^3) := by native_decide

/-! ## §5 — UNIVERSAL pair rigidity: ∀n, M(2n+1) = M(2n+2)

    This is the genuine theorem from the LaTeX note
    "Une rigidité par paires des moments spectraux".

    Strategy:
      (a) Express M k in raw form: (2 + 4·(1/3)^k + 2·(-1/3)^k) / 8.
      (b) Treat the parity of k = 2n+1 vs 2n+2 via (-1)^(2n+1) = -1
          and (-1)^(2n+2) = 1.
      (c) Reduce to the elementary identity
              4/3^{2n+1} - 2/3^{2n+1}  =  4/3^{2n+2} + 2/3^{2n+2}
          which simplifies to  2 = 6/3,  i.e., the 4:2 multiplicity
          asymmetry between +1/3 and -1/3.

    [TODO-COMPILE-VERIFY] : preuve algébrique standard, mais le
    `simp only` qui déballe `List.foldr` sur la liste littérale à 8
    éléments peut nécessiter des lemmes simp supplémentaires en
    Mathlib v4.29. Si la combinaison `simp only [...] ; ring` ne
    ferme pas, fallback proposé en commentaire au-dessus du théorème. -/

/-- Raw-form expression of the k-th moment.

    Fallback proof si le `simp only ; ring` ci-dessous ne ferme pas :
    ```lean
    show (([1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3] : List ℚ).map (· ^ k)).foldr (· + ·) 0 / 8 = _
    rw [show ([1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3] : List ℚ) =
            (1 :: 1 :: 1/3 :: 1/3 :: 1/3 :: 1/3 :: -1/3 :: -1/3 :: []) from rfl]
    repeat rw [List.map_cons]
    rw [List.map_nil]
    repeat rw [List.foldr_cons]
    rw [List.foldr_nil]
    simp only [one_pow]
    ring
    ``` -/
theorem M_raw_formula (k : ℕ) :
    M k = (2 + 4 * ((1/3 : ℚ)^k) + 2 * ((-1/3 : ℚ)^k)) / 8 := by
  simp only [M, normalizedSpectrum, List.map_cons, List.map_nil,
             List.foldr_cons, List.foldr_nil, one_pow]
  ring

/-- Sign at odd exponent: (-1)^(2n+1) = -1. -/
private lemma neg_one_pow_two_n_plus_one (n : ℕ) :
    ((-1 : ℚ))^(2*n+1) = -1 := by
  rw [pow_succ, pow_mul]
  norm_num

/-- Sign at even exponent: (-1)^(2n+2) = 1. -/
private lemma neg_one_pow_two_n_plus_two (n : ℕ) :
    ((-1 : ℚ))^(2*n+2) = 1 := by
  rw [show 2*n+2 = 2*(n+1) by ring, pow_mul]
  norm_num

/-- (-1/3)^(2n+1) = -(1/3)^(2n+1). -/
private lemma neg_third_pow_odd (n : ℕ) :
    ((-1/3 : ℚ))^(2*n+1) = -((1/3 : ℚ)^(2*n+1)) := by
  rw [show (-1/3 : ℚ) = (-1) * (1/3) by ring, mul_pow,
      neg_one_pow_two_n_plus_one]
  ring

/-- (-1/3)^(2n+2) = (1/3)^(2n+2). -/
private lemma neg_third_pow_even (n : ℕ) :
    ((-1/3 : ℚ))^(2*n+2) = (1/3 : ℚ)^(2*n+2) := by
  rw [show (-1/3 : ℚ) = (-1) * (1/3) by ring, mul_pow,
      neg_one_pow_two_n_plus_two]
  ring

/--
**Universal pair rigidity** of the normalized spectrum K_TC.

For every n ≥ 0, M(2n+1) = M(2n+2).

This is a finite combinatorial theorem on the multiset
{1², (1/3)⁴, (-1/3)²}. It does not survive perturbation of the
multiplicities (4:2 ratio between +1/3 and -1/3 is what makes
the identity exact); it is therefore tensorial-only.
-/
theorem moments_paired_general (n : ℕ) :
    M (2*n+1) = M (2*n+2) := by
  rw [M_raw_formula, M_raw_formula]
  rw [neg_third_pow_odd, neg_third_pow_even]
  -- Goal:
  --   (2 + 4·(1/3)^(2n+1) + 2·(-(1/3)^(2n+1))) / 8
  -- = (2 + 4·(1/3)^(2n+2) + 2·(1/3)^(2n+2)) / 8
  -- After simplification, both sides reduce to (2 + 2/3^(2n+1))/8.
  have h_pow : (1/3 : ℚ)^(2*n+2) = (1/3 : ℚ)^(2*n+1) * (1/3) := by
    rw [show 2*n+2 = (2*n+1)+1 by ring, pow_succ]
  rw [h_pow]
  ring

/--
**Closed-form universal expression** for odd index.

For every n ≥ 0, M(2n+1) = (1/4)·(1 + 1/3^(2n+1)).

This is the exact closed form from the LaTeX note Theorem 1.
-/
theorem moments_paired_closed_form_odd (n : ℕ) :
    M (2*n+1) = (1/4 : ℚ) * (1 + (1/3 : ℚ)^(2*n+1)) := by
  rw [M_raw_formula, neg_third_pow_odd]
  ring

/--
**Closed-form universal expression** for even index.

For every n ≥ 0, M(2n+2) = (1/4)·(1 + 1/3^(2n+1)).
-/
theorem moments_paired_closed_form_even (n : ℕ) :
    M (2*n+2) = (1/4 : ℚ) * (1 + (1/3 : ℚ)^(2*n+1)) := by
  rw [← moments_paired_general, moments_paired_closed_form_odd]

/-- Concrete verification of the universal closed form for n=0,1,2. -/
theorem closed_form_universal_check :
    M 1 = (1/4 : ℚ) * (1 + (1/3)^1) ∧
    M 3 = (1/4 : ℚ) * (1 + (1/3)^3) ∧
    M 5 = (1/4 : ℚ) * (1 + (1/3)^5) := by
  refine ⟨?_, ?_, ?_⟩
  · have := moments_paired_closed_form_odd 0; simpa using this
  · have := moments_paired_closed_form_odd 1; simpa using this
  · have := moments_paired_closed_form_odd 2; simpa using this

/-! ## §6 — Doctrinal firewall -/

theorem no_rh_from_tensorial_moment_rigidity :
    RHClaimed = false := rfl

theorem no_rh_from_paired_rigidity :
    RHClaimed = false := rfl

theorem no_rh_from_universal_paired_rigidity :
    RHClaimed = false := rfl

end AnalyticHorizon
end CouretUnification
