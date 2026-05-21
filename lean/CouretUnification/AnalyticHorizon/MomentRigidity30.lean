/-
  CouretUnification.AnalyticHorizon.MomentRigidity30
  ════════════════════════════════════════════════════════════════════
  Rétrogradation doctrinale ET enrichissement structurel.

  RÉTROGRADATION :
    L'identité M₃ = M₄ = 7/27 est conservée comme invariant
    TENSORIAL-ONLY, et non comme rigidité structurelle profonde.

    Le crash-test de Legendre (q = 210, ε = 0.5) brise la signature
    normalisée

        {1, 1/3, -1/3}

    en

        {1, ±1/2, ±1/3, ±1/6}.

  ENRICHISSEMENT v38.1 :
    • conserve les théorèmes calculatoires k = 1..6, fermés par
      `native_decide` ;
    • ajoute le théorème universel M(2n+1) = M(2n+2) pour tout n,
      avec preuve algébrique, conformément à la note LaTeX
      « Une rigidité par paires des moments spectraux » ;
    • la rigidité par paires est un fait COMBINATOIRE FINI sur le spectre

          {1², (1/3)⁴, (-1/3)²}.

      Elle ne survit pas en général à toute perturbation — c'est précisément
      pourquoi elle reste tensorial-only.

  Doctrine :
    v38.1 enrichi.

  Statut :
    tensorial-only globalement ;
    calculs scalaires fermés ;
    rigidité combinatoire universelle prouvée.

  Sorries :
    0 nouveau.
-/

import Mathlib.Tactic.Ring
import CouretUnification.AnalyticHorizon.TraceFormulaTargets
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants

open CouretUnification.EpistemicDiscipline

namespace CouretUnification.AnalyticHorizon

/-! ## §1 — Énumération de statut -/

inductive RigidityStatus where
  | closedFinite
  | tensorialOnly
  | theoremTarget
deriving Repr, DecidableEq

/-! ## §2 — Rétrogradation doctrinale -/

/-- L'identité M₃ = M₄ = 7/27 est conservée uniquement comme invariant
    du régime tensoriel. Elle ne doit pas être utilisée comme pont global
    de Lock 3. -/
def MomentRigidity30Status : RigidityStatus := RigidityStatus.tensorialOnly

def MomentRigidity30Value : ℚ := 7 / 27

theorem moment_rigidity_30_is_tensorial_only :
    MomentRigidity30Status = RigidityStatus.tensorialOnly := rfl

theorem moment_rigidity_30_value :
    MomentRigidity30Value = 7 / 27 := rfl

/-! ## §3 — Spectre actif normalisé — témoins scalaires fermés

    Spectre : {1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3}
              avec multiplicités 2, 4, 2.

    M_k := (1/8) Σ λ_i^k                                                   -/

/-- Le spectre actif normalisé sous forme de liste — longueur 8. -/
def normalizedSpectrum : List ℚ :=
  [1, 1, 1/3, 1/3, 1/3, 1/3, -1/3, -1/3]

theorem normalizedSpectrum_length : normalizedSpectrum.length = 8 := by decide

/-- k-ième moment du spectre actif normalisé. -/
def M (k : ℕ) : ℚ :=
  (normalizedSpectrum.map (fun x => x^k)).foldr (· + ·) 0 / 8

/-! ### Valeurs fermées des moments — k = 1..6, témoins concrets par `native_decide` -/

theorem CM1_eq : M 1 = 1 / 3   := by native_decide
theorem CM2_eq : M 2 = 1 / 3   := by native_decide
theorem CM3_eq : M 3 = 7 / 27  := by native_decide
theorem CM4_eq : M 4 = 7 / 27  := by native_decide
theorem CM5_eq : M 5 = 61 / 243 := by native_decide
theorem CM6_eq : M 6 = 61 / 243 := by native_decide

/-! ### Rigidité par paires aux ordres concrets -/

/-- Rigidité par paires à l'ordre 1 : M_1 = M_2. -/
theorem moments_paired_k1 : M 1 = M 2 := by
  rw [CM1_eq, CM2_eq]

/-- Rigidité par paires à l'ordre 2 : M_3 = M_4. -/
theorem moments_paired_k2 : M 3 = M 4 := by
  rw [CM3_eq, CM4_eq]

/-- Rigidité par paires à l'ordre 3 : M_5 = M_6. -/
theorem moments_paired_k3 : M 5 = M 6 := by
  rw [CM5_eq, CM6_eq]

/-- Conjonction des trois premières rigidités par paires. -/
theorem moments_paired_first_three :
    M 1 = M 2 ∧ M 3 = M 4 ∧ M 5 = M 6 :=
  ⟨moments_paired_k1, moments_paired_k2, moments_paired_k3⟩

/-! ## §4 — Forme fermée : M_{2k-1} = M_{2k} = (9^k + 3) / (4·9^k), k=1..3 -/

theorem closed_form_k1 : M 2 = (9^1 + 3) / (4 * 9^1) := by native_decide
theorem closed_form_k2 : M 4 = (9^2 + 3) / (4 * 9^2) := by native_decide
theorem closed_form_k3 : M 6 = (9^3 + 3) / (4 * 9^3) := by native_decide

/-! ## §5 — Rigidité universelle par paires : ∀n, M(2n+1) = M(2n+2)

    C'est le théorème véritable issu de la note LaTeX
    « Une rigidité par paires des moments spectraux ».

    Stratégie :
      (a) exprimer M k sous forme brute :
            (2 + 4·(1/3)^k + 2·(-1/3)^k) / 8 ;
      (b) traiter la parité de k = 2n+1 et k = 2n+2 via
            (-1)^(2n+1) = -1
        et
            (-1)^(2n+2) = 1 ;
      (c) réduire à l'identité élémentaire

            4/3^{2n+1} - 2/3^{2n+1}
          =
            4/3^{2n+2} + 2/3^{2n+2},

        qui se simplifie en 2 = 6/3, c'est-à-dire l'asymétrie de
        multiplicité 4:2 entre +1/3 et -1/3. -/

/-- Expression brute du k-ième moment.

    Preuve de repli si le `simp only ; ring` ci-dessous ne ferme pas :
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

/-- Signe à exposant impair : (-1)^(2n+1) = -1. -/
private lemma neg_one_pow_two_n_plus_one (n : ℕ) :
    ((-1 : ℚ))^(2*n+1) = -1 := by
  rw [pow_succ, pow_mul]
  norm_num

/-- Signe à exposant pair : (-1)^(2n+2) = 1. -/
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
**Rigidité universelle par paires** du spectre normalisé K_TC.

Pour tout n ≥ 0, M(2n+1) = M(2n+2).

C'est un théorème combinatoire fini sur le multiensemble

    {1², (1/3)⁴, (-1/3)²}.

Il ne survit pas à une perturbation des multiplicités : le rapport 4:2 entre
+1/3 et -1/3 est précisément ce qui rend l'identité exacte. Il est donc
tensorial-only.
-/
theorem moments_paired_general (n : ℕ) :
    M (2*n+1) = M (2*n+2) := by
  rw [M_raw_formula, M_raw_formula]
  rw [neg_third_pow_odd, neg_third_pow_even]
  -- Objectif :
  --   (2 + 4·(1/3)^(2n+1) + 2·(-(1/3)^(2n+1))) / 8
  -- = (2 + 4·(1/3)^(2n+2) + 2·(1/3)^(2n+2)) / 8
  -- Après simplification, les deux côtés se réduisent à
  --   (2 + 2/3^(2n+1)) / 8.
  have h_pow : (1/3 : ℚ)^(2*n+2) = (1/3 : ℚ)^(2*n+1) * (1/3) := by
    rw [show 2*n+2 = (2*n+1)+1 by ring, pow_succ]
  rw [h_pow]
  ring

/--
**Expression fermée universelle** pour l'indice impair.

Pour tout n ≥ 0,

    M(2n+1) = (1/4)·(1 + 1/3^(2n+1)).

C'est la forme fermée exacte de la note LaTeX, Théorème 1.
-/
theorem moments_paired_closed_form_odd (n : ℕ) :
    M (2*n+1) = (1/4 : ℚ) * (1 + (1/3 : ℚ)^(2*n+1)) := by
  rw [M_raw_formula, neg_third_pow_odd]
  ring

/--
**Expression fermée universelle** pour l'indice pair.

Pour tout n ≥ 0,

    M(2n+2) = (1/4)·(1 + 1/3^(2n+1)).
-/
theorem moments_paired_closed_form_even (n : ℕ) :
    M (2*n+2) = (1/4 : ℚ) * (1 + (1/3 : ℚ)^(2*n+1)) := by
  rw [← moments_paired_general, moments_paired_closed_form_odd]

/-- Vérification concrète de la forme fermée universelle pour n = 0, 1, 2. -/
theorem closed_form_universal_check :
    M 1 = (1/4 : ℚ) * (1 + (1/3)^1) ∧
    M 3 = (1/4 : ℚ) * (1 + (1/3)^3) ∧
    M 5 = (1/4 : ℚ) * (1 + (1/3)^5) := by
  refine ⟨?_, ?_, ?_⟩
  · have := moments_paired_closed_form_odd 0; simpa using this
  · have := moments_paired_closed_form_odd 1; simpa using this
  · have := moments_paired_closed_form_odd 2; simpa using this

/-! ## §6 — Pare-feu doctrinal -/

theorem no_rh_from_tensorial_moment_rigidity :
    RHClaimed = false := rfl

theorem no_rh_from_paired_rigidity :
    RHClaimed = false := rfl

theorem no_rh_from_universal_paired_rigidity :
    RHClaimed = false := rfl

end CouretUnification.AnalyticHorizon
