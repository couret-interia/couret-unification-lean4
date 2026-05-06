/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/PrimeSide.lean

  Objet : PREMIÈRE FERMETURE MATHÉMATIQUE du programme.

         supp(g) ⊂ [-A, A]  ⇒  ∃ N, ∀ n > N, primeTerm(n) = 0.

         Compression géométrique : l'infini arithmétique est ramené
         au fini par le support compact. Aucune propriété de
         vonMangoldt n'est invoquée — le théorème vaut pour TOUT
         ArithmeticWeight.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local)
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Pour Bernard.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import CouretUnification.Logic.ExplicitFormula.TestPair
import CouretUnification.Logic.ExplicitFormula.ArithmeticWeight

namespace CouretUnification.Logic.ExplicitFormula

/-- Terme arithmétique d'indice n. -/
noncomputable def primeTerm
    (Λ : ArithmeticWeight) (φ : TestPair) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ) *
    (φ.g (Real.log (n : ℝ)) + φ.g (-Real.log (n : ℝ)))

/-- Annulation pointwise : si log n dépasse le rayon A du support, alors primeTerm(n) = 0. -/
theorem primeTerm_zero_of_log_gt_support
    (Λ : ArithmeticWeight)
    (φ : TestPair)
    (A : ℝ)
    (hApos : 0 < A)
    (hSupp : ∀ x : ℝ, A < |x| → φ.g x = 0)
    (n : ℕ)
    (hlog : A < Real.log (n : ℝ)) :
    primeTerm Λ φ n = 0 := by
  have hlog_pos : 0 < Real.log (n : ℝ) := lt_trans hApos hlog
  have h_abs_log : A < |Real.log (n : ℝ)| := by
    rw [abs_of_nonneg (le_of_lt hlog_pos)]; exact hlog
  have h_abs_neg_log : A < |-(Real.log (n : ℝ))| := by
    rw [abs_neg, abs_of_nonneg (le_of_lt hlog_pos)]; exact hlog
  have h1 : φ.g (Real.log (n : ℝ)) = 0 :=
    hSupp (Real.log (n : ℝ)) h_abs_log
  have h2 : φ.g (-(Real.log (n : ℝ))) = 0 :=
    hSupp (-(Real.log (n : ℝ))) h_abs_neg_log
  simp [primeTerm, h1, h2]

/-- THÉORÈME CENTRAL : sous support compact, PrimeSide est fini.
    Seuil N choisi via `exists_nat_gt (Real.exp A)` (robuste). -/
theorem primeSide_finite_of_compactSupport
    (Λ : ArithmeticWeight)
    (φ : TestPair) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → primeTerm Λ φ n = 0 := by
  rcases φ.compactSupport_g with ⟨A, hApos, hSupp⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp A)
  refine ⟨N, ?_⟩
  intro n hn
  have hn_real : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp_lt_n : Real.exp A < (n : ℝ) := lt_trans hN hn_real
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos A) hexp_lt_n
  have hlog : A < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hn_pos).2 hexp_lt_n
  exact primeTerm_zero_of_log_gt_support Λ φ A hApos hSupp n hlog

/-- Certificat de finitude du support. -/
structure PrimeSideFiniteSupport
    (Λ : ArithmeticWeight) (φ : TestPair) where
  cutoff         : ℕ
  vanishesBeyond : ∀ n : ℕ, cutoff < n → primeTerm Λ φ n = 0

/-- Construction canonique du certificat. -/
noncomputable def buildPrimeSideFiniteSupport
    (Λ : ArithmeticWeight) (φ : TestPair) :
    PrimeSideFiniteSupport Λ φ :=
  { cutoff := (primeSide_finite_of_compactSupport Λ φ).choose,
    vanishesBeyond := (primeSide_finite_of_compactSupport Λ φ).choose_spec }

/-- Évaluation finie de PrimeSide à partir d'un seuil. -/
noncomputable def evalPrimeSideFinite
    (Λ : ArithmeticWeight) (φ : TestPair) (N : ℕ) : ℂ :=
  (Finset.range (N + 1)).sum fun n => primeTerm Λ φ n

end CouretUnification.Logic.ExplicitFormula
