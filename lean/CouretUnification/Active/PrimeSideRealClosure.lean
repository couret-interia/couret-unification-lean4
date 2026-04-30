/-
  CouretUnification/Active/PrimeSideRealClosure.lean

  Active-module : preuve MATHÉMATIQUE réelle que tout test à support compact
  (au sens Mathlib `HasCompactSupport`) induit une `LogCompactTest` du
  Frozen Core v36.0.

  Contenu :
    · `hasCompactSupport_bound`           — borne sur le support
    · `primeSide_vanishes_past_cutoff`    — fermeture finie du PrimeSide
    · `LogCompactTest.ofCompactSupport`   — pont constructif Active → Frozen

  Statut doctrinal
  ────────────────
  · Layer         : Active (dépend de Mathlib.Topology.Support)
  · indeterminateProofs : 0 (cible : à confirmer par `lake build` dans le dépôt)
  · axiomCount    : 0
  · RHClaimed     : false
  · ExplicitFormulaClaimedAsClosed : false

  Règle de sécurité : ce module N'EST PAS importé par le Frozen Core.
  Seul le chemin inverse est permis : Active importe Frozen.

  NOTE DE VÉRIFICATION
  ────────────────────
  La preuve utilise les API Mathlib suivantes (à confirmer au premier build) :
    · `HasCompactSupport.isBounded` (topologie du support)
    · `Bornology.IsBounded.subset_closedBall`
    · `image_eq_zero_of_nmem_tsupport` (ou équivalent)
    · `Real.log_lt_log`, `Real.exp_log`, `Nat.le_ceil`
  Si un de ces noms a dérivé entre versions Mathlib, l'ajustement est local
  et ne change pas la structure de la preuve.

  Pour Bernard.
-/

import Mathlib.Topology.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import CouretUnification.Logic.ExplicitFormula.PrimeSideCompactSupport

namespace CouretUnification.Active

open CouretUnification.Logic.ExplicitFormula

/-! ### Étape 1 — Support compact implique support borné -/

/--
Un support compact dans `ℝ` est borné : il existe `R ≥ 0` tel que `g` s'annule
dès que `|x| > R`. C'est l'énoncé fin dont on a besoin, formulé directement
en termes de la fonction `g` (et non de `tsupport g`).
-/
lemma hasCompactSupport_bound {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → g x = 0 := by
  -- Le tsupport de g est compact, donc borné dans ℝ.
  have hbound : Bornology.IsBounded (tsupport g) := hg.isBounded
  -- Extraire une boule fermée centrée en 0 contenant tsupport g.
  obtain ⟨R₀, hR₀⟩ := hbound.subset_closedBall 0
  -- Prendre R := max R₀ 0 pour assurer R ≥ 0.
  refine ⟨max R₀ 0, le_max_right _ _, ?_⟩
  intro x hx
  -- Si |x| > max R₀ 0 ≥ R₀, alors x ∉ closedBall 0 R₀ ⊇ tsupport g.
  have hx_nmem : x ∉ tsupport g := by
    intro hmem
    have hdist := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hdist
    -- hdist : |x| ≤ R₀ ; hx : max R₀ 0 < |x|.
    have h1 : R₀ ≤ max R₀ 0 := le_max_left _ _
    linarith
  -- x hors du tsupport ⟹ g x = 0.
  exact image_eq_zero_of_nmem_tsupport hx_nmem

/-! ### Étape 2 — Fermeture finie du PrimeSide -/

/--
Si `g` a un support compact, alors pour tout `n` entier strictement supérieur
à `⌈exp R⌉ + 1` (où `R` borne le support), on a `g(log n) = 0` ET
`g(−log n) = 0`.

C'est la **fermeture finie** du PrimeSide : après ce cutoff, chaque terme
premier `Λ(n)·(g(log n) + g(−log n))` est nul, quelle que soit la fonction
`Λ : ℕ → ℂ`.
-/
theorem primeSide_vanishes_past_cutoff {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      g (Real.log n) = 0 ∧ g (-Real.log n) = 0 := by
  -- Extraire la borne R du support.
  obtain ⟨R, hR_nn, hR_ann⟩ := hasCompactSupport_bound hg
  -- Cutoff entier : N := ⌈exp R⌉ + 1. On assure ainsi exp R < n dès que N < n.
  refine ⟨Nat.ceil (Real.exp R) + 1, fun n hn => ?_⟩
  -- Étape 2.a — Montrer exp R < n.
  have hexp_lt_n : Real.exp R < (n : ℝ) := by
    have h1 : Real.exp R ≤ (Nat.ceil (Real.exp R) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp R) + 1 : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    push_cast at h2
    linarith
  -- Étape 2.b — log n est bien défini et strictement supérieur à R.
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos R) hexp_lt_n.le
  have hlog_gt : R < Real.log n := by
    have h_expR : R = Real.log (Real.exp R) := (Real.log_exp R).symm
    rw [h_expR]
    exact Real.log_lt_log (Real.exp_pos R) hexp_lt_n
  -- Étape 2.c — |log n| > R et |−log n| > R.
  have hlog_pos : 0 < Real.log n := lt_of_le_of_lt hR_nn hlog_gt
  have habs_pos : R < |Real.log n| := by
    rw [abs_of_pos hlog_pos]; exact hlog_gt
  have habs_neg : R < |-Real.log n| := by
    rw [abs_neg]; exact habs_pos
  -- Étape 2.d — Conclure via l'annulation de g hors de {|x| ≤ R}.
  exact ⟨hR_ann _ habs_pos, hR_ann _ habs_neg⟩

/-! ### Étape 3 — Pont constructif vers le Frozen `LogCompactTest` -/

/--
Constructeur non-calculable (car dépend de `Classical.choice` via
`Exists.choose`) qui prend une fonction `g : ℝ → ℂ` à support compact
et produit une `LogCompactTest` du Frozen Core.

C'est le **pont** qui permet d'instancier le Frozen à partir du monde
analytique standard de Mathlib.
-/
noncomputable def LogCompactTest.ofCompactSupport
    (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    LogCompactTest where
  g := g
  cutoff := (primeSide_vanishes_past_cutoff hg).choose
  vanishes_after_cutoff :=
    (primeSide_vanishes_past_cutoff hg).choose_spec

/-- Vérification typographique : le pont préserve `g`. -/
@[simp] theorem LogCompactTest.ofCompactSupport_g
    (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    (LogCompactTest.ofCompactSupport g hg).g = g :=
  rfl

end CouretUnification.Active
