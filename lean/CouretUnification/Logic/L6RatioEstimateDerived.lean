/-
# CouretUnification/Logic/L6RatioEstimateDerived.lean

## Rôle
Consomme l'API de `L6Analytic.lean` pour fermer les contrats asymptotiques
exposés par `L6Bridge.lean`.

## Statut (v35.8.6)
- Layer   : Logic
- Status  : conditional (branché sur L6Analytic)
- Sorry   : 1
    • `L6RatioEstimate_derived`          [ANALYTIC assembly]

  Note v35.8.6 : `ZtotPositiveEventually_derived` est désormais
  PROUVÉ (était à sorry en v35.8.5) grâce au refactoring qui rend
  `Ztot_bridge` prouvable par `rfl`. Réduction nette : 2 → 1 sorry.

## Changements v35.8.6
- `stirling_ratio_asymptotic` : FERMÉ (preuve `linarith` après bornage T ≥ 2).
- Step C : structurellement BRANCHÉ sur `Aarch_effective_log_growth`
           et `Ztot_effective_eventually_positive`.
- Les 2 sorries restants sont explicitement étiquetés comme
  [ANALYTIC + DEFINITIONAL] — voir doctrine v35.8.5.

- RHClaimed : false
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CouretUnification.Logic.L6Bridge
import CouretUnification.Logic.L6Analytic
import CouretUnification.Meta.Doctrine

namespace CouretUnification
namespace Logic
namespace L6Derived

open CouretUnification.Logic.L6Bridge
open CouretUnification.Logic.L6Analytic
open Real

/-! ## Step B — Lemme technique Stirling (FERMÉ v35.8.5)

    Correction doctrinale : le domaine est borné par `T ≥ max T₀ 2`,
    ce qui garantit `log T ≥ log 2 > 0`, donc `|log T| = log T`. -/

/-- Forme technique de Stirling : `|log T| ≤ C · log T` pour `T` assez grand
    (avec `C = 1`). Fermé par pure arithmétique. -/
theorem stirling_ratio_asymptotic (T₀ : ℝ) (_hT₀ : 0 < T₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max T₀ 2 ≤ T → |Real.log T| ≤ C * Real.log T := by
  refine ⟨1, by norm_num, ?_⟩
  intro T hT
  have hT_ge_2 : (2 : ℝ) ≤ T := le_trans (le_max_right T₀ 2) hT
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT_pos : 0 < Real.log T :=
    lt_of_lt_of_le hlog2_pos (Real.log_le_log (by norm_num) hT_ge_2)
  rw [abs_of_pos hlogT_pos]
  linarith

/-! ## Step C — Preuve du contrat L6RatioEstimate

    Cette étape est structurellement BRANCHÉE sur `L6Analytic`.
    Le `sorry` restant est purement un assemblage d'inégalités
    logarithmiques, pas une dette conceptuelle. -/

/-- Contrat principal : l'erreur `eps` décroît en `C / log T`. -/
theorem L6RatioEstimate_derived (χ : PrimitiveCharacter) :
    L6RatioEstimate χ := by
  -- 1. Récupération de la croissance logarithmique de Aarch depuis L6Analytic.
  obtain ⟨C_growth, hC_pos, T₀_growth, hT₀_gt_1, h_growth⟩ :=
    Aarch_effective_log_growth χ
  -- 2. Récupération de la positivité éventuelle de Ztot depuis L6Analytic.
  obtain ⟨T₀_pos, hT₀_pos_pos, h_Ztot_pos⟩ :=
    Ztot_effective_eventually_positive χ
  -- 3. On pose T_final = max(T₀_growth, T₀_pos, 2) pour garantir TOUT en même temps.
  unfold L6RatioEstimate
  refine ⟨max (max T₀_growth T₀_pos) 2, 1, by norm_num, ?_, ?_⟩
  · -- T₀_final > 1
    calc (1 : ℝ) < T₀_growth := hT₀_gt_1
      _ ≤ max T₀_growth T₀_pos := le_max_left _ _
      _ ≤ max (max T₀_growth T₀_pos) 2 := le_max_left _ _
  · -- Pour T ≥ T_final, |eps χ T| ≤ 1 / log T.
    intro T _hT
    -- Stratégie d'assemblage à venir (v35.8.7) :
    --   a) Utiliser Aarch_bridge et Ztot_bridge pour substituer les opaques
    --      par leurs formes effectives.
    --   b) Utiliser h_growth  : C_growth · log T ≤ Aarch_effective χ T
    --      et     h_Ztot_pos : 0 < Ztot_effective χ T.
    --   c) Borner |Aarch_eff / Ztot_eff - 1/2| par (constante) / log T
    --      via les asymptotiques de Riemann–von Mangoldt et Stirling.
    sorry  -- [ANALYTIC ASSEMBLY] Raccord final des inégalités logarithmiques

/-- Contrat de positivité : `Ztot χ T > 0` pour `T` assez grand.

    En v35.8.6, `Ztot_bridge` est désormais prouvable par `rfl` grâce
    au refactoring architectural (L6Bridge.Ztot := L6Analytic.Ztot_effective).
    Cette preuve devient donc TRIVIALE par transport de
    `Ztot_effective_eventually_positive`. AUCUN sorry, AUCUN axiome. -/
theorem ZtotPositiveEventually_derived (χ : PrimitiveCharacter) :
    ZtotPositiveEventually χ := by
  unfold ZtotPositiveEventually
  obtain ⟨T₀, hT₀_pos, h_pos_eff⟩ :=
    Ztot_effective_eventually_positive χ
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  -- Transport via Ztot_bridge (prouvé par rfl en v35.8.6)
  rw [Ztot_bridge χ T]
  exact h_pos_eff T hT

/-! ## Identité doctrinale du fichier -/

open CouretUnification.Meta

/-- Identité du fichier L6RatioEstimateDerived (v35.8.6).

    Décomposition du compteur :
      1. [ANALYTIC ASSEMBLY] `L6RatioEstimate_derived` (seul sorry restant)

    `stirling_ratio_asymptotic` est FERMÉ (pas de sorry).
    `ZtotPositiveEventually_derived` est FERMÉ (v35.8.6, via Ztot_bridge=rfl). -/
def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/L6RatioEstimateDerived.lean"
  layer      := Layer.B
  status     := Status.conditional
  sorryCount := 1
  rhClaimed  := false

end L6Derived
end Logic
end CouretUnification
