-- =========================================================================
-- Couret-Unification / TowerLift v18
-- Module : Numerics/ScanSummary.lean
--
-- AUTO-GÉNÉRÉ depuis toymodel_scan_complete.json
-- Date : 2026-03-26 06:21:31
--
-- Version v38x corrigée :
--   - aucune axiomatisation numérique fausse ;
--   - les diagnostics vrais sont prouvés par `norm_num` ;
--   - les diagnostics faux sont explicitement réfutés.
-- =========================================================================

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum

namespace CouretUnification.Numerics

/-! Constantes issues du scan Python (N = 5,000,000, 30,657 SG). -/

/-- Valeur canonique λ = 1 / sqrt(7). -/
noncomputable def lambdaCanonical : Real := 1 / Real.sqrt 7

/-- Valeur propre positive de Δ̃_SG, la plus proche de λ dans le scan. -/
def sgDeltaPos : Real := 0.37517432

/-- Valeur propre dominante en module de Δ̃_SG. -/
def sgDeltaDom : Real := -0.39639813

/-- Erreur relative de δ̃_pos par rapport à λ, en pourcentage. -/
def sgRelErrorPosPercent : Real := 0.738205

/-- Moyenne empirique de μ(s) = Euler / δ̃_pos. -/
def toyMuPosMean : Real := -0.0492025133

/-- Écart-type de μ_pos(s). -/
def toyMuPosStd : Real := 0.0625610372

/-- Coefficient de variation de μ_pos(s). -/
def toyMuPosCV : Real := 1.2715008448

/-- Taille de l'échantillon SG actif. -/
def toySampleSize : Nat := 30654

/-- Grille : s ∈ [0.8, 5.0], 14 points. -/
def sMin : Real := 0.8
def sMax : Real := 5.0
def sGridCard : Nat := 14

/-! Propositions de diagnostic. -/

def NumericalWeakCouplingStable : Prop := toyMuPosCV < 0.10
def NumericalWeakCouplingVeryStable : Prop := toyMuPosCV < 0.05
def StrongSpectralProximity : Prop := sgRelErrorPosPercent < 1.0
def VeryStrongSpectralProximity : Prop := sgRelErrorPosPercent < 0.5

/-! Diagnostics prouvés depuis les constantes encodées. -/

/-- Le scan vérifie la proximité spectrale forte : 0.738205% < 1%. -/
theorem sgSpectralProximity : StrongSpectralProximity := by
  norm_num [StrongSpectralProximity, sgRelErrorPosPercent]

/-- Le scan ne vérifie pas la proximité très forte : 0.738205% n'est pas < 0.5%. -/
theorem not_veryStrongSpectralProximity : ¬ VeryStrongSpectralProximity := by
  norm_num [VeryStrongSpectralProximity, sgRelErrorPosPercent]

/-- Le couplage faible n'est pas stable au seuil 0.10 : CV = 1.2715... -/
theorem not_NumericalWeakCouplingStable : ¬ NumericalWeakCouplingStable := by
  norm_num [NumericalWeakCouplingStable, toyMuPosCV]

/-- Le couplage faible n'est pas très stable au seuil 0.05. -/
theorem not_NumericalWeakCouplingVeryStable : ¬ NumericalWeakCouplingVeryStable := by
  norm_num [NumericalWeakCouplingVeryStable, toyMuPosCV]

/-- Verdict honnête du scan : proximité spectrale forte, mais couplage faible non stable. -/
def ScanSummaryVerdict : Prop :=
  StrongSpectralProximity ∧ ¬ NumericalWeakCouplingStable

theorem scanSummary_verdict : ScanSummaryVerdict := by
  exact ⟨sgSpectralProximity, not_NumericalWeakCouplingStable⟩

end CouretUnification.Numerics