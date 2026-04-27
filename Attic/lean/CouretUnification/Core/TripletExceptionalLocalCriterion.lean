import CouretUnification.Core.TripletExceptionalLocalSummary
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Critère local minimal synthétique, pour un triplet arbitraire, dérivé du résumé
noyau effectivement utilisé par la candidature exceptionnelle locale :

- recollement harmonique/documentaire historique ;
- recollement quadratique harmonique/documentaire ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
def satisfiesExceptionalLocalCriterion (T : Triplet) : Prop :=
  ∃ S : TripletExceptionalLocalSummary T,
      matchesHistoricalSpectrum T S.coreView.candidate
    ∧ S.coreView.powerCoeffs =
        S.coreView.candidate.powerHistorical.map (fun n => (n : ℝ))
    ∧ certificateHasIntegralEntries S.coreView.harmonic
    ∧ hasIntegralSpectrum S.coreView.candidate
    ∧ hasRawIntegralCriterion T

/--
Tout résumé local minimal fournit immédiatement le critère local synthétique.
-/
theorem TripletExceptionalLocalSummary.satisfiesCriterion
    {T : Triplet} (S : TripletExceptionalLocalSummary T) :
    satisfiesExceptionalLocalCriterion T := by
  exact ⟨ S
        , S.historical
        , S.powerHistorical
        , S.harmonicIntegral
        , S.finiteIntegral
        , S.rawIntegral ⟩

/--
Élimination minimale : le critère local synthétique fournit bien
un résumé local empaqueté.
-/
theorem satisfiesExceptionalLocalCriterion_hasSummary
    {T : Triplet} (h : satisfiesExceptionalLocalCriterion T) :
    Nonempty (TripletExceptionalLocalSummary T) := by
  rcases h with ⟨S, _, _, _, _, _⟩
  exact ⟨S⟩

/--
Cas Couret : critère local synthétique canonique.
-/
def couretTripletExceptionalLocalCriterion : Prop :=
  satisfiesExceptionalLocalCriterion couretTriplet

/--
Dans le cas Couret, le critère local synthétique est bien satisfait.
-/
theorem couretTripletExceptionalLocalCriterion_true :
    couretTripletExceptionalLocalCriterion := by
  exact couretTripletExceptionalLocalSummary.satisfiesCriterion

/--
Validation groupée minimale du cas Couret au niveau du critère local synthétique.
-/
theorem couretTripletExceptionalLocalCriterion_valid :
    satisfiesExceptionalLocalCriterion couretTriplet := by
  exact couretTripletExceptionalLocalCriterion_true

end

end CouretUnification.Core