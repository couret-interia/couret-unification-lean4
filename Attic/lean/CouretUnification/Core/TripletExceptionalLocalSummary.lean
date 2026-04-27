import CouretUnification.Core.TripletExceptionalCoreView
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Résumé local minimal, pour un triplet arbitraire, du noyau effectivement
utilisé par la candidature exceptionnelle locale :

- un candidat documentaire historique ;
- un profil quadratique harmonique ;
- l’intégralité harmonique minimale ;
- l’intégralité finie documentaire ;
- le critère brut d’intégralité harmonique.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletExceptionalLocalSummary (T : Triplet) where
  coreView : TripletExceptionalCoreView T
  historical : matchesHistoricalSpectrum T coreView.candidate
  powerHistorical :
    coreView.powerCoeffs =
      coreView.candidate.powerHistorical.map (fun n => (n : ℝ))
  harmonicIntegral :
    certificateHasIntegralEntries coreView.harmonic
  finiteIntegral :
    hasIntegralSpectrum coreView.candidate
  rawIntegral :
    hasRawIntegralCriterion T

/--
Constructeur canonique :
à partir d’une vue noyau déjà construite,
on en extrait le résumé local minimal.
-/
def canonicalTripletExceptionalLocalSummary
    (T : Triplet) (V : TripletExceptionalCoreView T) :
    TripletExceptionalLocalSummary T where
  coreView := V
  historical := V.historicalRecollement
  powerHistorical := V.powerHistoricalRecollement
  harmonicIntegral := V.harmonicEntriesIntegral
  finiteIntegral := V.finiteIntegral
  rawIntegral := V.rawIntegral

/--
Cas Couret : résumé local canonique.
-/
def couretTripletExceptionalLocalSummary :
    TripletExceptionalLocalSummary couretTriplet :=
  canonicalTripletExceptionalLocalSummary
    couretTriplet
    couretTripletExceptionalCoreView

/--
Le résumé local canonique du cas Couret recolle bien
avec l’historique documentaire.
-/
theorem couretTripletExceptionalLocalSummary_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletExceptionalLocalSummary.coreView.candidate := by
  exact couretTripletExceptionalLocalSummary.historical

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique ;
- recollement quadratique harmonique/documentaire ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique.
-/
theorem couretTripletExceptionalLocalSummary_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletExceptionalLocalSummary.coreView.candidate
      ∧ couretTripletExceptionalLocalSummary.coreView.powerCoeffs =
          couretTripletExceptionalLocalSummary.coreView.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletExceptionalLocalSummary.coreView.harmonic
      ∧ hasIntegralSpectrum
          couretTripletExceptionalLocalSummary.coreView.candidate
      ∧ hasRawIntegralCriterion couretTriplet := by
  exact ⟨ couretTripletExceptionalLocalSummary.historical
        , couretTripletExceptionalLocalSummary.powerHistorical
        , couretTripletExceptionalLocalSummary.harmonicIntegral
        , couretTripletExceptionalLocalSummary.finiteIntegral
        , couretTripletExceptionalLocalSummary.rawIntegral ⟩

end

end CouretUnification.Core