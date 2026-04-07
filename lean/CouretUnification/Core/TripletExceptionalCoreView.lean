import CouretUnification.Core.TripletExceptionalLocalPackage
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Vue noyau locale unifiée, pour un triplet arbitraire, des seules données
réellement utilisées par la candidature exceptionnelle locale :

- certificat harmonique ;
- spectre documentaire candidat ;
- profil quadratique harmonique ;
- recollement historique ;
- recollement quadratique ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletExceptionalCoreView (T : Triplet) where
  localPackage : TripletExceptionalLocalPackage T
  harmonic : HarmonicCertificate T
  candidate : FiniteSpectrum
  powerCoeffs : List ℝ
  powerCoeffs_len : powerCoeffs.length = 8
  harmonicRealizes :
    tripletFourier T = harmonic.coeffs
  historicalRecollement :
    matchesHistoricalSpectrum T candidate
  powerRealizes :
    powerCoeffs = tripletPowerSpectrum T
  powerHistoricalRecollement :
    powerCoeffs =
      candidate.powerHistorical.map (fun n => (n : ℝ))
  harmonicEntriesIntegral :
    certificateHasIntegralEntries harmonic
  finiteIntegral :
    hasIntegralSpectrum candidate
  rawIntegral :
    hasRawIntegralCriterion T

/--
Constructeur canonique :
à partir d’un paquet local déjà construit,
on extrait la vue noyau minimale effectivement utilisée.
-/
def canonicalTripletExceptionalCoreView
    (T : Triplet) (P : TripletExceptionalLocalPackage T) :
    TripletExceptionalCoreView T where
  localPackage := P
  harmonic :=
    P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic
  candidate :=
    P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate
  powerCoeffs :=
    P.localCandidate.quadraticIntegral.quadratic.powerCoeffs
  powerCoeffs_len :=
    P.localCandidate.quadraticIntegral.quadratic.powerCoeffs_len
  harmonicRealizes :=
    P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic.realizes
  historicalRecollement := P.matchesHistorical
  powerRealizes := P.realizesPower
  powerHistoricalRecollement := P.matchesHistoricalPower
  harmonicEntriesIntegral := P.harmonicIntegral
  finiteIntegral := P.documentaryIntegral
  rawIntegral := P.rawIntegral

/--
Cas Couret : vue noyau locale canonique de référence.
-/
def couretTripletExceptionalCoreView :
    TripletExceptionalCoreView couretTriplet :=
  canonicalTripletExceptionalCoreView
    couretTriplet
    couretTripletExceptionalLocalPackage

/--
La vue noyau canonique du cas Couret recolle bien
avec l’historique documentaire.
-/
theorem couretTripletExceptionalCoreView_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletExceptionalCoreView.candidate := by
  exact couretTripletExceptionalCoreView.historicalRecollement

/--
La vue noyau canonique du cas Couret réalise bien
le calcul harmonique canonique.
-/
theorem couretTripletExceptionalCoreView_harmonicRealizes :
    tripletFourier couretTriplet =
      couretTripletExceptionalCoreView.harmonic.coeffs := by
  exact couretTripletExceptionalCoreView.harmonicRealizes

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique ;
- réalisation quadratique harmonique ;
- recollement quadratique harmonique/documentaire ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique.
-/
theorem couretTripletExceptionalCoreView_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletExceptionalCoreView.candidate
      ∧ couretTripletExceptionalCoreView.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletExceptionalCoreView.powerCoeffs =
          couretTripletExceptionalCoreView.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletExceptionalCoreView.harmonic
      ∧ hasIntegralSpectrum
          couretTripletExceptionalCoreView.candidate
      ∧ hasRawIntegralCriterion couretTriplet := by
  exact ⟨ couretTripletExceptionalCoreView.historicalRecollement
        , couretTripletExceptionalCoreView.powerRealizes
        , couretTripletExceptionalCoreView.powerHistoricalRecollement
        , couretTripletExceptionalCoreView.harmonicEntriesIntegral
        , couretTripletExceptionalCoreView.finiteIntegral
        , couretTripletExceptionalCoreView.rawIntegral ⟩

end

end CouretUnification.Core