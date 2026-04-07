import CouretUnification.Core.TripletDocumentaryIntegralInterface
import CouretUnification.Core.TripletDocumentaryPowerInterface
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet minimal pour un triplet arbitraire :
- un certificat documentaire candidat,
- l'intégralité harmonique minimale de ses entrées,
- l'intégralité finie documentaire de son candidat,
- le recollement quadratique harmonique/documentaire.

On ne filtre encore aucun triplet,
et on n'ouvre pas `ExceptionalFilter`.
-/
structure TripletDocumentaryIntegralPowerPackage (T : Triplet) where
  documentary : TripletDocumentaryCertificate T
  harmonicEntriesIntegral :
    certificateHasIntegralEntries documentary.harmonic
  candidateFiniteIntegral :
    hasIntegralSpectrum documentary.candidate
  powerHistoricalRecollement :
    tripletPowerSpectrum T =
      documentary.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Constructeur minimal :
on empaquette un certificat documentaire déjà construit
avec ses témoins minimaux d'intégralité et de recollement quadratique.
-/
def mkTripletDocumentaryIntegralPowerPackage
    (T : Triplet)
    (D : TripletDocumentaryCertificate T)
    (hH : certificateHasIntegralEntries D.harmonic)
    (hF : hasIntegralSpectrum D.candidate)
    (hP :
      tripletPowerSpectrum T =
        D.candidate.powerHistorical.map (fun n => (n : ℝ))) :
    TripletDocumentaryIntegralPowerPackage T where
  documentary := D
  harmonicEntriesIntegral := hH
  candidateFiniteIntegral := hF
  powerHistoricalRecollement := hP

/--
Le paquet conserve bien le recollement historique harmonique/documentaire.
-/
theorem TripletDocumentaryIntegralPowerPackage.matchesHistorical
    {T : Triplet} (P : TripletDocumentaryIntegralPowerPackage T) :
    matchesHistoricalSpectrum T P.documentary.candidate := by
  exact P.documentary.matchesHistorical

/-- Le paquet porte bien l'intégralité harmonique des entrées du certificat. -/
theorem TripletDocumentaryIntegralPowerPackage.harmonicIntegral
    {T : Triplet} (P : TripletDocumentaryIntegralPowerPackage T) :
    certificateHasIntegralEntries P.documentary.harmonic := by
  exact P.harmonicEntriesIntegral

/-- Le paquet porte bien l'intégralité finie du candidat documentaire. -/
theorem TripletDocumentaryIntegralPowerPackage.documentaryIntegral
    {T : Triplet} (P : TripletDocumentaryIntegralPowerPackage T) :
    hasIntegralSpectrum P.documentary.candidate := by
  exact P.candidateFiniteIntegral

/-- Le paquet porte bien le recollement quadratique harmonique/documentaire. -/
theorem TripletDocumentaryIntegralPowerPackage.powerMatchesHistorical
    {T : Triplet} (P : TripletDocumentaryIntegralPowerPackage T) :
    tripletPowerSpectrum T =
      P.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact P.powerHistoricalRecollement

/--
Cas Couret : paquet canonique minimal harmonique/documentaire/intégral/quadratique.
-/
def couretTripletDocumentaryIntegralPowerPackage :
    TripletDocumentaryIntegralPowerPackage couretTriplet :=
  mkTripletDocumentaryIntegralPowerPackage
    couretTriplet
    couretTripletDocumentaryCertificate
    couretCanonicalCertificate_hasIntegralEntries
    couretTriplet_hasIntegralSpectrum
    couretTriplet_power_reconstructs_finiteSpectrum

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- intégralité harmonique,
- intégralité finie documentaire,
- recollement quadratique harmonique/documentaire.
-/
theorem couretTripletDocumentaryIntegralPowerPackage_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletDocumentaryIntegralPowerPackage.documentary.candidate
      ∧ certificateHasIntegralEntries
          couretTripletDocumentaryIntegralPowerPackage.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletDocumentaryIntegralPowerPackage.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletDocumentaryIntegralPowerPackage.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ)) := by
  exact ⟨ couretTripletDocumentaryIntegralPowerPackage.matchesHistorical
        , couretTripletDocumentaryIntegralPowerPackage.harmonicIntegral
        , couretTripletDocumentaryIntegralPowerPackage.documentaryIntegral
        , couretTripletDocumentaryIntegralPowerPackage.powerMatchesHistorical ⟩

end

end CouretUnification.Core