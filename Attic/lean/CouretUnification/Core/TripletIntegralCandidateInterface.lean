import CouretUnification.Core.TripletCandidateInterface
import CouretUnification.Core.TripletDocumentaryIntegralInterface
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Interface minimale de candidat intégral harmonico-quadratique
pour un triplet arbitraire :
- un candidat documentaire harmonico-quadratique,
- l'intégralité harmonique minimale des entrées du certificat,
- l'intégralité finie documentaire du candidat.

On ne filtre encore aucun triplet,
et on n'ouvre pas `ExceptionalFilter`.
-/
structure TripletIntegralCandidateInterface (T : Triplet) where
  candidate : TripletCandidateInterface T
  harmonicEntriesIntegral :
    certificateHasIntegralEntries candidate.documentary.harmonic
  candidateFiniteIntegral :
    hasIntegralSpectrum candidate.documentary.candidate

/--
Constructeur minimal :
on empaquette un candidat harmonico-quadratique déjà construit
avec ses deux témoins minimaux d'intégralité.
-/
def mkTripletIntegralCandidateInterface
    (T : Triplet)
    (C : TripletCandidateInterface T)
    (hH : certificateHasIntegralEntries C.documentary.harmonic)
    (hF : hasIntegralSpectrum C.documentary.candidate) :
    TripletIntegralCandidateInterface T where
  candidate := C
  harmonicEntriesIntegral := hH
  candidateFiniteIntegral := hF

/--
L'interface empaquetée conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletIntegralCandidateInterface.matchesHistorical
    {T : Triplet} (I : TripletIntegralCandidateInterface T) :
    matchesHistoricalSpectrum T I.candidate.documentary.candidate := by
  exact I.candidate.matchesHistorical

/--
L'interface empaquetée conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletIntegralCandidateInterface.matchesHistoricalPower
    {T : Triplet} (I : TripletIntegralCandidateInterface T) :
    tripletPowerSpectrum T =
      I.candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact I.candidate.matchesHistoricalPower

/--
L'interface empaquetée porte bien l'intégralité harmonique minimale
des entrées du certificat.
-/
theorem TripletIntegralCandidateInterface.harmonicIntegral
    {T : Triplet} (I : TripletIntegralCandidateInterface T) :
    certificateHasIntegralEntries I.candidate.documentary.harmonic := by
  exact I.harmonicEntriesIntegral

/--
L'interface empaquetée porte bien l'intégralité finie documentaire
du candidat.
-/
theorem TripletIntegralCandidateInterface.documentaryIntegral
    {T : Triplet} (I : TripletIntegralCandidateInterface T) :
    hasIntegralSpectrum I.candidate.documentary.candidate := by
  exact I.candidateFiniteIntegral

/--
Cas Couret : interface canonique intégrale harmonico-quadratique.
-/
def couretTripletIntegralCandidateInterface :
    TripletIntegralCandidateInterface couretTriplet :=
  mkTripletIntegralCandidateInterface
    couretTriplet
    couretTripletCandidateInterface
    couretCanonicalCertificate_hasIntegralEntries
    couretTriplet_hasIntegralSpectrum

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- recollement quadratique harmonique/documentaire,
- intégralité harmonique minimale,
- intégralité finie documentaire.
-/
theorem couretTripletIntegralCandidateInterface_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletIntegralCandidateInterface.candidate.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletIntegralCandidateInterface.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletIntegralCandidateInterface.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletIntegralCandidateInterface.candidate.documentary.candidate := by
  exact ⟨ couretTripletIntegralCandidateInterface.matchesHistorical
        , couretTripletIntegralCandidateInterface.matchesHistoricalPower
        , couretTripletIntegralCandidateInterface.harmonicIntegral
        , couretTripletIntegralCandidateInterface.documentaryIntegral ⟩

end

end CouretUnification.Core