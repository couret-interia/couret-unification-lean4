import CouretUnification.Core.TripletQuadraticCandidateCertificate
import CouretUnification.Core.IntegralSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Interface minimale de candidat quadratique intégral pour un triplet arbitraire :
- un certificat candidat purement quadratique,
- l'intégralité harmonique minimale des entrées du certificat harmonique sous-jacent,
- l'intégralité finie documentaire du candidat sous-jacent.

On ne filtre encore aucun triplet,
et on n'ouvre pas `ExceptionalFilter`.
-/
structure TripletQuadraticIntegralCandidateInterface (T : Triplet) where
  quadratic : TripletQuadraticCandidateCertificate T
  harmonicEntriesIntegral :
    certificateHasIntegralEntries quadratic.candidate.documentary.harmonic
  candidateFiniteIntegral :
    hasIntegralSpectrum quadratic.candidate.documentary.candidate

/--
Constructeur minimal :
on empaquette un certificat quadratique déjà construit
avec ses deux témoins minimaux d'intégralité.
-/
def mkTripletQuadraticIntegralCandidateInterface
    (T : Triplet)
    (Q : TripletQuadraticCandidateCertificate T)
    (hH : certificateHasIntegralEntries Q.candidate.documentary.harmonic)
    (hF : hasIntegralSpectrum Q.candidate.documentary.candidate) :
    TripletQuadraticIntegralCandidateInterface T where
  quadratic := Q
  harmonicEntriesIntegral := hH
  candidateFiniteIntegral := hF

/--
L'interface empaquetée conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletQuadraticIntegralCandidateInterface.matchesHistorical
    {T : Triplet} (I : TripletQuadraticIntegralCandidateInterface T) :
    matchesHistoricalSpectrum T I.quadratic.candidate.documentary.candidate := by
  exact I.quadratic.matchesHistorical

/--
L'interface empaquetée conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletQuadraticIntegralCandidateInterface.matchesHistoricalPower
    {T : Triplet} (I : TripletQuadraticIntegralCandidateInterface T) :
    I.quadratic.powerCoeffs =
      I.quadratic.candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact I.quadratic.matchesHistoricalPower

/--
L'interface empaquetée réalise bien le calcul quadratique harmonique.
-/
theorem TripletQuadraticIntegralCandidateInterface.realizesPower
    {T : Triplet} (I : TripletQuadraticIntegralCandidateInterface T) :
    I.quadratic.powerCoeffs = tripletPowerSpectrum T := by
  exact I.quadratic.realizesPower

/--
L'interface empaquetée porte bien l'intégralité harmonique minimale
des entrées du certificat.
-/
theorem TripletQuadraticIntegralCandidateInterface.harmonicIntegral
    {T : Triplet} (I : TripletQuadraticIntegralCandidateInterface T) :
    certificateHasIntegralEntries I.quadratic.candidate.documentary.harmonic := by
  exact I.harmonicEntriesIntegral

/--
L'interface empaquetée porte bien l'intégralité finie documentaire
du candidat.
-/
theorem TripletQuadraticIntegralCandidateInterface.documentaryIntegral
    {T : Triplet} (I : TripletQuadraticIntegralCandidateInterface T) :
    hasIntegralSpectrum I.quadratic.candidate.documentary.candidate := by
  exact I.candidateFiniteIntegral

/--
Cas Couret : interface canonique quadratique intégrale.
-/
def couretTripletQuadraticIntegralCandidateInterface :
    TripletQuadraticIntegralCandidateInterface couretTriplet :=
  mkTripletQuadraticIntegralCandidateInterface
    couretTriplet
    couretTripletQuadraticCandidateCertificate
    couretCanonicalCertificate_hasIntegralEntries
    couretTriplet_hasIntegralSpectrum

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- réalisation quadratique harmonique,
- recollement quadratique harmonique/documentaire,
- intégralité harmonique minimale,
- intégralité finie documentaire.
-/
theorem couretTripletQuadraticIntegralCandidateInterface_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletQuadraticIntegralCandidateInterface.quadratic.candidate.documentary.candidate
      ∧ couretTripletQuadraticIntegralCandidateInterface.quadratic.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletQuadraticIntegralCandidateInterface.quadratic.powerCoeffs =
          couretTripletQuadraticIntegralCandidateInterface.quadratic.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletQuadraticIntegralCandidateInterface.quadratic.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletQuadraticIntegralCandidateInterface.quadratic.candidate.documentary.candidate := by
  exact ⟨ couretTripletQuadraticIntegralCandidateInterface.matchesHistorical
        , couretTripletQuadraticIntegralCandidateInterface.realizesPower
        , couretTripletQuadraticIntegralCandidateInterface.matchesHistoricalPower
        , couretTripletQuadraticIntegralCandidateInterface.harmonicIntegral
        , couretTripletQuadraticIntegralCandidateInterface.documentaryIntegral ⟩

end

end CouretUnification.Core