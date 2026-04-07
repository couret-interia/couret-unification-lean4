import CouretUnification.Core.TripletQuadraticIntegralCandidateInterface
import CouretUnification.Core.TripletRawQuadraticConsistency
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Candidat exceptionnel local, pour un triplet arbitraire :

- une interface quadratique intégrale candidate ;
- une cohérence raw/quadratique ;
- une compatibilité minimale assurant que les deux couches
  portent bien sur le même candidat documentaire.

On n’ouvre encore :
- aucun filtrage global,
- aucune classification des 21 triplets,
- aucun `ExceptionalFilter`.
-/
structure TripletLocalExceptionalCandidate (T : Triplet) where
  quadraticIntegral : TripletQuadraticIntegralCandidateInterface T
  rawQuadratic : TripletRawQuadraticConsistency T
  candidateCompatibility :
    quadraticIntegral.quadratic.candidate.documentary.candidate =
      rawQuadratic.quadratic.candidate.documentary.candidate

/--
Constructeur minimal :
à partir d’une interface quadratique intégrale candidate déjà construite
et d’une cohérence raw/quadratique déjà construite,
on les relie par compatibilité de candidat documentaire.
-/
def mkTripletLocalExceptionalCandidate
    (T : Triplet)
    (Q : TripletQuadraticIntegralCandidateInterface T)
    (R : TripletRawQuadraticConsistency T)
    (hCompat :
      Q.quadratic.candidate.documentary.candidate =
        R.quadratic.candidate.documentary.candidate) :
    TripletLocalExceptionalCandidate T where
  quadraticIntegral := Q
  rawQuadratic := R
  candidateCompatibility := hCompat

/--
Le candidat local empaqueté conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletLocalExceptionalCandidate.matchesHistorical
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    matchesHistoricalSpectrum
      T
      E.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact E.quadraticIntegral.matchesHistorical

/--
Le candidat local empaqueté réalise bien le calcul quadratique harmonique.
-/
theorem TripletLocalExceptionalCandidate.realizesPower
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    E.quadraticIntegral.quadratic.powerCoeffs =
      tripletPowerSpectrum T := by
  exact E.quadraticIntegral.realizesPower

/--
Le candidat local empaqueté conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletLocalExceptionalCandidate.matchesHistoricalPower
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    E.quadraticIntegral.quadratic.powerCoeffs =
      E.quadraticIntegral.quadratic.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact E.quadraticIntegral.matchesHistoricalPower

/--
Le candidat local empaqueté porte bien l’intégralité harmonique minimale.
-/
theorem TripletLocalExceptionalCandidate.harmonicIntegral
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    certificateHasIntegralEntries
      E.quadraticIntegral.quadratic.candidate.documentary.harmonic := by
  exact E.quadraticIntegral.harmonicIntegral

/--
Le candidat local empaqueté porte bien l’intégralité finie documentaire.
-/
theorem TripletLocalExceptionalCandidate.documentaryIntegral
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    hasIntegralSpectrum
      E.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact E.quadraticIntegral.documentaryIntegral

/--
Le candidat local empaqueté conserve bien le critère brut d’intégralité harmonique.
-/
theorem TripletLocalExceptionalCandidate.rawIntegral
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    hasRawIntegralCriterion T := by
  exact E.rawQuadratic.rawIntegral

/--
Le candidat local empaqueté conserve bien la compatibilité harmonique
de la couche raw/quadratique.
-/
theorem TripletLocalExceptionalCandidate.harmonic_eq
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    E.rawQuadratic.quadratic.candidate.documentary.harmonic =
      E.rawQuadratic.rawCriterion.harmonic := by
  exact E.rawQuadratic.harmonic_eq

/--
Le candidat local empaqueté identifie bien les deux candidats documentaires.
-/
theorem TripletLocalExceptionalCandidate.candidate_eq
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    E.quadraticIntegral.quadratic.candidate.documentary.candidate =
      E.rawQuadratic.quadratic.candidate.documentary.candidate := by
  exact E.candidateCompatibility

/--
Cas Couret : candidat exceptionnel local canonique.
-/
def couretTripletLocalExceptionalCandidate :
    TripletLocalExceptionalCandidate couretTriplet :=
  mkTripletLocalExceptionalCandidate
    couretTriplet
    couretTripletQuadraticIntegralCandidateInterface
    couretTripletRawQuadraticConsistency
    (by rfl)

/--
Dans le cas Couret, le candidat local recolle bien
avec l’historique documentaire.
-/
theorem couretTripletLocalExceptionalCandidate_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact couretTripletLocalExceptionalCandidate.matchesHistorical

/--
Dans le cas Couret, le candidat local réalise bien
le calcul quadratique harmonique.
-/
theorem couretTripletLocalExceptionalCandidate_realizesPower :
    couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.powerCoeffs =
      tripletPowerSpectrum couretTriplet := by
  exact couretTripletLocalExceptionalCandidate.realizesPower

/--
Dans le cas Couret, le candidat local recolle bien quadratiquement
avec l’historique documentaire.
-/
theorem couretTripletLocalExceptionalCandidate_matchesHistoricalPower :
    couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.powerCoeffs =
      couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretTripletLocalExceptionalCandidate.matchesHistoricalPower

/--
Dans le cas Couret, le candidat local porte bien
l’intégralité harmonique minimale.
-/
theorem couretTripletLocalExceptionalCandidate_harmonicIntegral :
    certificateHasIntegralEntries
      couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic := by
  exact couretTripletLocalExceptionalCandidate.harmonicIntegral

/--
Dans le cas Couret, le candidat local porte bien
l’intégralité finie documentaire.
-/
theorem couretTripletLocalExceptionalCandidate_documentaryIntegral :
    hasIntegralSpectrum
      couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact couretTripletLocalExceptionalCandidate.documentaryIntegral

/--
Dans le cas Couret, le critère brut d’intégralité harmonique
est bien satisfait.
-/
theorem couretTripletLocalExceptionalCandidate_rawIntegral :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletLocalExceptionalCandidate.rawIntegral

/--
Dans le cas Couret, les deux candidats documentaires coïncident bien.
-/
theorem couretTripletLocalExceptionalCandidate_candidate_eq :
    couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate =
      couretTripletLocalExceptionalCandidate.rawQuadratic.quadratic.candidate.documentary.candidate := by
  exact couretTripletLocalExceptionalCandidate.candidate_eq

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- réalisation quadratique harmonique,
- recollement quadratique harmonique/documentaire,
- intégralité harmonique minimale,
- intégralité finie documentaire,
- critère brut d’intégralité harmonique,
- compatibilité des candidats documentaires.
-/
theorem couretTripletLocalExceptionalCandidate_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate
      ∧ couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.powerCoeffs =
          couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate
      ∧ hasRawIntegralCriterion couretTriplet
      ∧ couretTripletLocalExceptionalCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate =
          couretTripletLocalExceptionalCandidate.rawQuadratic.quadratic.candidate.documentary.candidate := by
  exact ⟨ couretTripletLocalExceptionalCandidate_matchesHistorical
        , couretTripletLocalExceptionalCandidate_realizesPower
        , couretTripletLocalExceptionalCandidate_matchesHistoricalPower
        , couretTripletLocalExceptionalCandidate_harmonicIntegral
        , couretTripletLocalExceptionalCandidate_documentaryIntegral
        , couretTripletLocalExceptionalCandidate_rawIntegral
        , couretTripletLocalExceptionalCandidate_candidate_eq ⟩

end

end CouretUnification.Core