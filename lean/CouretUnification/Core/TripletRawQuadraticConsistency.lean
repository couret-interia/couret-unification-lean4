import CouretUnification.Core.TripletQuadraticCandidateCertificate
import CouretUnification.Core.TripletRawIntegralCriterion
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Cohérence minimale, pour un triplet arbitraire, entre :
- un certificat candidat purement quadratique,
- un critère brut d’intégralité harmonique.

On impose seulement ici que les deux couches utilisent bien
le même certificat harmonique canonique.
On n’ouvre encore :
- aucun filtrage global,
- aucune classification des 21 triplets,
- aucun `ExceptionalFilter`.
-/
structure TripletRawQuadraticConsistency (T : Triplet) where
  quadratic : TripletQuadraticCandidateCertificate T
  rawCriterion : TripletRawIntegralCriterion T
  harmonicCompatibility :
    quadratic.candidate.documentary.harmonic = rawCriterion.harmonic

/--
Constructeur minimal :
à partir d’un certificat candidat quadratique déjà construit
et d’un critère brut d’intégralité déjà construit,
on les relie par compatibilité harmonique.
-/
def mkTripletRawQuadraticConsistency
    (T : Triplet)
    (Q : TripletQuadraticCandidateCertificate T)
    (R : TripletRawIntegralCriterion T)
    (hCompat : Q.candidate.documentary.harmonic = R.harmonic) :
    TripletRawQuadraticConsistency T where
  quadratic := Q
  rawCriterion := R
  harmonicCompatibility := hCompat

/--
La cohérence empaquetée conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletRawQuadraticConsistency.matchesHistorical
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    matchesHistoricalSpectrum T C.quadratic.candidate.documentary.candidate := by
  exact C.quadratic.matchesHistorical

/--
La cohérence empaquetée réalise bien le calcul quadratique harmonique.
-/
theorem TripletRawQuadraticConsistency.realizesPower
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    C.quadratic.powerCoeffs = tripletPowerSpectrum T := by
  exact C.quadratic.realizesPower

/--
La cohérence empaquetée conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletRawQuadraticConsistency.matchesHistoricalPower
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    C.quadratic.powerCoeffs =
      C.quadratic.candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact C.quadratic.matchesHistoricalPower

/--
La cohérence empaquetée conserve bien le critère brut d’intégralité harmonique.
-/
theorem TripletRawQuadraticConsistency.rawIntegral
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    hasRawIntegralCriterion T := by
  exact C.rawCriterion.raw

/--
La cohérence empaquetée identifie bien les deux certificats harmoniques sous-jacents.
-/
theorem TripletRawQuadraticConsistency.harmonic_eq
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    C.quadratic.candidate.documentary.harmonic = C.rawCriterion.harmonic := by
  exact C.harmonicCompatibility

/--
La cohérence empaquetée réalise bien le calcul harmonique canonique
via son critère brut.
-/
theorem TripletRawQuadraticConsistency.realizesHarmonic
    {T : Triplet} (C : TripletRawQuadraticConsistency T) :
    tripletFourier T = C.rawCriterion.harmonic.coeffs := by
  exact C.rawCriterion.realizes

/--
Cas Couret : cohérence canonique entre
- le certificat candidat purement quadratique canonique,
- et le critère brut d’intégralité canonique.
-/
def couretTripletRawQuadraticConsistency :
    TripletRawQuadraticConsistency couretTriplet :=
  mkTripletRawQuadraticConsistency
    couretTriplet
    couretTripletQuadraticCandidateCertificate
    couretTripletRawIntegralCriterion
    (by rfl)

/--
Dans le cas Couret, la cohérence recolle bien avec l’historique documentaire.
-/
theorem couretTripletRawQuadraticConsistency_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.candidate := by
  exact couretTripletRawQuadraticConsistency.matchesHistorical

/--
Dans le cas Couret, la cohérence réalise bien le calcul quadratique harmonique.
-/
theorem couretTripletRawQuadraticConsistency_realizesPower :
    couretTripletRawQuadraticConsistency.quadratic.powerCoeffs =
      tripletPowerSpectrum couretTriplet := by
  exact couretTripletRawQuadraticConsistency.realizesPower

/--
Dans le cas Couret, la cohérence recolle bien quadratiquement
avec l’historique documentaire.
-/
theorem couretTripletRawQuadraticConsistency_matchesHistoricalPower :
    couretTripletRawQuadraticConsistency.quadratic.powerCoeffs =
      couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretTripletRawQuadraticConsistency.matchesHistoricalPower

/--
Dans le cas Couret, le critère brut d’intégralité harmonique est bien satisfait.
-/
theorem couretTripletRawQuadraticConsistency_rawIntegral :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletRawQuadraticConsistency.rawIntegral

/--
Dans le cas Couret, les deux certificats harmoniques coïncident bien.
-/
theorem couretTripletRawQuadraticConsistency_harmonic_eq :
    couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.harmonic =
      couretTripletRawQuadraticConsistency.rawCriterion.harmonic := by
  exact couretTripletRawQuadraticConsistency.harmonic_eq

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- réalisation quadratique harmonique,
- recollement quadratique harmonique/documentaire,
- critère brut d’intégralité harmonique,
- compatibilité harmonique entre les deux couches empaquetées.
-/
theorem couretTripletRawQuadraticConsistency_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.candidate
      ∧ couretTripletRawQuadraticConsistency.quadratic.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletRawQuadraticConsistency.quadratic.powerCoeffs =
          couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ hasRawIntegralCriterion couretTriplet
      ∧ couretTripletRawQuadraticConsistency.quadratic.candidate.documentary.harmonic =
          couretTripletRawQuadraticConsistency.rawCriterion.harmonic := by
  exact ⟨ couretTripletRawQuadraticConsistency_matchesHistorical
        , couretTripletRawQuadraticConsistency_realizesPower
        , couretTripletRawQuadraticConsistency_matchesHistoricalPower
        , couretTripletRawQuadraticConsistency_rawIntegral
        , couretTripletRawQuadraticConsistency_harmonic_eq ⟩

end

end CouretUnification.Core