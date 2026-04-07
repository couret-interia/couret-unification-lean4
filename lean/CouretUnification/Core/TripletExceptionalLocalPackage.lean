import CouretUnification.Core.TripletExceptionalPredicate
import CouretUnification.Core.TripletExceptionalDecidableShell
import CouretUnification.Core.TripletExceptionalWitness
import CouretUnification.Core.TripletLocalExceptionalCandidate
import CouretUnification.Core.TripletPowerSpectrum
import CouretUnification.Core.HarmonicCertificate
import CouretUnification.Core.IntegralSpectrum
import CouretUnification.Core.TripletRawIntegralCriterion
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet local cohérent, pour un triplet arbitraire, regroupant :

- le prédicat local de candidature exceptionnelle ;
- sa shell décidable purement locale ;
- un témoin explicite de candidature exceptionnelle locale.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletExceptionalLocalPackage (T : Triplet) where
  shell : TripletExceptionalDecidableShell T
  witness : TripletExceptionalWitness T
  shellPredicate :
    shell.predicate = isLocalExceptionalCandidate T
  witnessShell :
    witness.shell = shell

/--
Constructeur minimal :
on empaquette une shell locale déjà construite
et un témoin explicite déjà construit,
en imposant leur cohérence.
-/
def mkTripletExceptionalLocalPackage
    (T : Triplet)
    (S : TripletExceptionalDecidableShell T)
    (W : TripletExceptionalWitness T)
    (hP : S.predicate = isLocalExceptionalCandidate T)
    (hS : W.shell = S) :
    TripletExceptionalLocalPackage T where
  shell := S
  witness := W
  shellPredicate := hP
  witnessShell := hS

/--
Constructeur canonique minimal :
à partir d’une preuve du prédicat local, on fabrique
le paquet local canonique.
-/
def canonicalTripletExceptionalLocalPackage
    (T : Triplet) (h : isLocalExceptionalCandidate T) :
    TripletExceptionalLocalPackage T :=
  mkTripletExceptionalLocalPackage
    T
    (canonicalTripletExceptionalDecidableShell T)
    { shell := canonicalTripletExceptionalDecidableShell T
      witnessPredicate := by
        simpa [canonicalTripletExceptionalDecidableShell] using h }
    rfl
    rfl

/--
Le paquet local empaqueté vérifie bien le prédicat local.
-/
theorem TripletExceptionalLocalPackage.predicate
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    isLocalExceptionalCandidate T := by
  have hw : P.witness.shell.predicate := P.witness.witnessPredicate
  have hs : P.shell.predicate := by
    simpa [P.witnessShell] using hw
  simpa [P.shellPredicate] using hs

/--
Le paquet local fournit bien un candidat local explicite.
-/
def TripletExceptionalLocalPackage.localCandidate
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    TripletLocalExceptionalCandidate T :=
  P.witness.localCandidate

/--
Le paquet local conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletExceptionalLocalPackage.matchesHistorical
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    matchesHistoricalSpectrum
      T
      P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact P.localCandidate.matchesHistorical

/--
Le paquet local réalise bien le calcul quadratique harmonique.
-/
theorem TripletExceptionalLocalPackage.realizesPower
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    P.localCandidate.quadraticIntegral.quadratic.powerCoeffs =
      tripletPowerSpectrum T := by
  exact P.localCandidate.realizesPower

/--
Le paquet local conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletExceptionalLocalPackage.matchesHistoricalPower
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    P.localCandidate.quadraticIntegral.quadratic.powerCoeffs =
      P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact P.localCandidate.matchesHistoricalPower

/--
Le paquet local porte bien l’intégralité harmonique minimale.
-/
theorem TripletExceptionalLocalPackage.harmonicIntegral
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    certificateHasIntegralEntries
      P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic := by
  exact P.localCandidate.harmonicIntegral

/--
Le paquet local porte bien l’intégralité finie documentaire.
-/
theorem TripletExceptionalLocalPackage.documentaryIntegral
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    hasIntegralSpectrum
      P.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact P.localCandidate.documentaryIntegral

/--
Le paquet local porte bien le critère brut d’intégralité harmonique.
-/
theorem TripletExceptionalLocalPackage.rawIntegral
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    hasRawIntegralCriterion T := by
  exact P.localCandidate.rawIntegral

/--
Cas Couret : paquet local canonique de référence.
-/
def couretTripletExceptionalLocalPackage :
    TripletExceptionalLocalPackage couretTriplet :=
  mkTripletExceptionalLocalPackage
    couretTriplet
    couretTripletExceptionalDecidableShell
    couretTripletExceptionalWitness
    rfl
    rfl

/--
Dans le cas Couret, le paquet local vérifie bien le prédicat local.
-/
theorem couretTripletExceptionalLocalPackage_predicate :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTripletExceptionalLocalPackage.predicate

/--
Validation groupée du cas Couret :
- prédicat local ;
- recollement harmonique/documentaire historique ;
- réalisation quadratique harmonique ;
- recollement quadratique harmonique/documentaire ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique.
-/
theorem couretTripletExceptionalLocalPackage_valid :
    isLocalExceptionalCandidate couretTriplet
      ∧ matchesHistoricalSpectrum
          couretTriplet
          couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate
      ∧ couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.powerCoeffs =
          couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletExceptionalLocalPackage.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate
      ∧ hasRawIntegralCriterion couretTriplet := by
  exact ⟨ couretTripletExceptionalLocalPackage_predicate
        , couretTripletExceptionalLocalPackage.matchesHistorical
        , couretTripletExceptionalLocalPackage.realizesPower
        , couretTripletExceptionalLocalPackage.matchesHistoricalPower
        , couretTripletExceptionalLocalPackage.harmonicIntegral
        , couretTripletExceptionalLocalPackage.documentaryIntegral
        , couretTripletExceptionalLocalPackage.rawIntegral ⟩

end

end CouretUnification.Core