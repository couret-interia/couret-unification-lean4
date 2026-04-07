import CouretUnification.Core.TripletDocumentaryCertificate
import CouretUnification.Core.IntegralSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Interface minimale d'intégralité documentaire pour un triplet arbitraire :
- un certificat documentaire,
- l'intégralité des entrées du certificat harmonique empaqueté,
- l'intégralité finie du spectre documentaire candidat empaqueté.
On ne classe encore aucun triplet, et on n'ouvre pas `ExceptionalFilter`.
-/
structure TripletDocumentaryIntegralInterface (T : Triplet) where
  documentary : TripletDocumentaryCertificate T
  harmonicEntriesIntegral :
    certificateHasIntegralEntries documentary.harmonic
  candidateFiniteIntegral :
    hasIntegralSpectrum documentary.candidate

/--
Constructeur minimal :
on empaquette un certificat documentaire déjà construit
avec ses deux témoins d'intégralité minimaux.
-/
def mkTripletDocumentaryIntegralInterface
    (T : Triplet)
    (D : TripletDocumentaryCertificate T)
    (hH : certificateHasIntegralEntries D.harmonic)
    (hF : hasIntegralSpectrum D.candidate) :
    TripletDocumentaryIntegralInterface T where
  documentary := D
  harmonicEntriesIntegral := hH
  candidateFiniteIntegral := hF

/--
Le certificat documentaire empaqueté continue à recoller
avec le spectre historique de son candidat.
-/
theorem TripletDocumentaryIntegralInterface.matchesHistorical
    {T : Triplet} (I : TripletDocumentaryIntegralInterface T) :
    matchesHistoricalSpectrum T I.documentary.candidate := by
  exact I.documentary.matchesHistorical

/-- L'interface empaquetée porte bien l'intégralité harmonique documentaire. -/
theorem TripletDocumentaryIntegralInterface.harmonicIntegral
    {T : Triplet} (I : TripletDocumentaryIntegralInterface T) :
    certificateHasIntegralEntries I.documentary.harmonic := by
  exact I.harmonicEntriesIntegral

/-- L'interface empaquetée porte bien l'intégralité finie documentaire. -/
theorem TripletDocumentaryIntegralInterface.documentaryIntegral
    {T : Triplet} (I : TripletDocumentaryIntegralInterface T) :
    hasIntegralSpectrum I.documentary.candidate := by
  exact I.candidateFiniteIntegral

/--
Prédicat brut : un certificat documentaire a des entrées harmoniques entières.
-/
def documentaryCertificateHasIntegralHarmonicEntries
    {T : Triplet} (D : TripletDocumentaryCertificate T) : Prop :=
  certificateHasIntegralEntries D.harmonic

/--
Prédicat brut : un certificat documentaire a un spectre fini candidat entier.
-/
def documentaryCertificateHasIntegralFiniteSpectrum
    {T : Triplet} (D : TripletDocumentaryCertificate T) : Prop :=
  hasIntegralSpectrum D.candidate

/--
Cas Couret : interface minimale canonique.
On ne généralise encore rien aux 21 triplets.
-/
def couretTripletDocumentaryIntegralInterface :
    TripletDocumentaryIntegralInterface couretTriplet :=
  mkTripletDocumentaryIntegralInterface
    couretTriplet
    couretTripletDocumentaryCertificate
    couretCanonicalCertificate_hasIntegralEntries
    couretTriplet_hasIntegralSpectrum

/--
Validation groupée du cas Couret :
- recollement historique,
- intégralité harmonique documentaire,
- intégralité finie documentaire.
-/
theorem couretTripletDocumentaryIntegralInterface_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletDocumentaryIntegralInterface.documentary.candidate
      ∧ certificateHasIntegralEntries
          couretTripletDocumentaryIntegralInterface.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletDocumentaryIntegralInterface.documentary.candidate := by
  exact ⟨ couretTripletDocumentaryIntegralInterface.matchesHistorical
        , couretTripletDocumentaryIntegralInterface.harmonicIntegral
        , couretTripletDocumentaryIntegralInterface.documentaryIntegral ⟩

end

end CouretUnification.Core