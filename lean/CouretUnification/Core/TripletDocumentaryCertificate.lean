import CouretUnification.Core.HarmonicCertificate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Certificat documentaire minimal pour un triplet arbitraire :
- un certificat harmonique,
- un spectre documentaire candidat,
- une preuve que le certificat harmonique recolle avec l'historique du candidat.
-/
structure TripletDocumentaryCertificate (T : Triplet) where
  harmonic : HarmonicCertificate T
  candidate : FiniteSpectrum
  historicalRecollement :
    certificateMatchesHistoricalSpectrum harmonic candidate

/--
Constructeur canonique :
si l'on dispose déjà d'un spectre documentaire candidat `S`
et d'une preuve de recollement historique,
alors on empaquette le tout avec le certificat harmonique canonique.
-/
def canonicalTripletDocumentaryCertificate
    (T : Triplet) (S : FiniteSpectrum)
    (h : matchesHistoricalSpectrum T S) :
    TripletDocumentaryCertificate T where
  harmonic := canonicalHarmonicCertificate T
  candidate := S
  historicalRecollement := by
    dsimp [certificateMatchesHistoricalSpectrum, matchesHistoricalSpectrum,
      canonicalHarmonicCertificate]
    exact h

/--
Un certificat documentaire implique bien le recollement historique nu.
-/
theorem TripletDocumentaryCertificate.matchesHistorical
    {T : Triplet} (D : TripletDocumentaryCertificate T) :
    matchesHistoricalSpectrum T D.candidate := by
  calc
    tripletFourier T = D.harmonic.coeffs := D.harmonic.realizes
    _ = D.candidate.rawHistorical.map (fun z => (z : ℂ)) := D.historicalRecollement

/--
Version spécialisée : le certificat documentaire canonique recolle bien
avec le spectre candidat utilisé à sa construction.
-/
theorem canonicalTripletDocumentaryCertificate_matches
    (T : Triplet) (S : FiniteSpectrum)
    (h : matchesHistoricalSpectrum T S) :
    (canonicalTripletDocumentaryCertificate T S h).candidate = S := by
  rfl

/--
Cas Couret : certificat documentaire canonique du triplet distingué.
-/
def couretTripletDocumentaryCertificate :
    TripletDocumentaryCertificate couretTriplet :=
  canonicalTripletDocumentaryCertificate
    couretTriplet
    couretTripletSpectrum
    couretCanonicalCertificate_matchesHistorical

/--
Cas Couret : le certificat documentaire recolle bien avec l'historique.
-/
theorem couretTripletDocumentaryCertificate_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletDocumentaryCertificate.candidate := by
  exact couretTripletDocumentaryCertificate.matchesHistorical

/--
Cas Couret : le candidat documentaire empaqueté est bien le spectre
documentaire gelé du triplet distingué.
-/
theorem couretTripletDocumentaryCertificate_candidate :
    couretTripletDocumentaryCertificate.candidate = couretTripletSpectrum := by
  rfl

/--
Cas Couret : le certificat harmonique empaqueté est bien le certificat canonique.
-/
theorem couretTripletDocumentaryCertificate_harmonic :
    couretTripletDocumentaryCertificate.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

end

end CouretUnification.Core