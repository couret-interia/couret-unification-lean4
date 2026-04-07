import CouretUnification.Core.HarmonicCertificate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Critère minimal d’intégralité brute pour un triplet arbitraire :
les 8 coefficients harmoniques calculés sont des entiers vus dans `ℂ`.

Aucun filtrage global n’est encore imposé ici,
et on n’ouvre pas encore `ExceptionalFilter`.
-/
def hasRawIntegralCriterion (T : Triplet) : Prop :=
  hasIntegralHarmonicSpectrum T

/--
Interface minimale empaquetant :
- le certificat harmonique canonique ;
- le critère brut d’intégralité sur les 8 coefficients harmoniques.
-/
structure TripletRawIntegralCriterion (T : Triplet) where
  harmonic : HarmonicCertificate T
  rawIntegral : hasRawIntegralCriterion T

/--
Constructeur canonique minimal :
à partir d’un témoin du critère brut d’intégralité,
on l’adosse au certificat harmonique canonique.
-/
def canonicalTripletRawIntegralCriterion
    (T : Triplet) (h : hasRawIntegralCriterion T) :
    TripletRawIntegralCriterion T where
  harmonic := canonicalHarmonicCertificate T
  rawIntegral := h

/--
Le critère empaqueté conserve bien la réalisation harmonique canonique.
-/
theorem TripletRawIntegralCriterion.realizes
    {T : Triplet} (R : TripletRawIntegralCriterion T) :
    tripletFourier T = R.harmonic.coeffs := by
  exact R.harmonic.realizes

/--
Le critère empaqueté porte bien le critère brut d’intégralité.
-/
theorem TripletRawIntegralCriterion.raw
    {T : Triplet} (R : TripletRawIntegralCriterion T) :
    hasRawIntegralCriterion T := by
  exact R.rawIntegral

/--
Le certificat harmonique empaqueté garde bien longueur 8.
-/
theorem TripletRawIntegralCriterion.coeffs_len
    {T : Triplet} (R : TripletRawIntegralCriterion T) :
    R.harmonic.coeffs.length = 8 := by
  exact R.harmonic.coeffs_len

/--
Cas Couret : critère brut d’intégralité canonique.
-/
def couretTripletRawIntegralCriterion :
    TripletRawIntegralCriterion couretTriplet :=
  canonicalTripletRawIntegralCriterion
    couretTriplet
    couretTriplet_hasIntegralHarmonicSpectrum

/--
Dans le cas Couret, le certificat harmonique empaqueté est bien
le certificat canonique déjà gelé.
-/
theorem couretTripletRawIntegralCriterion_harmonic :
    couretTripletRawIntegralCriterion.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/--
Dans le cas Couret, le critère brut d’intégralité est bien satisfait.
-/
theorem couretTripletRawIntegralCriterion_raw :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletRawIntegralCriterion.raw

/--
Dans le cas Couret, les entrées du certificat harmonique empaqueté
sont bien entières.
-/
theorem couretTripletRawIntegralCriterion_hasIntegralEntries :
    certificateHasIntegralEntries
      couretTripletRawIntegralCriterion.harmonic := by
  simpa [couretTripletRawIntegralCriterion, canonicalTripletRawIntegralCriterion]
    using couretCanonicalCertificate_hasIntegralEntries

/--
Validation groupée du cas Couret :
- critère brut d’intégralité ;
- identification du certificat harmonique canonique ;
- intégralité des entrées du certificat harmonique.
-/
theorem couretTripletRawIntegralCriterion_valid :
    hasRawIntegralCriterion couretTriplet
      ∧ couretTripletRawIntegralCriterion.harmonic =
          canonicalHarmonicCertificate couretTriplet
      ∧ certificateHasIntegralEntries
          couretTripletRawIntegralCriterion.harmonic := by
  exact ⟨ couretTripletRawIntegralCriterion_raw
        , couretTripletRawIntegralCriterion_harmonic
        , couretTripletRawIntegralCriterion_hasIntegralEntries ⟩

end

end CouretUnification.Core