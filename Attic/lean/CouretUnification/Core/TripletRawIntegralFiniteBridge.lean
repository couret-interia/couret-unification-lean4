import CouretUnification.Core.TripletDocumentaryIntegralInterface
import CouretUnification.Core.TripletRawIntegralCriterion
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Pont minimal, pour un triplet arbitraire, entre :
- un critère brut d’intégralité harmonique,
- une interface documentaire finie déjà empaquetée.

On impose seulement ici que les deux couches utilisent bien
le même certificat harmonique canonique.

On n’ouvre encore :
- aucun filtrage global,
- aucune classification des 21 triplets,
- aucun `ExceptionalFilter`.
-/
structure TripletRawIntegralFiniteBridge (T : Triplet) where
  documentaryIntegral : TripletDocumentaryIntegralInterface T
  rawCriterion : TripletRawIntegralCriterion T
  harmonicCompatibility :
    documentaryIntegral.documentary.harmonic = rawCriterion.harmonic

/--
Constructeur minimal :
à partir d’une interface documentaire intégrale déjà construite
et d’un critère brut d’intégralité déjà construit,
on les relie par compatibilité harmonique.
-/
def mkTripletRawIntegralFiniteBridge
    (T : Triplet)
    (D : TripletDocumentaryIntegralInterface T)
    (R : TripletRawIntegralCriterion T)
    (hCompat : D.documentary.harmonic = R.harmonic) :
    TripletRawIntegralFiniteBridge T where
  documentaryIntegral := D
  rawCriterion := R
  harmonicCompatibility := hCompat

/--
Le pont empaqueté conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletRawIntegralFiniteBridge.matchesHistorical
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    matchesHistoricalSpectrum T B.documentaryIntegral.documentary.candidate := by
  exact B.documentaryIntegral.matchesHistorical

/--
Le pont empaqueté conserve bien l’intégralité harmonique
des entrées du certificat documentaire.
-/
theorem TripletRawIntegralFiniteBridge.harmonicEntriesIntegral
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    certificateHasIntegralEntries B.documentaryIntegral.documentary.harmonic := by
  exact B.documentaryIntegral.harmonicIntegral

/--
Le pont empaqueté conserve bien l’intégralité finie documentaire
du candidat empaqueté.
-/
theorem TripletRawIntegralFiniteBridge.documentaryFiniteIntegral
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    hasIntegralSpectrum B.documentaryIntegral.documentary.candidate := by
  exact B.documentaryIntegral.documentaryIntegral

/--
Le pont empaqueté conserve bien le critère brut d’intégralité harmonique.
-/
theorem TripletRawIntegralFiniteBridge.rawIntegral
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    hasRawIntegralCriterion T := by
  exact B.rawCriterion.raw

/--
Le pont empaqueté identifie bien les deux certificats harmoniques sous-jacents.
-/
theorem TripletRawIntegralFiniteBridge.harmonic_eq
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    B.documentaryIntegral.documentary.harmonic = B.rawCriterion.harmonic := by
  exact B.harmonicCompatibility

/--
Le pont empaqueté réalise bien le calcul harmonique canonique
via son critère brut.
-/
theorem TripletRawIntegralFiniteBridge.realizes
    {T : Triplet} (B : TripletRawIntegralFiniteBridge T) :
    tripletFourier T = B.rawCriterion.harmonic.coeffs := by
  exact B.rawCriterion.realizes

/--
Cas Couret : pont canonique entre
- l’interface documentaire intégrale canonique,
- et le critère brut d’intégralité canonique.
-/
def couretTripletRawIntegralFiniteBridge :
    TripletRawIntegralFiniteBridge couretTriplet :=
  mkTripletRawIntegralFiniteBridge
    couretTriplet
    couretTripletDocumentaryIntegralInterface
    couretTripletRawIntegralCriterion
    (by rfl)

/--
Dans le cas Couret, le pont recolle bien avec l’historique documentaire.
-/
theorem couretTripletRawIntegralFiniteBridge_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.candidate := by
  exact couretTripletRawIntegralFiniteBridge.matchesHistorical

/--
Dans le cas Couret, le pont porte bien l’intégralité harmonique minimale
des entrées du certificat documentaire.
-/
theorem couretTripletRawIntegralFiniteBridge_harmonicEntriesIntegral :
    certificateHasIntegralEntries
      couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.harmonic := by
  exact couretTripletRawIntegralFiniteBridge.harmonicEntriesIntegral

/--
Dans le cas Couret, le pont porte bien l’intégralité finie documentaire.
-/
theorem couretTripletRawIntegralFiniteBridge_documentaryFiniteIntegral :
    hasIntegralSpectrum
      couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.candidate := by
  exact couretTripletRawIntegralFiniteBridge.documentaryFiniteIntegral

/--
Dans le cas Couret, le critère brut d’intégralité harmonique est bien satisfait.
-/
theorem couretTripletRawIntegralFiniteBridge_rawIntegral :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletRawIntegralFiniteBridge.rawIntegral

/--
Dans le cas Couret, les deux certificats harmoniques coïncident bien.
-/
theorem couretTripletRawIntegralFiniteBridge_harmonic_eq :
    couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.harmonic =
      couretTripletRawIntegralFiniteBridge.rawCriterion.harmonic := by
  exact couretTripletRawIntegralFiniteBridge.harmonic_eq

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- intégralité harmonique minimale des entrées,
- intégralité finie documentaire,
- critère brut d’intégralité harmonique,
- compatibilité harmonique entre les deux couches empaquetées.
-/
theorem couretTripletRawIntegralFiniteBridge_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.candidate
      ∧ certificateHasIntegralEntries
          couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.candidate
      ∧ hasRawIntegralCriterion couretTriplet
      ∧ couretTripletRawIntegralFiniteBridge.documentaryIntegral.documentary.harmonic =
          couretTripletRawIntegralFiniteBridge.rawCriterion.harmonic := by
  exact ⟨ couretTripletRawIntegralFiniteBridge_matchesHistorical
        , couretTripletRawIntegralFiniteBridge_harmonicEntriesIntegral
        , couretTripletRawIntegralFiniteBridge_documentaryFiniteIntegral
        , couretTripletRawIntegralFiniteBridge_rawIntegral
        , couretTripletRawIntegralFiniteBridge_harmonic_eq ⟩

end

end CouretUnification.Core