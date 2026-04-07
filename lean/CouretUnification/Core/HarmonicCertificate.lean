import CouretUnification.Core.TripletToFiniteSpectrum
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Certificat harmonique minimal pour un triplet arbitraire :
- la liste des 8 coefficients complexes,
- sa longueur,
- la preuve qu'elle réalise exactement `tripletFourier T`.
-/
structure HarmonicCertificate (T : Triplet) where
  coeffs : List ℂ
  coeffs_len : coeffs.length = 8
  realizes : tripletFourier T = coeffs

/-- Certificat harmonique canonique associé à un triplet arbitraire. -/
def canonicalHarmonicCertificate (T : Triplet) : HarmonicCertificate T where
  coeffs := tripletFourier T
  coeffs_len := tripletFourier_length T
  realizes := rfl

/--
Comparaison minimale entre le calcul harmonique d'un triplet
et un spectre historique documentaire déjà gelé.
-/
def matchesHistoricalSpectrum (T : Triplet) (S : FiniteSpectrum) : Prop :=
  tripletFourier T = S.rawHistorical.map (fun z => (z : ℂ))

/--
Version empaquetée via certificat harmonique.
-/
def certificateMatchesHistoricalSpectrum
    {T : Triplet} (C : HarmonicCertificate T) (S : FiniteSpectrum) : Prop :=
  C.coeffs = S.rawHistorical.map (fun z => (z : ℂ))

/--
Intégralité harmonique minimale :
chaque coefficient de Fourier du triplet est un entier vu dans `ℂ`.
-/
def hasIntegralHarmonicSpectrum (T : Triplet) : Prop :=
  ∀ χ : CharIdx, ∃ z : Int, fourierCoeff (tripletIndicator T) χ = (z : ℂ)

/--
Version empaquetée via certificat harmonique :
toutes les entrées du certificat sont entières dans `ℂ`.
-/
def certificateHasIntegralEntries
    {T : Triplet} (C : HarmonicCertificate T) : Prop :=
  ∀ c ∈ C.coeffs, ∃ z : Int, c = (z : ℂ)

theorem canonicalHarmonicCertificate_len (T : Triplet) :
    (canonicalHarmonicCertificate T).coeffs.length = 8 := by
  exact (canonicalHarmonicCertificate T).coeffs_len

theorem canonicalHarmonicCertificate_realizes (T : Triplet) :
    tripletFourier T = (canonicalHarmonicCertificate T).coeffs := by
  exact (canonicalHarmonicCertificate T).realizes

/--
Cas Couret : le certificat canonique recolle bien avec le spectre
historique documentaire gelé.
-/
theorem couretCanonicalCertificate_matchesHistorical :
    certificateMatchesHistoricalSpectrum
      (canonicalHarmonicCertificate couretTriplet)
      couretTripletSpectrum := by
  simpa [certificateMatchesHistoricalSpectrum, canonicalHarmonicCertificate]
    using couretTriplet_harmonic_reconstructs_finiteSpectrum

/--
Cas Couret : intégralité harmonique directe, sans classifier d'autres triplets.
-/
theorem couretTriplet_hasIntegralHarmonicSpectrum :
    hasIntegralHarmonicSpectrum couretTriplet := by
  intro χ
  fin_cases χ
  · exact ⟨3, by simpa using couretTriplet_fourier_coeff_0⟩
  · exact ⟨1, by simpa using couretTriplet_fourier_coeff_1⟩
  · exact ⟨1, by simpa using couretTriplet_fourier_coeff_2⟩
  · exact ⟨1, by simpa using couretTriplet_fourier_coeff_3⟩
  · exact ⟨3, by simpa using couretTriplet_fourier_coeff_4⟩
  · exact ⟨1, by simpa using couretTriplet_fourier_coeff_5⟩
  · exact ⟨-1, by simpa using couretTriplet_fourier_coeff_6⟩
  · exact ⟨-1, by simpa using couretTriplet_fourier_coeff_7⟩

/--
Cas Couret : le certificat canonique a bien des entrées entières.
-/
theorem couretCanonicalCertificate_hasIntegralEntries :
    certificateHasIntegralEntries
      (canonicalHarmonicCertificate couretTriplet) := by
  intro c hc
  have hc_explicit : c ∈ ([3, 1, 1, 1, 3, 1, -1, -1] : List ℂ) := by
    simpa [canonicalHarmonicCertificate, couretTriplet_fourier_explicit] using hc
  have hc_cases : c = (3 : ℂ) ∨ c = (1 : ℂ) ∨ c = (-1 : ℂ) := by
    simp at hc_explicit
    tauto
  rcases hc_cases with h3 | h1 | hm1
  · exact ⟨3, by simpa using h3⟩
  · exact ⟨1, by simpa using h1⟩
  · exact ⟨-1, by simpa using hm1⟩

/--
Formulation groupée minimale pour le cas Couret :
- recollement historique,
- intégralité harmonique,
- intégralité des entrées du certificat canonique.
-/
theorem couretCanonicalCertificate_valid :
    certificateMatchesHistoricalSpectrum
        (canonicalHarmonicCertificate couretTriplet)
        couretTripletSpectrum
      ∧ hasIntegralHarmonicSpectrum couretTriplet
      ∧ certificateHasIntegralEntries
          (canonicalHarmonicCertificate couretTriplet) := by
  exact ⟨ couretCanonicalCertificate_matchesHistorical
        , couretTriplet_hasIntegralHarmonicSpectrum
        , couretCanonicalCertificate_hasIntegralEntries ⟩

end

end CouretUnification.Core