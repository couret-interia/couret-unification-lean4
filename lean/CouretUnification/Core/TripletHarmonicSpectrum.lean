import CouretUnification.Core.TripletSpectrum
import CouretUnification.Core.Fourier30
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-- Spectre harmonique fini d'un triplet :
liste ordonnée des 8 coefficients de Fourier dans l'ordre documentaire gelé. -/
structure HarmonicSpectrum where
  coeffs : List ℂ
  coeffs_len : coeffs.length = 8

/-- Indicatrice complexe d'un triplet sur la base active. -/
def tripletIndicator (T : Triplet) : Signal30 :=
  fun i => if i ∈ tripletSupport T then 1 else 0

/-- Spectre harmonique brut d'un triplet. -/
def tripletFourier (T : Triplet) : List ℂ :=
  finiteFourier (tripletIndicator T)

lemma tripletFourier_length (T : Triplet) :
    (tripletFourier T).length = 8 := by
  simpa [tripletFourier] using finiteFourier_length (tripletIndicator T)

/-- Empaquetage du spectre harmonique. -/
def tripletHarmonicSpectrum (T : Triplet) : HarmonicSpectrum :=
  { coeffs := tripletFourier T
  , coeffs_len := tripletFourier_length T }

/-- Spectre harmonique du triplet distingué. -/
def couretTripletHarmonicSpectrum : HarmonicSpectrum :=
  tripletHarmonicSpectrum couretTriplet

/-- Injection du spectre brut historique dans `ℂ`. -/
def historicalRawSpectrumAsComplex : List ℂ :=
  TCRawSpectrumHistorical.map (fun z => (z : ℂ))

/-- Injection du spectre brut trié dans `ℂ`. -/
def sortedRawSpectrumAsComplex : List ℂ :=
  TCRawSpectrumSorted.map (fun z => (z : ℂ))

lemma historicalRawSpectrumAsComplex_length :
    historicalRawSpectrumAsComplex.length = 8 := by
  simp [historicalRawSpectrumAsComplex, TCRawSpectrumHistorical_length]

lemma sortedRawSpectrumAsComplex_length :
    sortedRawSpectrumAsComplex.length = 8 := by
  simp [sortedRawSpectrumAsComplex, TCRawSpectrumSorted_length]

/-- Le calcul harmonique coïncide avec le spectre brut historique gelé. -/
def matchesHistoricalRawSpectrum (T : Triplet) : Prop :=
  tripletFourier T = historicalRawSpectrumAsComplex

/-- Le calcul harmonique coïncide avec le spectre brut trié gelé. -/
def matchesSortedRawSpectrum (T : Triplet) : Prop :=
  tripletFourier T = sortedRawSpectrumAsComplex

end

end CouretUnification.Core