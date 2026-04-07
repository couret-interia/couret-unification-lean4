import CouretUnification.Core.TripletHarmonicSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

private theorem I_pow_six : (Complex.I : ℂ)^6 = (-1 : ℂ) := by
  norm_num [pow_succ, Complex.I_sq]

private theorem neg_I_pow_six : (-Complex.I : ℂ)^6 = (-1 : ℂ) := by
  norm_num [pow_succ, Complex.I_sq]

private theorem sum_fin8 (f : Fin 8 → ℂ) :
    (∑ g : Fin 8, f g) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  repeat rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_zero]
  norm_num
  rw [show (Fin.succ 2 : Fin 8) = 3 by decide]
  rw [show ((Fin.succ 2).succ : Fin 8) = 4 by decide]
  rw [show ((Fin.succ 2).succ.succ : Fin 8) = 5 by decide]
  rw [show ((Fin.succ 2).succ.succ.succ : Fin 8) = 6 by decide]
  rw [show ((Fin.succ 2).succ.succ.succ.succ : Fin 8) = 7 by decide]
  ring_nf

lemma couretTriplet_support_explicit :
    tripletSupport couretTriplet = ([0, 2, 7] : List Idx) := by
  native_decide

lemma documentaryCharacters_explicit :
    documentaryCharacters = ([0, 1, 2, 3, 4, 5, 6, 7] : List CharIdx) := by
  native_decide

lemma couretTriplet_fourier_coeff_0 :
    fourierCoeff (tripletIndicator couretTriplet) 0 = (3 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]
  norm_num

lemma couretTriplet_fourier_coeff_1 :
    fourierCoeff (tripletIndicator couretTriplet) 1 = (1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

lemma couretTriplet_fourier_coeff_2 :
    fourierCoeff (tripletIndicator couretTriplet) 2 = (1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase,
    neg_I_pow_six]

lemma couretTriplet_fourier_coeff_3 :
    fourierCoeff (tripletIndicator couretTriplet) 3 = (1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

lemma couretTriplet_fourier_coeff_4 :
    fourierCoeff (tripletIndicator couretTriplet) 4 = (3 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]
  norm_num

lemma couretTriplet_fourier_coeff_5 :
    fourierCoeff (tripletIndicator couretTriplet) 5 = (1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase,
    I_pow_six]

lemma couretTriplet_fourier_coeff_6 :
    fourierCoeff (tripletIndicator couretTriplet) 6 = (-1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

lemma couretTriplet_fourier_coeff_7 :
    fourierCoeff (tripletIndicator couretTriplet) 7 = (-1 : ℂ) := by
  rw [fourierCoeff, sum_fin8]
  simp [tripletIndicator, couretTriplet_support_explicit,
    character, characterEval, charCoord, residueCoord, c2Phase, c4Phase,
    I_pow_six]

lemma couretTriplet_fourier_explicit :
    tripletFourier couretTriplet = ([3, 1, 1, 1, 3, 1, -1, -1] : List ℂ) := by
  rw [tripletFourier, finiteFourier, documentaryCharacters_explicit]
  simp [couretTriplet_fourier_coeff_0,
        couretTriplet_fourier_coeff_1,
        couretTriplet_fourier_coeff_2,
        couretTriplet_fourier_coeff_3,
        couretTriplet_fourier_coeff_4,
        couretTriplet_fourier_coeff_5,
        couretTriplet_fourier_coeff_6,
        couretTriplet_fourier_coeff_7]

lemma couretTriplet_matchesHistoricalRawSpectrum :
    matchesHistoricalRawSpectrum couretTriplet := by
  simpa [matchesHistoricalRawSpectrum, historicalRawSpectrumAsComplex, TCRawSpectrumHistorical]
    using couretTriplet_fourier_explicit

lemma couretTriplet_harmonic_equals_historical :
    tripletFourier couretTriplet = historicalRawSpectrumAsComplex := by
  simpa [matchesHistoricalRawSpectrum]
    using couretTriplet_matchesHistoricalRawSpectrum

lemma couretTriplet_harmonic_reconstructs_finiteSpectrum :
    tripletFourier couretTriplet =
      couretTripletSpectrum.rawHistorical.map (fun z => (z : ℂ)) := by
  simpa [historicalRawSpectrumAsComplex]
    using couretTriplet_harmonic_equals_historical

end

end CouretUnification.Core