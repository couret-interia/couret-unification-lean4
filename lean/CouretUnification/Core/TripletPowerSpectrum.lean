import CouretUnification.Core.TripletToFiniteSpectrum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/-- Profil quadratique harmonique d'un triplet :
carrés des modules des 8 coefficients de Fourier, dans l'ordre documentaire gelé. -/
def tripletPowerSpectrum (T : Triplet) : List ℝ :=
  (tripletFourier T).map Complex.normSq

lemma tripletPowerSpectrum_length (T : Triplet) :
    (tripletPowerSpectrum T).length = 8 := by
  simp [tripletPowerSpectrum, tripletFourier_length]

/-- Injection du profil quadratique historique dans `ℝ`. -/
def historicalPowerSpectrumAsReal : List ℝ :=
  TCPowerSpectrumHistorical.map (fun n => (n : ℝ))

/-- Injection du profil quadratique trié dans `ℝ`. -/
def sortedPowerSpectrumAsReal : List ℝ :=
  TCPowerSpectrumSorted.map (fun n => (n : ℝ))

lemma historicalPowerSpectrumAsReal_length :
    historicalPowerSpectrumAsReal.length = 8 := by
  simp [historicalPowerSpectrumAsReal, TCPowerSpectrumHistorical_length]

lemma sortedPowerSpectrumAsReal_length :
    sortedPowerSpectrumAsReal.length = 8 := by
  simp [sortedPowerSpectrumAsReal, TCPowerSpectrumSorted_length]

/-- Le profil quadratique harmonique calculé coïncide avec le profil historique gelé. -/
def matchesHistoricalPowerSpectrum (T : Triplet) : Prop :=
  tripletPowerSpectrum T = historicalPowerSpectrumAsReal

/-- Le profil quadratique harmonique calculé coïncide avec le profil trié gelé. -/
def matchesSortedPowerSpectrum (T : Triplet) : Prop :=
  tripletPowerSpectrum T = sortedPowerSpectrumAsReal

lemma couretTriplet_power_explicit :
    tripletPowerSpectrum couretTriplet = ([9, 1, 1, 1, 9, 1, 1, 1] : List ℝ) := by
  rw [tripletPowerSpectrum, couretTriplet_fourier_explicit]
  norm_num [Complex.normSq]

lemma couretTriplet_matchesHistoricalPowerSpectrum :
    matchesHistoricalPowerSpectrum couretTriplet := by
  simpa [matchesHistoricalPowerSpectrum, historicalPowerSpectrumAsReal, TCPowerSpectrumHistorical]
    using couretTriplet_power_explicit

/-- Recollement harmonique du profil quadratique avec le profil documentaire déjà gelé. -/
lemma couretTriplet_power_reconstructs_finiteSpectrum :
    tripletPowerSpectrum couretTriplet =
      couretTripletSpectrum.powerHistorical.map (fun n => (n : ℝ)) := by
  simpa [historicalPowerSpectrumAsReal]
    using couretTriplet_matchesHistoricalPowerSpectrum

end

end CouretUnification.Core