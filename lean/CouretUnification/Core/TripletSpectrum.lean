import CouretUnification.Core.ExceptionalTriplets
import CouretUnification.Core.SpectralProfile
import Mathlib.Tactic

namespace CouretUnification.Core

/--
Un enregistrement spectral fini :
- spectre brut trié,
- spectre brut historique,
- profil quadratique trié,
- profil quadratique historique.
-/
structure FiniteSpectrum where
  rawSorted : List Int
  rawHistorical : List Int
  powerSorted : List Nat
  powerHistorical : List Nat
  rawSorted_len : rawSorted.length = 8
  rawHistorical_len : rawHistorical.length = 8
  powerSorted_len : powerSorted.length = 8
  powerHistorical_len : powerHistorical.length = 8

/-- Le triplet distingué T_C = {1,11,29}. -/
def couretTriplet : Triplet :=
  mkTriplet 0 2 7 (by decide) (by decide) (by decide)

/--
Spectre fini du triplet distingué.
-/
def couretTripletSpectrum : FiniteSpectrum :=
  { rawSorted := TCRawSpectrumSorted
  , rawHistorical := TCRawSpectrumHistorical
  , powerSorted := TCPowerSpectrumSorted
  , powerHistorical := TCPowerSpectrumHistorical
  , rawSorted_len := TCRawSpectrumSorted_length
  , rawHistorical_len := TCRawSpectrumHistorical_length
  , powerSorted_len := TCPowerSpectrumSorted_length
  , powerHistorical_len := TCPowerSpectrumHistorical_length
  }

/-- Masse quadratique du triplet distingué. -/
def couretTripletParsevalMass : Nat :=
  couretTripletSpectrum.powerHistorical.sum

lemma couretTripletParsevalMass_eq :
    couretTripletParsevalMass = 24 := by
  native_decide

/-
À ce stade, on fige seulement le vocabulaire spectral du triplet distingué.

La suite correcte est :
1. geler définitivement l'ordre des caractères ;
2. fermer la couche harmonique finie ;
3. calculer le spectre d'un triplet arbitraire ;
4. définir `hasIntegralSpectrum` ;
5. filtrer les 21 triplets.
-/

end CouretUnification.Core