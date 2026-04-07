import CouretUnification.Core.FiniteOperator
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Core

abbrev RawEigenvalue := Int
abbrev PowerEigenvalue := Nat

/--
Spectre brut de TC, vu comme multiensemble trié à permutation près.
-/
def TCRawSpectrumSorted : List RawEigenvalue :=
  [3, 3, 1, 1, 1, 1, -1, -1]

/--
Spectre brut de TC dans l'ordre documentaire choisi pour les caractères.
Cet ordre est celui qui donnera ensuite le profil quadratique historique
`[9,1,1,1,9,1,1,1]`.
-/
def TCRawSpectrumHistorical : List RawEigenvalue :=
  [3, 1, 1, 1, 3, 1, -1, -1]

/--
Profil quadratique canonique : carrés des modules des valeurs propres.
Version triée.
-/
def TCPowerSpectrumSorted : List PowerEigenvalue :=
  [9, 9, 1, 1, 1, 1, 1, 1]

/--
Profil quadratique historique tel qu'il apparaît dans la documentation.
Même multiensemble que `TCPowerSpectrumSorted`, ordre documentaire conservé.
-/
def TCPowerSpectrumHistorical : List PowerEigenvalue :=
  [9, 1, 1, 1, 9, 1, 1, 1]

def TCParsevalMass : Nat := TCPowerSpectrumHistorical.sum

lemma TCRawSpectrumSorted_length :
    TCRawSpectrumSorted.length = 8 := by
  decide

lemma TCRawSpectrumHistorical_length :
    TCRawSpectrumHistorical.length = 8 := by
  decide

lemma TCPowerSpectrumSorted_length :
    TCPowerSpectrumSorted.length = 8 := by
  decide

lemma TCPowerSpectrumHistorical_length :
    TCPowerSpectrumHistorical.length = 8 := by
  decide

lemma TCParsevalMass_eq : TCParsevalMass = 24 := by
  native_decide

noncomputable def TCAverageEnergy : ℚ :=
  (TCParsevalMass : ℚ) / 8

lemma TCAverageEnergy_eq : TCAverageEnergy = 3 := by
  norm_num [TCAverageEnergy, TCParsevalMass, TCPowerSpectrumHistorical]

end CouretUnification.Core