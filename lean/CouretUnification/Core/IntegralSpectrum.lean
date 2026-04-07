import CouretUnification.Core.TripletSpectrum
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

/--
Masse quadratique associée à une valeur propre entière `z`.

On passe de `z` au profil quadratique via `z^2`.
Comme `z^2 ≥ 0`, on peut l'enregistrer en `Nat` via `Int.natAbs`.
-/
def rawEntryToPower (z : Int) : Nat :=
  Int.natAbs (z * z)

/--
Transformation d'un spectre brut entier en profil quadratique.
-/
def rawSpectrumToPower (L : List Int) : List Nat :=
  L.map rawEntryToPower

/--
Notion minimale de "spectre entier" au niveau fini :
le spectre brut enregistré doit reproduire le profil quadratique enregistré
par passage au carré, à la fois

- dans l'ordre documentaire historique ;
- dans l'ordre trié canonique.

Ce fichier ne prétend pas encore calculer le spectre d'un triplet arbitraire.
Il fige seulement une propriété de cohérence sur un `FiniteSpectrum` déjà donné.
-/
def hasIntegralSpectrum (S : FiniteSpectrum) : Prop :=
  rawSpectrumToPower S.rawHistorical = S.powerHistorical ∧
  rawSpectrumToPower S.rawSorted = S.powerSorted

lemma couretTriplet_rawHistorical_toPower :
    rawSpectrumToPower couretTripletSpectrum.rawHistorical =
      couretTripletSpectrum.powerHistorical := by
  native_decide

lemma couretTriplet_rawSorted_toPower :
    rawSpectrumToPower couretTripletSpectrum.rawSorted =
      couretTripletSpectrum.powerSorted := by
  native_decide

/--
Le triplet distingué `T_C = {1,11,29}` possède bien un spectre entier
au sens fini/documentaire fixé dans le noyau.
-/
lemma couretTriplet_hasIntegralSpectrum :
    hasIntegralSpectrum couretTripletSpectrum := by
  constructor <;> native_decide

/--
Version spécialisée du prédicat au triplet distingué.
-/
def couretTripletHasIntegralSpectrum : Prop :=
  hasIntegralSpectrum couretTripletSpectrum

lemma couretTripletHasIntegralSpectrum_true :
    couretTripletHasIntegralSpectrum := by
  exact couretTriplet_hasIntegralSpectrum

/-
À ce stade, `IntegralSpectrum.lean` ne fait qu'une chose :
il relie proprement

- spectre brut entier enregistré,
- profil quadratique enregistré.

La prochaine étape correcte est :

1. construire la vraie couche harmonique finie pour un triplet arbitraire ;
2. produire son `FiniteSpectrum` ;
3. tester alors `hasIntegralSpectrum`.
-/

end CouretUnification.Core