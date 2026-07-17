import Mathlib.Tactic

/-!
Les objets `U30Nat` et `TCResiduesNat` sont des représentants au niveau `Nat`
utilisés pour la certification par `native_decide`.

Ils ne réutilisent volontairement pas les noms canoniques `U30` et `TC`,
qui existent déjà dans `Core/U30.lean` au-dessus de `ZMod 30`.
-/

open Finset

namespace CouretUnification.Core.TripletTCDoubleAdmissibility

/-- Les classes inversibles modulo 30, représentées par leurs résidus dans `Nat`. -/
def U30Nat : Finset Nat := {1, 7, 11, 13, 17, 19, 23, 29}

/-- Les représentants naturels du triplet de Couret. -/
def TCResiduesNat : Finset Nat := {1, 11, 29}

/-- Appartenance booléenne à `U30Nat`. -/
def inU30NatB (a : Nat) : Bool := decide (a ∈ U30Nat)

/-- Test booléen d’admissibilité affine pour les canaux jumeaux. -/
def twinOKB (a : Nat) : Bool := inU30NatB ((a + 2) % 30)

/-- Test booléen d’admissibilité affine pour les canaux Sophie-Germain. -/
def sophieOKB (a : Nat) : Bool := inU30NatB ((2 * a + 1) % 30)

/-- Test booléen de 2-torsion modulo 30. -/
def torsion2OKB (a : Nat) : Bool := decide ((a * a) % 30 = 1)

/-- Enveloppe propositionnelle du test d’admissibilité affine jumeaux. -/
def twinOK (a : Nat) : Prop := twinOKB a = true

/-- Enveloppe propositionnelle du test d’admissibilité affine Sophie-Germain. -/
def sophieOK (a : Nat) : Prop := sophieOKB a = true

/-- Classes de départ pour les canaux jumeaux modulo 30. -/
def twinSet : Finset Nat :=
  U30Nat.filter (fun a => twinOKB a = true)

/-- Classes admissibles pour les canaux Sophie-Germain modulo 30. -/
def sophieSet : Finset Nat :=
  U30Nat.filter (fun a => sophieOKB a = true)

/-- La 2-torsion dans `U30Nat`, c’est-à-dire les classes vérifiant `a^2 = 1 mod 30`. -/
def torsion2 : Finset Nat :=
  U30Nat.filter (fun a => torsion2OKB a = true)

/-- Les classes de départ des canaux jumeaux sont exactement 11, 17 et 29. -/
theorem twinSet_eq :
    twinSet = ({11, 17, 29} : Finset Nat) := by
  native_decide

/-- Les classes admissibles Sophie-Germain sont exactement 11, 23 et 29. -/
theorem sophieSet_eq :
    sophieSet = ({11, 23, 29} : Finset Nat) := by
  native_decide

/-- Les classes doublement admissibles sont exactement 11 et 29. -/
theorem intersection_eq :
    twinSet ∩ sophieSet = ({11, 29} : Finset Nat) := by
  native_decide

/-- La normalisation du noyau doublement admissible par la classe neutre `1` donne `T_C`. -/
theorem TC_from_double_admissibility :
    ({1} : Finset Nat) ∪ (twinSet ∩ sophieSet) = TCResiduesNat := by
  native_decide

/-- La 2-torsion de `U30Nat` est exactement `{1, 11, 19, 29}`. -/
theorem torsion2_eq :
    torsion2 = ({1, 11, 19, 29} : Finset Nat) := by
  native_decide

/-- Retirer `19 = -11 mod 30` de la 2-torsion donne `T_C`. -/
theorem TC_as_torsion_without_neg11 :
    torsion2.erase 19 = TCResiduesNat := by
  native_decide

/--
`T_C` n’est pas fermé pour la multiplication modulo 30 :
`11 * 29 ≡ 19 mod 30`, et `19 ∉ T_C`.
-/
theorem TC_not_closed_witness :
    (11 * 29) % 30 = 19 ∧ 19 ∉ TCResiduesNat := by
  native_decide

/-- Les classes non neutres de 2-torsion sont 11, 19 et 29. -/
theorem nonneutral_torsion_eq :
    torsion2.erase 1 = ({11, 19, 29} : Finset Nat) := by
  native_decide

/-- 11 survit aux deux tests affines. -/
theorem eleven_survives_both :
    twinOK 11 ∧ sophieOK 11 := by
  constructor
  · unfold twinOK
    native_decide
  · unfold sophieOK
    native_decide

/-- 29 survit aux deux tests affines. -/
theorem twentynine_survives_both :
    twinOK 29 ∧ sophieOK 29 := by
  constructor
  · unfold twinOK
    native_decide
  · unfold sophieOK
    native_decide

/-- 19 est la classe non neutre de 2-torsion qui échoue aux deux tests affines. -/
theorem nineteen_fails_both :
    ¬ twinOK 19 ∧ ¬ sophieOK 19 := by
  constructor
  · unfold twinOK
    native_decide
  · unfold sophieOK
    native_decide

/--
Dans la 2-torsion non neutre, les classes qui survivent aux deux tests
sont exactement 11 et 29.
-/
def nonneutralDoubleSurvivors : Finset Nat :=
  (torsion2.erase 1).filter
    (fun a => twinOKB a = true ∧ sophieOKB a = true)

theorem nonneutralDoubleSurvivors_eq :
    nonneutralDoubleSurvivors = ({11, 29} : Finset Nat) := by
  native_decide

/--
Énoncé compact :
`T_C` est la classe neutre plus les classes non neutres de 2-torsion
qui survivent aux deux tests affines.
-/
theorem TC_as_neutral_plus_survivors :
    ({1} : Finset Nat) ∪ nonneutralDoubleSurvivors = TCResiduesNat := by
  native_decide

/-!
## Statut

Ce fichier certifie un phénomène fini modulo 30 :

  twinSet      = {11, 17, 29}
  sophieSet    = {11, 23, 29}
  intersection = {11, 29}
  T_C          = {1} ∪ ({11, 29})

et aussi :

  torsion2 = {1, 11, 19, 29}
  T_C      = torsion2.erase 19

avec le défaut de fermeture :

  11 * 29 ≡ 19 mod 30
  19 ∉ T_C

Statut :
  [D-computational, finite]

Aucune revendication d’infinitude.
Aucune revendication RH.
Aucun transport revendiqué vers les nombres premiers réels.
-/

end CouretUnification.Core.TripletTCDoubleAdmissibility
