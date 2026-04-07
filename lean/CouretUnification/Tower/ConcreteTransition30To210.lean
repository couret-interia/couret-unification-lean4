import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteUnits30
import CouretUnification.Tower.ConcreteUnits210

namespace CouretUnification
namespace ConcreteTransition30To210

open CouretUnification.H3PrimorialTower
open ConcreteUnits30
open ConcreteUnits210

/-- Réduction canonique `ZMod 210 → ZMod 30`. -/
def cast210To30 : ZMod 210 →+* ZMod 30 :=
  ZMod.castHom (show 30 ∣ 210 by decide) (ZMod 30)

/-- Projection naturelle des unités modulo 210 vers les unités modulo 30. -/
def reduceUnit210To30 : UMod 210 → UMod 30 :=
  Units.map cast210To30

@[simp]
theorem reduceUnit210To30_one :
    reduceUnit210To30 1 = 1 := by
  simp [reduceUnit210To30, cast210To30]

@[simp]
theorem reduceUnit210To30_mul (a b : UMod 210) :
    reduceUnit210To30 (a * b) = reduceUnit210To30 a * reduceUnit210To30 b := by
  simp [reduceUnit210To30, cast210To30]

def levelMap30To210 : LevelMap 30 210 where
  toFun := reduceUnit210To30
  map_one' := by
    simp
  map_mul' := by
    intro a b
    simp

@[simp]
theorem levelMap30To210_apply (u : UMod 210) :
    levelMap30To210 u = reduceUnit210To30 u :=
  rfl

example : levelMap30To210 1 = 1 := by
  simp [levelMap30To210]

/-
On reconstruit localement le morphisme 210 -> 30 à partir de la réduction concrète.
-/
set_option linter.unnecessarySimpa false

def transition30To210 : LevelMap 30 210 where
  toFun := reduceUnit210To30
  map_one' := by
    simpa using
      reduceUnit210To30_map_one
  map_mul' := by
    intro a b
    simpa using
      reduceUnit210To30_map_mul a b

set_option linter.unnecessarySimpa true

end ConcreteTransition30To210
end CouretUnification
