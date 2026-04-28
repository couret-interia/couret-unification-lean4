import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Basic
import CouretUnification.Tower.PrimorialCharacterTower

namespace CouretUnification
namespace ConcreteUnits210

abbrev U210 := (ZMod 210)ˣ

instance : Fintype U210 :=
  inferInstance

instance : DecidableEq U210 :=
  inferInstance

instance : CommGroup U210 :=
  inferInstance

open CouretUnification.H3PrimorialTower

instance : FiniteUnitLevel 210 where
  U := U210
  fintypeU := inferInstance
  decEqU := inferInstance
  commGroupU := inferInstance

example : (1 : UMod 210) = 1 := rfl

end ConcreteUnits210
end CouretUnification
