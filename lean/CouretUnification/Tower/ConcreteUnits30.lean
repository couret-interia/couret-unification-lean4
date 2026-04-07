import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Basic
import CouretUnification.Tower.PrimorialCharacterTower -- H3PrimorialTower

namespace CouretUnification
namespace ConcreteUnits30

/-!
# ConcreteUnits30

Instance concrète de `FiniteUnitLevel` pour `n = 30`.

On utilise directement :
  (ZMod 30)ˣ
-/


/- =========================
   Définition des unités mod 30
   ========================= -/

abbrev U30 := (ZMod 30)ˣ


/- =========================
   Instances de base
   ========================= -/

instance : Fintype U30 :=
  inferInstance

instance : DecidableEq U30 :=
  inferInstance

instance : CommGroup U30 :=
  inferInstance


/-
Les unités modulo 30 sont les inversibles dans ZMod 30,
donc exactement les classes :
1, 7, 11, 13, 17, 19, 23, 29
(8 éléments)
-/


/- =========================
   Bridge vers FiniteUnitLevel
   ========================= -/

open CouretUnification.H3PrimorialTower

instance : FiniteUnitLevel 30 where
  U := U30
  fintypeU := inferInstance
  decEqU := inferInstance
  commGroupU := inferInstance


/-
À ce stade :
- `UMod 30` est utilisable
- toute la tour abstraite fonctionne sur 30
-/


/- =========================
   Sanity checks (Lean)
   ========================= -/

-- exemple : on peut utiliser l’unité neutre
example : (1 : UMod 30) = 1 := rfl

-- cardinal attendu (non prouvé ici, juste vérifiable si besoin)
-- #eval Fintype.card (UMod 30)

end ConcreteUnits30
end CouretUnification
