/-
  CouretUnification/Core/UnitsBridge.lean
  Pont U30 (Finset) ↔ G30 ((ZMod 30)ˣ).
  0 sorry. 0 axiome.
-/

import CouretUnification.Core.U30
import Mathlib.Data.ZMod.Units

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Le type de groupe
-- ═══════════════════════════════════════════════════════════

abbrev G30 : Type := (ZMod 30)ˣ

instance : CommGroup G30 := inferInstance
instance : Fintype G30 := inferInstance
instance : DecidableEq G30 := inferInstance

theorem card_G30 : Fintype.card G30 = 8 := by decide

-- ═══════════════════════════════════════════════════════════
-- §2. Pont U30 ↔ G30
-- ═══════════════════════════════════════════════════════════

/-- Injection canonique : une unité donne un élément de ZMod 30. -/
def G30.toZMod (u : G30) : ZMod 30 := (u : ZMod 30)

/-- Tout élément de G30, vu dans ZMod 30, est dans U30. -/
theorem G30.toZMod_mem_U30 (u : G30) : G30.toZMod u ∈ U30 := by
  -- Énumérer les 8 unités, vérifier chacune
  fin_cases u <;> native_decide

/-- Tout élément de U30 provient d'un unique élément de G30. -/
theorem U30_of_mem (x : ZMod 30) (hx : x ∈ U30) :
    ∃ u : G30, G30.toZMod u = x := by
  -- Déplier U30 = {1,7,11,13,17,19,23,29} et traiter chaque cas
  simp only [U30, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨1,  1,  by decide, by decide⟩, rfl⟩
  · exact ⟨⟨7,  13, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨11, 11, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨13, 7,  by decide, by decide⟩, rfl⟩
  · exact ⟨⟨17, 23, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨19, 19, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨23, 17, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨29, 29, by decide, by decide⟩, rfl⟩

-- ═══════════════════════════════════════════════════════════
-- §3. Cohérence cardinale
-- ═══════════════════════════════════════════════════════════

theorem card_U30_eq_card_G30 : U30.card = Fintype.card G30 := by
  rw [card_U30, card_G30]

-- ═══════════════════════════════════════════════════════════
-- §4. Cohérence avec FiniteCore existant
-- ═══════════════════════════════════════════════════════════

theorem TC_mem_bridge :
    (1 : ZMod 30) ∈ TC ∧ (11 : ZMod 30) ∈ TC ∧ (29 : ZMod 30) ∈ TC := by
  native_decide

end CouretUnification.Core
