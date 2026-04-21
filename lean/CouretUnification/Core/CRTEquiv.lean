/-
  CouretUnification/Core/CRTEquiv.lean
  Équivalence CRT : G30 ≃ Fin 2 × Fin 4

  ALIGNÉ sur residueCoord de Characters30.lean (convention documentaire).

  Table réelle (de residueCoord) :
  (0,0) ↦ 1     (1,0) ↦ 29
  (0,1) ↦ 7     (1,1) ↦ 23
  (0,2) ↦ 19    (1,2) ↦ 11
  (0,3) ↦ 13    (1,3) ↦ 17

  0 sorry.

  NOTE : g30Coord et addCoord sont définis dans Characters30Bridge.
  Ce fichier les RÉUTILISE, il ne les redéfinit pas.
-/

import CouretUnification.Core.Characters30Bridge

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Fin 2 × Fin 4 → G30 (ALIGNÉ sur residueCoord)
-- ═══════════════════════════════════════════════════════════

/-- Inverse explicite, aligné sur la convention de Characters30.lean. -/
def coordToG30 : Fin 2 × Fin 4 → G30
  | (⟨0, _⟩, ⟨0, _⟩) => ⟨1,  1,  by decide, by decide⟩
  | (⟨0, _⟩, ⟨1, _⟩) => ⟨7,  13, by decide, by decide⟩
  | (⟨0, _⟩, ⟨2, _⟩) => ⟨19, 19, by decide, by decide⟩
  | (⟨0, _⟩, ⟨3, _⟩) => ⟨13, 7,  by decide, by decide⟩
  | (⟨1, _⟩, ⟨0, _⟩) => ⟨29, 29, by decide, by decide⟩
  | (⟨1, _⟩, ⟨1, _⟩) => ⟨23, 17, by decide, by decide⟩
  | (⟨1, _⟩, ⟨2, _⟩) => ⟨11, 11, by decide, by decide⟩
  | (⟨1, _⟩, ⟨3, _⟩) => ⟨17, 23, by decide, by decide⟩

-- ═══════════════════════════════════════════════════════════
-- §2. Équivalence G30 ≃ Fin 2 × Fin 4
-- ═══════════════════════════════════════════════════════════

def g30EquivCoord : G30 ≃ (Fin 2 × Fin 4) where
  toFun := g30Coord
  invFun := coordToG30
  left_inv := by
    intro g
    fin_cases g <;>
      simp [g30Coord, coordToG30, g30ToIdx, residueCoord] <;>
      decide
  right_inv := by
    intro p
    rcases p with ⟨e, k⟩
    fin_cases e <;> fin_cases k <;>
      simp [g30Coord, coordToG30, g30ToIdx, residueCoord] <;>
      decide

-- ═══════════════════════════════════════════════════════════
-- §3. Réindexation des sommes
-- ═══════════════════════════════════════════════════════════

theorem sum_reindex_g30 {β : Type*} [AddCommMonoid β] (F : G30 → β) :
    (∑ g : G30, F g) = ∑ p : Fin 2 × Fin 4, F (coordToG30 p) := by
  refine Fintype.sum_equiv g30EquivCoord
    (fun g : G30 => F g)
    (fun p : Fin 2 × Fin 4 => F (coordToG30 p))
    ?_
  intro g
  exact congrArg F ((g30EquivCoord.left_inv g).symm)

theorem sum_split_fin2_fin4 {β : Type*} [AddCommMonoid β]
    (H : Fin 2 × Fin 4 → β) :
    (∑ p : Fin 2 × Fin 4, H p) = ∑ e : Fin 2, ∑ k : Fin 4, H (e, k) := by
  rw [Fintype.sum_prod_type]

-- ═══════════════════════════════════════════════════════════
-- §4. Factorisation CRT (tautologie)
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_eq_CRT (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

end CouretUnification.Core
