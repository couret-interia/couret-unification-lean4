/-
  CouretUnification/Core/CRTEquiv.lean
  Équivalence CRT : G30 ≃ Fin 2 × Fin 4

  ALIGNÉ sur residueCoord de Characters30.lean (convention documentaire).
  NOTE : cette convention N'EST PAS 11ᵃ·7ᵇ pour la composante C₂.

  Table réelle (de residueCoord) :
  (0,0) ↦ 1     (1,0) ↦ 29
  (0,1) ↦ 7     (1,1) ↦ 23
  (0,2) ↦ 19    (1,2) ↦ 11
  (0,3) ↦ 13    (1,3) ↦ 17

  0 sorry visé (charOnG30_eq_CRT = tautologie).
-/

import CouretUnification.Core.Characters30Bridge

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. G30 → Fin 2 × Fin 4 via residueCoord existant
-- ═══════════════════════════════════════════════════════════

/-- Coordonnées CRT sur G30, obtenues par composition
    g30ToIdx (du bridge) puis residueCoord (de Characters30). -/
def g30Coord (g : G30) : Fin 2 × Fin 4 :=
  residueCoord (g30ToIdx g)

-- ═══════════════════════════════════════════════════════════
-- §2. Fin 2 × Fin 4 → G30 (ALIGNÉ sur residueCoord)
-- ═══════════════════════════════════════════════════════════

/-- Inverse explicite, aligné sur la convention de Characters30.lean. -/
def coordToG30 : Fin 2 × Fin 4 → G30
  | (⟨0, _⟩, ⟨0, _⟩) => ⟨1,  1,  by decide, by decide⟩   -- residueCoord 0 = (0,0)
  | (⟨0, _⟩, ⟨1, _⟩) => ⟨7,  13, by decide, by decide⟩   -- residueCoord 1 = (0,1)
  | (⟨0, _⟩, ⟨2, _⟩) => ⟨19, 19, by decide, by decide⟩   -- residueCoord 5 = (0,2)
  | (⟨0, _⟩, ⟨3, _⟩) => ⟨13, 7,  by decide, by decide⟩   -- residueCoord 3 = (0,3)
  | (⟨1, _⟩, ⟨0, _⟩) => ⟨29, 29, by decide, by decide⟩   -- residueCoord 7 = (1,0)
  | (⟨1, _⟩, ⟨1, _⟩) => ⟨23, 17, by decide, by decide⟩   -- residueCoord 6 = (1,1)
  | (⟨1, _⟩, ⟨2, _⟩) => ⟨11, 11, by decide, by decide⟩   -- residueCoord 2 = (1,2)
  | (⟨1, _⟩, ⟨3, _⟩) => ⟨17, 23, by decide, by decide⟩   -- residueCoord 4 = (1,3)

-- ═══════════════════════════════════════════════════════════
-- §3. Équivalence G30 ≃ Fin 2 × Fin 4
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
-- §4. Réindexation des sommes
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
-- §5. Factorisation CRT (cible)
--     charCoord et residueCoord sont EXISTANTS (Characters30.lean)
-- ═══════════════════════════════════════════════════════════

/-- χ(g) = c2Phase(m, ε) · c4Phase(n, k)
    où (m,n) = charCoord χ, (ε,k) = g30Coord g = residueCoord(g30ToIdx g).
    C'est exactement characterEval, reformulé via le bridge. -/
theorem charOnG30_eq_CRT (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  -- Tautologie : characterEval est DÉFINI comme c2Phase · c4Phase,
  -- et g30Coord est DÉFINI comme residueCoord ∘ g30ToIdx.
  -- Donc charOnG30 χ g = characterEval χ (g30ToIdx g)
  --                    = c2Phase (charCoord χ).1 (residueCoord (g30ToIdx g)).1
  --                    * c4Phase (charCoord χ).2 (residueCoord (g30ToIdx g)).2
  --                    = c2Phase m ε * c4Phase n k  (par def g30Coord)
  simp only [charOnG30, g30Coord, characterEval]
  -- Fallback si simp ne déplie pas tout :
  -- unfold charOnG30 g30Coord characterEval; rfl

end CouretUnification.Core
