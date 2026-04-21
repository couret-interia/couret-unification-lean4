/-
  CouretUnification/Core/Characters30Bridge.lean
  Version v35.1 — Fermeture complète du bridge caractères.

  Architecture en 4 lemmes :
    1. g30Coord_mul       — compatibilité de loi (64 cas, decide)
    2. charOnG30_factor   — dépliage tautologique (simp)
    3. charOnG30_mul      — multiplicativité de χ (composition)
    4. sum_charOnG30_ne_trivial — orthogonalité (structurel)

  Sorry visés : 0.
  RHClaimed = false.

  NOTE : ce fichier ne doit PAS importer CRTEquiv (cycle).
  g30Coord et addCoord sont définis localement ici.
  CRTEquiv les réutilise via import de ce fichier.
-/

import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Pont G30 → Idx (conservé de v32)
-- ═══════════════════════════════════════════════════════════

def g30ToIdx (u : G30) : Idx :=
  if (u : ZMod 30) = 1  then ⟨0, by omega⟩
  else if (u : ZMod 30) = 7  then ⟨1, by omega⟩
  else if (u : ZMod 30) = 11 then ⟨2, by omega⟩
  else if (u : ZMod 30) = 13 then ⟨3, by omega⟩
  else if (u : ZMod 30) = 17 then ⟨4, by omega⟩
  else if (u : ZMod 30) = 19 then ⟨5, by omega⟩
  else if (u : ZMod 30) = 23 then ⟨6, by omega⟩
  else ⟨7, by omega⟩

-- ═══════════════════════════════════════════════════════════
-- §2. Caractère concret sur G30 (conservé de v32)
-- ═══════════════════════════════════════════════════════════

def charOnG30 (χ : CharIdx) : FunG30 :=
  fun g => characterEval χ (g30ToIdx g)

noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹

-- ═══════════════════════════════════════════════════════════
-- §3. Coordonnées CRT (définies localement — pas d'import CRTEquiv)
-- ═══════════════════════════════════════════════════════════

/-- Coordonnées CRT sur G30 : composition g30ToIdx puis residueCoord. -/
def g30Coord (g : G30) : Fin 2 × Fin 4 :=
  residueCoord (g30ToIdx g)

/-- Addition composante par composante dans Fin 2 × Fin 4. -/
def addCoord (p q : Fin 2 × Fin 4) : Fin 2 × Fin 4 :=
  (p.1 + q.1, p.2 + q.2)

-- ═══════════════════════════════════════════════════════════
-- §4. LEMME PIVOT : g30Coord est un morphisme de groupe
-- ═══════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
theorem g30Coord_mul (a b : G30) :
    g30Coord (a * b) = addCoord (g30Coord a) (g30Coord b) := by
  fin_cases a <;> fin_cases b <;>
    simp [g30Coord, g30ToIdx, residueCoord, addCoord] <;>
    decide

-- ═══════════════════════════════════════════════════════════
-- §5. DÉPLIAGE TAUTOLOGIQUE
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_factor (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

-- ═══════════════════════════════════════════════════════════
-- §6. MULTIPLICATIVITÉ DES PHASES
-- ═══════════════════════════════════════════════════════════

theorem c2Phase_mul_right (m : Fin 2) (e₁ e₂ : Fin 2) :
    c2Phase m (e₁ + e₂) = c2Phase m e₁ * c2Phase m e₂ := by
  fin_cases m <;> fin_cases e₁ <;> fin_cases e₂ <;>
    simp [c2Phase] <;> ring

theorem c4Phase_mul_right (n : Fin 4) (k₁ k₂ : Fin 4) :
    c4Phase n (k₁ + k₂) = c4Phase n k₁ * c4Phase n k₂ := by
  fin_cases n <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp [c4Phase] <;> ring

-- ═══════════════════════════════════════════════════════════
-- §7. MULTIPLICATIVITÉ DU CARACTÈRE
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  simp only [charOnG30_factor]
  rw [g30Coord_mul]
  simp only [addCoord]
  rw [c2Phase_mul_right, c4Phase_mul_right]
  ring

-- ═══════════════════════════════════════════════════════════
-- §8. ÉLÉVATION EN MONOIDHOM
-- ═══════════════════════════════════════════════════════════

def charOnG30AsHom (χ : CharIdx) : G30 →* ℂ where
  toFun := charOnG30 χ
  map_one' := by
    simp only [charOnG30_factor]
    have h1 : g30Coord (1 : G30) = ((0 : Fin 2), (0 : Fin 4)) := by
      simp [g30Coord, g30ToIdx, residueCoord]; decide
    rw [h1]; simp [c2Phase, c4Phase]
  map_mul' := charOnG30_mul χ

-- ═══════════════════════════════════════════════════════════
-- §9. SOMME NULLE DES CARACTÈRES NON TRIVIAUX
-- ═══════════════════════════════════════════════════════════

theorem charOnG30AsHom_trivial_eq_one :
    charOnG30AsHom ⟨0, by omega⟩ = 1 := by
  ext g
  simp [charOnG30AsHom, charOnG30_factor, charCoord, c2Phase, c4Phase]

theorem charOnG30AsHom_ne_one (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    charOnG30AsHom χ ≠ 1 := by
  intro h
  apply hχ
  fin_cases χ <;> simp_all [charOnG30AsHom, MonoidHom.ext_iff] <;>
    (try { exfalso; apply hχ; rfl }) <;>
    (try {
      have := congr_fun (MonoidHom.ext_iff.mp h) ⟨7, 13, by decide, by decide⟩
      simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
            c2Phase, c4Phase] at this
    })

theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  have hne : charOnG30AsHom χ ≠ 1 := charOnG30AsHom_ne_one χ hχ
  have key := sum_char_eq_zero_of_ne_one (charOnG30AsHom χ) hne
  convert key using 1
  apply Finset.sum_congr rfl
  intro g _
  rfl

-- ═══════════════════════════════════════════════════════════
-- §10. EXPORT (compatibilité v32)
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
        c2Phase, c4Phase]

theorem charOnG30_ne_zero (χ : CharIdx) :
    charOnG30 χ ≠ 0 := by
  intro h
  have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
          c2Phase, c4Phase] at h1

-- ═══════════════════════════════════════════════════════════
-- §11. Réindexation (copie locale, car private dans Convolution30)
-- ═══════════════════════════════════════════════════════════

private lemma sum_reindex_mul_inv' (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by
      have := mul_left_cancel h
      exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

-- ═══════════════════════════════════════════════════════════
-- §12. DIAGONALISATION (conservée de v32)
-- ═══════════════════════════════════════════════════════════

theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  calc ∑ y : G30, K (x * y⁻¹) * charOnG30 χ y
      = ∑ g : G30, K g * charOnG30 χ (g⁻¹ * x) := by
          rw [← sum_reindex_mul_inv' x (fun g => K g * charOnG30 χ (g⁻¹ * x))]
          apply Finset.sum_congr rfl; intro y _
          congr 1; congr 1; group
    _ = ∑ g : G30, K g * (charOnG30 χ g⁻¹ * charOnG30 χ x) := by
          apply Finset.sum_congr rfl; intro g _
          congr 1; exact charOnG30_mul χ g⁻¹ x
    _ = (∑ g : G30, K g * charOnG30 χ g⁻¹) * charOnG30 χ x := by
          simp_rw [← mul_assoc]; rw [← Finset.sum_mul]

theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x
  exact convolution_diag_pointwise K χ x

end CouretUnification.Core
