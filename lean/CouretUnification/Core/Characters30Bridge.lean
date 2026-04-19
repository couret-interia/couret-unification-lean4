/-
  CouretUnification/Core/Characters30Bridge.lean
  Pont table concrète ↔ couche algébrique.
  Version v2 : 0 sorry visé.
  
  NOTE : `set_option maxHeartbeats 800000` pour les preuves par
  énumération finie (512 cas pour la multiplicativité).
-/

import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30

open scoped BigOperators

set_option maxHeartbeats 800000

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Pont G30 → Idx
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
-- §2. Caractère concret sur G30
-- ═══════════════════════════════════════════════════════════

def charOnG30 (χ : CharIdx) : FunG30 :=
  fun g => characterEval χ (g30ToIdx g)

noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹

-- ═══════════════════════════════════════════════════════════
-- §3. Multiplicativité (8 × 8 × 8 = 512 cas finis)
-- ═══════════════════════════════════════════════════════════

/-- χ(ab) = χ(a)χ(b) : vérifié par énumération exhaustive. -/
theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  fin_cases χ <;> fin_cases a <;> fin_cases b <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord,
          residueCoord, c2Phase, c4Phase, Complex.ext_iff,
          Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im] <;>
    norm_num

-- ═══════════════════════════════════════════════════════════
-- §4. Somme nulle des caractères non triviaux
-- ═══════════════════════════════════════════════════════════

/-- ∑ χ(g) = 0 pour χ non trivial : 7 cas × 8 termes. -/
theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  fin_cases χ <;>
    simp_all [charOnG30, g30ToIdx, characterEval, charCoord,
              residueCoord, c2Phase, c4Phase, Finset.sum_cons,
              Complex.ext_iff, Complex.I_re, Complex.I_im,
              Complex.add_re, Complex.add_im] <;>
    norm_num

-- ═══════════════════════════════════════════════════════════
-- §5. Propriétés élémentaires
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord,
        residueCoord, c2Phase, c4Phase]

theorem charOnG30_ne_zero (χ : CharIdx) :
    charOnG30 χ ≠ 0 := by
  intro h
  have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord,
          residueCoord, c2Phase, c4Phase] at h1

-- ═══════════════════════════════════════════════════════════
-- §6. Diagonalisation
-- ═══════════════════════════════════════════════════════════

/-- Réindexation locale (même preuve que Convolution30, non private). -/
private lemma sum_reindex_diag (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹) y) =
    ∑ g : G30, F g (g⁻¹ * x) := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by
      have := mul_left_cancel h; exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun y _ => by congr 1 <;> group)

/-- Version pointwise de la diagonalisation. -/
theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  -- ∑ y, K(xy⁻¹) χ(y) = (∑ g, K(g) χ(g⁻¹)) * χ(x)
  -- Étape 1 : réindexation g = xy⁻¹
  conv_lhs =>
    arg 2; ext y
    rw [show x * y⁻¹ = x * y⁻¹ from rfl] -- noop pour clarté
  rw [show (∑ y : G30, K (x * y⁻¹) * charOnG30 χ y) =
          ∑ g : G30, K g * charOnG30 χ (g⁻¹ * x) from by
    apply Finset.sum_nbij (fun y => x * y⁻¹)
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => by have := mul_left_cancel h; exact inv_injective this)
      (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
      (fun y _ => by simp only []; congr 1 <;> congr 1 <;> group)]
  -- Étape 2 : multiplicativité χ(g⁻¹ x) = χ(g⁻¹) χ(x)
  simp_rw [charOnG30_mul]
  -- Étape 3 : factoriser χ(x)
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul]

/-- Les caractères sont vecteurs propres de T_K. -/
theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  exact convolution_diag_pointwise K χ x

end CouretUnification.Core
