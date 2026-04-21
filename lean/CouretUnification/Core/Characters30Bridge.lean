/-
  CouretUnification/Core/Characters30Bridge.lean
  Version v35.1 — Fermeture complète du bridge caractères.
  Sorry visés : 0.  RHClaimed = false.

  NOTE : ce fichier ne doit PAS importer CRTEquiv (cycle).
  NOTE : CharacterLemmas fournit sum_char_eq_zero_of_ne_one.
-/

import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharacterLemmas

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
-- §3. Coordonnées CRT (définies localement)
-- ═══════════════════════════════════════════════════════════

def g30Coord (g : G30) : Fin 2 × Fin 4 :=
  residueCoord (g30ToIdx g)

def addCoord (p q : Fin 2 × Fin 4) : Fin 2 × Fin 4 :=
  (p.1 + q.1, p.2 + q.2)

-- ═══════════════════════════════════════════════════════════
-- §4. Puissances de I (ring ne gère pas I² = -1)
-- ═══════════════════════════════════════════════════════════

-- Pairs
private lemma Ip6  : Complex.I ^ (6:ℕ)  = -1 := by
  have : Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip10 : Complex.I ^ (10:ℕ) = -1 := by
  have : Complex.I ^ 10 = (Complex.I ^ 2) ^ 5 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip12 : Complex.I ^ (12:ℕ) = 1  := by
  have : Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 := by ring
  rw [this, Complex.I_sq]; norm_num
private lemma Ip18 : Complex.I ^ (18:ℕ) = -1 := by
  have : Complex.I ^ 18 = (Complex.I ^ 2) ^ 9 := by ring
  rw [this, Complex.I_sq]; norm_num

-- Impairs
private lemma Ip3  : Complex.I ^ (3:ℕ)  = -Complex.I := by
  have : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  rw [this, Complex.I_sq]; ring
private lemma Ip7  : Complex.I ^ (7:ℕ)  = -Complex.I := by
  have : Complex.I ^ 7 = (Complex.I ^ 2) ^ 3 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num; ring
private lemma Ip9  : Complex.I ^ (9:ℕ)  = Complex.I := by
  have : Complex.I ^ 9 = (Complex.I ^ 2) ^ 4 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num; ring
private lemma Ip15 : Complex.I ^ (15:ℕ) = -Complex.I := by
  have : Complex.I ^ 15 = (Complex.I ^ 2) ^ 7 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num; ring

-- ═══════════════════════════════════════════════════════════
-- §5. g30Coord est un morphisme de groupe
-- ═══════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
theorem g30Coord_mul (a b : G30) :
    g30Coord (a * b) = addCoord (g30Coord a) (g30Coord b) := by
  fin_cases a <;> fin_cases b <;>
    simp [g30Coord, g30ToIdx, residueCoord, addCoord] <;>
    decide

-- ═══════════════════════════════════════════════════════════
-- §6. Dépliage tautologique
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_factor (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

-- ═══════════════════════════════════════════════════════════
-- §7. Multiplicativité des phases
-- ═══════════════════════════════════════════════════════════

theorem c2Phase_mul_right (m : Fin 2) (e₁ e₂ : Fin 2) :
    c2Phase m (e₁ + e₂) = c2Phase m e₁ * c2Phase m e₂ := by
  fin_cases m <;> fin_cases e₁ <;> fin_cases e₂ <;>
    simp [c2Phase] <;> ring

set_option maxHeartbeats 400000 in
theorem c4Phase_mul_right (n : Fin 4) (k₁ k₂ : Fin 4) :
    c4Phase n (k₁ + k₂) = c4Phase n k₁ * c4Phase n k₂ := by
  fin_cases n <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp only [c4Phase, Complex.I_sq, Ip3, Ip6, Ip7, Ip9, Ip10, Ip12, Ip15, Ip18,
               pow_zero, pow_one, neg_neg, one_mul, mul_one, neg_mul, mul_neg] <;>
    ring

-- ═══════════════════════════════════════════════════════════
-- §8. Multiplicativité du caractère
-- ═══════════════════════════════════════════════════════════

theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  simp only [charOnG30_factor]
  rw [g30Coord_mul]
  simp only [addCoord]
  rw [c2Phase_mul_right, c4Phase_mul_right]

-- ═══════════════════════════════════════════════════════════
-- §9. Élévation en MonoidHom
-- ═══════════════════════════════════════════════════════════

def charOnG30AsHom (χ : CharIdx) : G30 →* ℂ where
  toFun := charOnG30 χ
  map_one' := by
    fin_cases χ <;>
      simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord,
            c2Phase, c4Phase]
  map_mul' := charOnG30_mul χ

-- ═══════════════════════════════════════════════════════════
-- §10. Somme nulle des caractères non triviaux
-- ═══════════════════════════════════════════════════════════

theorem charOnG30AsHom_ne_one (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    charOnG30AsHom χ ≠ 1 := by
  fin_cases χ
  · exact absurd rfl hχ
  all_goals (
    intro h
    have h7 := MonoidHom.ext_iff.mp h ⟨7, 13, by decide, by decide⟩
    simp only [charOnG30AsHom, MonoidHom.coe_mk, OneHom.coe_mk,
               MonoidHom.one_apply,
               charOnG30, g30ToIdx, characterEval, charCoord,
               residueCoord, c2Phase, c4Phase,
               Complex.I_sq, Ip3, pow_zero, pow_one] at h7
    -- h7 is now a false equation; split into re/im to close
    have := h7
    rw [Complex.ext_iff] at this
    simp [Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
          Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.zero_re, Complex.zero_im] at this
  )

theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  have hne : charOnG30AsHom χ ≠ 1 := charOnG30AsHom_ne_one χ hχ
  have key := sum_char_eq_zero_of_ne_one (charOnG30AsHom χ) hne
  convert key using 1
  apply Finset.sum_congr rfl
  intro g _; rfl

-- ═══════════════════════════════════════════════════════════
-- §11. Export (compatibilité v32)
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
-- §12. Réindexation (copie locale)
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
-- §13. Diagonalisation (conservée de v32)
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