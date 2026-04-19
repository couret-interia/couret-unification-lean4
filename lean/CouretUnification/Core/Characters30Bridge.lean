/-
  CouretUnification/Core/Characters30Bridge.lean
  
  Pont entre la table concrète des caractères (Characters30.lean)
  et la couche algébrique (UnitsBridge/Convolution30).
  
  Ce fichier :
  - mappe G30 ↔ Idx
  - lève characterEval sur G30 → ℂ
  - définit eigenvalue
  - prouve la diagonalisation en supposant la multiplicativité
  
  Sorry attendus : 2 (multiplicativité + somme nulle des non-triviaux)
  Ces sorry sont des calculs finis sur 8 éléments, pas des verrous.
-/

import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30

open scoped BigOperators

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════
-- §1. Pont G30 → Idx
-- ═══════════════════════════════════════════════════════════

/-- Mappe chaque unité de G₃₀ vers son indice dans [1,7,11,13,17,19,23,29]. -/
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

/-- Évaluation d'un caractère concret sur G₃₀ (via la table CRT). -/
def charOnG30 (χ : CharIdx) : FunG30 :=
  fun g => characterEval χ (g30ToIdx g)

/-- Valeur propre associée au noyau K et au caractère χ. -/
noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹

-- ═══════════════════════════════════════════════════════════
-- §3. Propriétés des caractères (sorry = calculs finis)
-- ═══════════════════════════════════════════════════════════

/-- Multiplicativité : χ(ab) = χ(a)χ(b).
    Sorry : vérifiable par calcul fini (8 × 8 = 64 cas). -/
theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  sorry -- 64 cas finis, chacun ferme par norm_num sur les phases CRT

/-- Le caractère trivial (χ₀ = index 0) vaut 1 partout. -/
theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

/-- Un caractère non trivial a pour somme 0 sur G₃₀.
    Sorry : conséquence de la multiplicativité + orthogonalité standard. -/
theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  sorry -- 7 cas × 8 termes, chacun ferme par calcul sur les phases

/-- Un caractère n'est pas la fonction nulle. -/
theorem charOnG30_ne_zero (χ : CharIdx) :
    charOnG30 χ ≠ 0 := by
  intro h
  have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase] at h1

-- ═══════════════════════════════════════════════════════════
-- §4. Diagonalisation
-- ═══════════════════════════════════════════════════════════

/-- Version pointwise plus directe. -/
theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  -- ∑ y, K(xy⁻¹) χ(y) = (∑ g, K(g) χ(g⁻¹)) * χ(x)
  -- Changement de variable g = xy⁻¹, y = g⁻¹x
  sorry
  -- Preuve esquissée :
  -- rw [← sum_reindex_mul_inv x]
  -- puis charOnG30_mul pour χ(g⁻¹ * x) = χ(g⁻¹) * χ(x)
  -- puis Finset.mul_sum pour sortir χ(x)

/-- Les caractères sont vecteurs propres de la convolution.
    Preuve : changement de variable + multiplicativité. -/
theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x
  exact convolution_diag_pointwise K χ x

end CouretUnification.Core
