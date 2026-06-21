import CouretUnification.Core.Classification63
import Mathlib.Tactic

namespace CouretUnification.Core.DefectProjection

/-!
# Projection du défaut δ₁₉ − δ₂₉

La classe 19 est un « fantôme C₄ » : 𝟙_TC(19) = 0 alors que 19 ∈ (ℤ/30ℤ)×.
Le défaut δ₁₉ − δ₂₉ mesure la différence de Fourier entre 19 et 29.

## Convention CRT (code Lean, depuis Characters30.lean)

  19 ↦ (ε=0, k=2),  29 ↦ (ε=1, k=0)

où (ε, k) ∈ C₂ × C₄ avec l’identification documentaire issue de Mod30.

⚠ NOTE : channel_bridge.py utilise une convention CRT DIFFÉRENTE
(générateurs 11, 7 au lieu de l’identification documentaire) :
  19 ↦ (0, 2),  29 ↦ (1, 2)  [convention channel_bridge]
  19 ↦ (0, 2),  29 ↦ (1, 0)  [convention Lean/Characters30]

Les deux sont des isomorphismes valides G₃₀ ≅ C₂ × C₄. Le contenu
mathématique est identique ; seul l’étiquetage des coordonnées C₄ diffère.

## Résultat (convention Lean)

  χ_{u,b}(19) = (−1)^b,   χ_{u,b}(29) = (−1)^u

Donc :
  defect(χ_{u,b}) = (−1)^b − (−1)^u

Le défaut s’annule si et seulement si u ≡ b (mod 2), c’est-à-dire exactement
sur 4 des 8 caractères. Les 4 autres portent toute la rupture, avec coefficient ±2.
-/

open Classification63

-- ═══════════════════════════════════════════
-- Masques pour les sous-ensembles à un seul élément
-- ═══════════════════════════════════════════

/-- Indice 5 = résidu 19, masque = 2⁵ = 32. -/
def mask19 : Nat := 32
/-- Indice 7 = résidu 29, masque = 2⁷ = 128. -/
def mask29 : Nat := 128

-- Vérification des coordonnées CRT
theorem crtCoord_19 : crtCoord 5 = (0, 2) := by native_decide
theorem crtCoord_29 : crtCoord 7 = (1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Coefficients de Fourier de δ₁₉ (indicatrice à un seul élément)
-- ═══════════════════════════════════════════

theorem f19_ch0 : subsetFourier mask19 0 = (1, 0) := by native_decide
theorem f19_ch1 : subsetFourier mask19 1 = (-1, 0) := by native_decide
theorem f19_ch2 : subsetFourier mask19 2 = (-1, 0) := by native_decide
theorem f19_ch3 : subsetFourier mask19 3 = (-1, 0) := by native_decide
theorem f19_ch4 : subsetFourier mask19 4 = (1, 0) := by native_decide
theorem f19_ch5 : subsetFourier mask19 5 = (-1, 0) := by native_decide
theorem f19_ch6 : subsetFourier mask19 6 = (1, 0) := by native_decide
theorem f19_ch7 : subsetFourier mask19 7 = (1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Coefficients de Fourier de δ₂₉
-- ═══════════════════════════════════════════

theorem f29_ch0 : subsetFourier mask29 0 = (1, 0) := by native_decide
theorem f29_ch1 : subsetFourier mask29 1 = (1, 0) := by native_decide
theorem f29_ch2 : subsetFourier mask29 2 = (1, 0) := by native_decide
theorem f29_ch3 : subsetFourier mask29 3 = (-1, 0) := by native_decide
theorem f29_ch4 : subsetFourier mask29 4 = (1, 0) := by native_decide
theorem f29_ch5 : subsetFourier mask29 5 = (-1, 0) := by native_decide
theorem f29_ch6 : subsetFourier mask29 6 = (-1, 0) := by native_decide
theorem f29_ch7 : subsetFourier mask29 7 = (-1, 0) := by native_decide

-- ═══════════════════════════════════════════
-- Défaut = F̂(δ₁₉) − F̂(δ₂₉)
-- ═══════════════════════════════════════════

/-- Coefficient de Fourier du défaut : F̂(δ₁₉)(χ) − F̂(δ₂₉)(χ). -/
def defect (χ : Fin 8) : GI :=
  let f19 := subsetFourier mask19 χ
  let f29 := subsetFourier mask29 χ
  (f19.1 - f29.1, f19.2 - f29.2)

-- Les 4 canaux D’ANNULATION (u ≡ b mod 2 dans la convention Lean)
theorem defect_ch0_zero : defect 0 = (0, 0) := by native_decide  -- (0,0) : u=0,b=0
theorem defect_ch3_zero : defect 3 = (0, 0) := by native_decide  -- (1,1) : u=1,b=1
theorem defect_ch4_zero : defect 4 = (0, 0) := by native_decide  -- (0,2) : u=0,b=2
theorem defect_ch5_zero : defect 5 = (0, 0) := by native_decide  -- (1,3) : u=1,b=3

-- Les 4 canaux NON NULS (u ≢ b mod 2 dans la convention Lean)
theorem defect_ch1_neg2 : defect 1 = (-2, 0) := by native_decide  -- (0,1) : u=0,b=1
theorem defect_ch2_neg2 : defect 2 = (-2, 0) := by native_decide  -- (0,3) : u=0,b=3
theorem defect_ch6_pos2 : defect 6 = (2, 0) := by native_decide   -- (1,0) : u=1,b=0
theorem defect_ch7_pos2 : defect 7 = (2, 0) := by native_decide   -- (1,2) : u=1,b=2

-- ═══════════════════════════════════════════
-- Propriétés structurelles
-- ═══════════════════════════════════════════

/-- Le défaut est réel (partie imaginaire = 0 sur tous les canaux). -/
theorem defect_real : (List.finRange 8).all (fun χ => (defect χ).2 == 0) = true := by
  native_decide

/-- Exactement 4 canaux portent le défaut. -/
theorem defect_support_card :
    (List.finRange 8).countP (fun χ => defect χ != (0, 0)) = 4 := by
  native_decide

/-- Le défaut se somme à zéro sur tous les caractères (orthogonalité de Parseval). -/
theorem defect_sum_zero :
    (List.finRange 8).foldl (fun acc χ => gi_add acc (defect χ)) gi_zero
      = (0, 0) := by
  native_decide

/-- Norme au carré du défaut : Σ|d_χ|² = 4·4 = 16. -/
def defectNormSq : Nat :=
  (List.finRange 8).foldl
    (fun acc χ => acc + ((defect χ).1 * (defect χ).1 + (defect χ).2 * (defect χ).2).natAbs) 0

theorem defect_norm_sq : defectNormSq = 16 := by native_decide

-- ═══════════════════════════════════════════
-- L’indicatrice de TC s’annule en 19
-- ═══════════════════════════════════════════

/-- 𝟙_TC(19) = 0 : le triplet de Couret ne contient pas 19. -/
theorem TC_vanishes_at_19 : bitSet couretMask 5 = false := by native_decide

/-- 𝟙_TC(29) = 1 : le triplet de Couret contient 29. -/
theorem TC_contains_29 : bitSet couretMask 7 = true := by native_decide

/-- 19 et 29 appartiennent à des secteurs C₂ différents. -/
theorem diff_C2 : (crtCoord 5).1 ≠ (crtCoord 7).1 := by native_decide

/-!
## Synthèse

Dans la convention CRT Lean/Characters30 :

| χ | dual (u,b) | F̂(δ₁₉) | F̂(δ₂₉) | Défaut | u≡b ? |
|---|-----------|---------|---------|--------|------|
| 0 | (0,0) | 1 | 1 | 0 | oui |
| 1 | (0,1) | −1 | 1 | −2 | non |
| 2 | (0,3) | −1 | 1 | −2 | non |
| 3 | (1,1) | −1 | −1 | 0 | oui |
| 4 | (0,2) | 1 | 1 | 0 | oui |
| 5 | (1,3) | −1 | −1 | 0 | oui |
| 6 | (1,0) | 1 | −1 | 2 | non |
| 7 | (1,2) | 1 | −1 | 2 | non |

Le défaut s’annule exactement sur les 4 caractères où u ≡ b (mod 2),
et vaut ±2 sur les 4 autres. Le défaut est entièrement réel.

**Formule** (convention Lean) :
  defect(χ_{u,b}) = (−1)^b − (−1)^u

**Équivalence avec channel_bridge.py** : le texte utilise les générateurs (11, 7),
où 29 ↦ (1, 2). Dans cette convention, le défaut vit sur les canaux u=1.
Dans la convention Lean (29 ↦ (1, 0)), il vit sur les canaux de
« désaccord de parité ». Les deux lectures sont correctes ; seul l’étiquetage
du générateur C₄ diffère.
-/

end CouretUnification.Core.DefectProjection
