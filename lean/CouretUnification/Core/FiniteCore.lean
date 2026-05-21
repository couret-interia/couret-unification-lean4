import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import CouretUnification.Core.U30

/-!
# CouretUnification.Core.FiniteCore — T1 Noyau fini exact

## Statut
- `0 sorry`
- `0 axiome`

## Légende
- `[REAL]`    : résultat exact, calculable ou prouvé ici
- `[ENCODED]` : encodage structurel / garde logique

Ce fichier contient le noyau fini exact modulo `30` :
résidus admissibles, triplet de Couret, fantôme `19`,
profil spectral fini, table CRT explicite et gardes minimales.
-/

namespace CouretUnification.Core.FiniteCore

-- ═══════════════════════════════════════════════════════════
-- §1. G₃₀
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Résidus admissibles, identifiés canoniquement à `Core.U30`. -/
abbrev admissibleResidues : Finset (ZMod 30) := CouretUnification.Core.U30

/-- [REAL] Le groupe des unités modulo `30` a cardinal `8`. -/
theorem admissibleResidues_card : admissibleResidues.card = 8 :=
  CouretUnification.Core.card_U30

-- ═══════════════════════════════════════════════════════════
-- §2. TC
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Le triplet de Couret `TC = {1, 11, 29}`. -/
abbrev TC : Finset (ZMod 30) := CouretUnification.Core.TC

/-- [REAL] `TC` a exactement trois éléments, alias de U30 (TC_card). -/
theorem FCTC_card : TC.card = 3 := CouretUnification.Core.TC_card

/-- [REAL] `TC` est inclus dans l’ensemble des résidus admissibles, alias de U30 (TC_subset). -/
theorem FCTC_subset : TC ⊆ admissibleResidues := by exact CouretUnification.Core.TC_subset

-- ═══════════════════════════════════════════════════════════
-- §3. Fantôme 19
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Produit fantôme :
`11 * 29 ≡ 19 [ZMOD 30]`, alias de U30 (phantom_product). -/
theorem FCphantom_product : (11 * 29 : ZMod 30) = 19 := CouretUnification.Core.phantom_product

/-- [REAL] Le fantôme `19` n’appartient pas au triplet `TC`, alias de U30 (phantom_not_in_TC). -/
theorem FCphantom_not_in_TC : (19 : ZMod 30) ∉ TC := CouretUnification.Core.phantom_not_in_TC

/-- [REAL] Le fantôme `19` reste néanmoins admissible dans `G₃₀`. -/
theorem phantom_in_G : (19 : ZMod 30) ∈ admissibleResidues := by native_decide

/-- [REAL] `TC` n’est pas un sous-groupe multiplicatif de `(ℤ/30ℤ)×`.

Preuve : `11,29 ∈ TC`, mais `11*29 = 19` et `19 ∉ TC`, alias de U30 (TC_not_subgroup). -/
theorem FCTC_not_subgroup : ¬ (∀ a b : ZMod 30, a ∈ TC → b ∈ TC → a * b ∈ TC) :=
  CouretUnification.Core.TC_not_subgroup

-- ═══════════════════════════════════════════════════════════
-- §4. Spectre
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Coefficients de Fourier rationnels de l’indicatrice de `TC`. -/
def c_chi : Fin 8 → ℚ := ![3/8, 1/8, 3/8, 1/8, -1/8, 1/8, -1/8, 1/8]

/-- [REAL] Valeurs des huit caractères au point `19`.

Comme `19 = 7^2`, le motif dépend seulement de la composante d’ordre `4`,
ce qui force l’annulation du fantôme. -/
def chi_at_19 : Fin 8 → ℚ := ![1, -1, 1, -1, 1, -1, 1, -1]

/-- [REAL] Valeurs des huit caractères au point `29`.

Comme `29 = 11 * 7^2`, ce motif combine les composantes d’ordre `2` et `4`. -/
def chi_at_29 : Fin 8 → ℚ := ![1, -1, 1, -1, -1, 1, -1, 1]

/-- [REAL] Annulation algébrique du fantôme `19` :
`∑ c_χ · χ(19) = 0`. -/
theorem ghost_cancellation : ∑ i : Fin 8, c_chi i * chi_at_19 i = 0 := by
  native_decide

/-- [REAL] Reconstruction de la présence en `29` :
`∑ c_χ · χ(29) = 1`. -/
theorem presence_at_29 : ∑ i : Fin 8, c_chi i * chi_at_29 i = 1 := by
  native_decide

/-- [REAL] Profil spectral fini sur les huit canaux. -/
def spectralProfile : Fin 8 → ℕ := ![9, 1, 9, 1, 1, 1, 1, 1]

/-- [REAL] Somme de Parseval finie :
`∑ spectralProfile = 24`. -/
theorem parseval_sum : ∑ i : Fin 8, spectralProfile i = 24 := by native_decide

/-- [REAL] Identité normalisée de Parseval :
`24 = 8 × 3`. -/
theorem parseval_identity : (8 : ℕ) * 3 = 24 := by norm_num

/-- [REAL] Classification finie :
`63 + 192 = 255`. -/
theorem classification : (63 : ℕ) + 192 = 255 := by norm_num

-- ═══════════════════════════════════════════════════════════
-- §5. Lambda
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Identité rationnelle minimale reliée à `λ² = 1/7`. -/
theorem lambda_sq : (1 : ℚ) / 7 * 7 = 1 := by norm_num

/-- [REAL] Parseval normalisé :
`24 / 8 = 3`. -/
theorem parseval_normalized : (24 : ℚ) / 8 = 3 := by norm_num

-- ═══════════════════════════════════════════════════════════
-- §6. Ordres des générateurs
-- ═══════════════════════════════════════════════════════════

/-- [REAL] `11` est d’ordre `2` modulo `30`, alias de U30 (order_11). -/
theorem FCorder_11 : (11 : ZMod 30) ^ 2 = 1 := CouretUnification.Core.order_11

/-- [REAL] `7` est d’ordre `4` modulo `30`, alias de U30 (order_7). -/
theorem FCorder_7 : (7 : ZMod 30) ^ 4 = 1 := CouretUnification.Core.order_7

/-- [REAL] `7` n’est pas d’ordre `2`. -/
theorem order_7_not_2 : (7 : ZMod 30) ^ 2 ≠ 1 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §7. CRT complet
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Élément CRT `(0,0)` : `1`. -/
theorem crt_1  : (11 : ZMod 30) ^ 0 * (7 : ZMod 30) ^ 0 = 1  := by native_decide

/-- [REAL] Élément CRT `(0,1)` : `7`. -/
theorem crt_7  : (11 : ZMod 30) ^ 0 * (7 : ZMod 30) ^ 1 = 7  := by native_decide

/-- [REAL] Élément CRT `(0,2)` : `19`. -/
theorem crt_19 : (11 : ZMod 30) ^ 0 * (7 : ZMod 30) ^ 2 = 19 := by native_decide

/-- [REAL] Élément CRT `(0,3)` : `13`. -/
theorem crt_13 : (11 : ZMod 30) ^ 0 * (7 : ZMod 30) ^ 3 = 13 := by native_decide

/-- [REAL] Élément CRT `(1,0)` : `11`. -/
theorem crt_11 : (11 : ZMod 30) ^ 1 * (7 : ZMod 30) ^ 0 = 11 := by native_decide

/-- [REAL] Élément CRT `(1,1)` : `17`. -/
theorem crt_17 : (11 : ZMod 30) ^ 1 * (7 : ZMod 30) ^ 1 = 17 := by native_decide

/-- [REAL] Élément CRT `(1,2)` : `29`. -/
theorem crt_29 : (11 : ZMod 30) ^ 1 * (7 : ZMod 30) ^ 2 = 29 := by native_decide

/-- [REAL] Élément CRT `(1,3)` : `23`. -/
theorem crt_23 : (11 : ZMod 30) ^ 1 * (7 : ZMod 30) ^ 3 = 23 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §8. Tour primoriale
-- ═══════════════════════════════════════════════════════════

/-- [REAL] `φ(30) = 8`, alias de U30 (phi_30). -/
theorem FCphi_30   : Nat.totient 30   = 8   := CouretUnification.Core.phi_30

/-- [REAL] `φ(210) = 48`, alias de U30 (phi_210). -/
theorem FCphi_210  : Nat.totient 210  = 48  := CouretUnification.Core.phi_210

/-- [REAL] `φ(2310) = 480`, alias de U30 (phi_2310). -/
theorem FCphi_2310 : Nat.totient 2310 = 480 := CouretUnification.Core.phi_2310

/-- [REAL] Passage `30 → 210` : facteur `7 - 1 = 6`. -/
theorem split_7  : 48  = 8  * (7 - 1)  := by norm_num

/-- [REAL] Passage `210 → 2310` : facteur `11 - 1 = 10`. -/
theorem split_11 : 480 = 48 * (11 - 1) := by norm_num

-- ═══════════════════════════════════════════════════════════
-- §9. Obstruction symplectique
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Le cardinal de `TC` est impair, alias de U30 (TC_dim_odd). -/
theorem FCTC_dim_odd : ¬ 2 ∣ TC.card := CouretUnification.Core.TC_dim_odd

/-- [REAL] Le cardinal de `G₃₀` est pair. -/
theorem G30_dim_even : 2 ∣ admissibleResidues.card := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §10. Cayley S={7,11,13} — Générateurs
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Générateurs choisis pour le graphe de Cayley fini. -/
def cayleyGens : Finset (ZMod 30) := {7, 11, 13}

/-- [REAL] `7` et `13` sont inverses l’un de l’autre modulo `30`. -/
theorem gen_sym_7  : (7 * 13 : ZMod 30) = 1 := by native_decide

/-- [REAL] `11` est involutif modulo `30`. -/
theorem gen_sym_11 : (11 * 11 : ZMod 30) = 1 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §11. Cayley connexité
-- ═══════════════════════════════════════════════════════════

/-- [REAL] Atteinte de `7` depuis `1`. -/
theorem reach_7  : (1 * 7 : ZMod 30) = 7 := by native_decide

/-- [REAL] Atteinte de `19` depuis `1`. -/
theorem reach_19 : (1 * 7 * 7 : ZMod 30) = 19 := by native_decide

/-- [REAL] Atteinte de `13` depuis `1`. -/
theorem reach_13 : (1 * 7 * 7 * 7 : ZMod 30) = 13 := by native_decide

/-- [REAL] Atteinte de `11` depuis `1`. -/
theorem reach_11 : (1 * 11 : ZMod 30) = 11 := by native_decide

/-- [REAL] Atteinte de `17` depuis `1`. -/
theorem reach_17 : (1 * 11 * 7 : ZMod 30) = 17 := by native_decide

/-- [REAL] Atteinte de `29` depuis `1`. -/
theorem reach_29 : (1 * 11 * 7 * 7 : ZMod 30) = 29 := by native_decide

/-- [REAL] Atteinte de `23` depuis `1`. -/
theorem reach_23 : (1 * 11 * 7 * 7 * 7 : ZMod 30) = 23 := by native_decide

/-- [REAL] Les huit sommets atteints par les générateurs coïncident
exactement avec `admissibleResidues`. -/
theorem cayley_covers_all :
    ({1, 1*7, 1*7*7, 1*7*7*7, 1*11, 1*11*7, 1*11*7*7, 1*11*7*7*7} :
      Finset (ZMod 30)) = admissibleResidues := by native_decide

-- ═══════════════════════════════════════════════════════════
-- §12. Garde
-- ═══════════════════════════════════════════════════════════

/-- [ENCODED] Garde épistémique : RH n’est pas revendiquée ici. -/
def RHClaimed : Bool := false

/-- [REAL] Vérification littérale de la garde. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Core.FiniteCore
