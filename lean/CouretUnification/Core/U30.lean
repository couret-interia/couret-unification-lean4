import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CouretUnification.Core

/-!
# U30 — Structure finie de `(ℤ/30ℤ)×`

Ce fichier formalise le **noyau fini exact mod 30** utilisé dans le projet
Couret–Unification.

On y fixe :

- `U30` : les 8 unités modulo 30 ;
- `TC` : le triplet de Couret `{1, 11, 29}` ;
- quelques faits élémentaires mais structurants :
  - cardinalités,
  - inclusion `TC ⊆ U30`,
  - produit fantôme `11 * 29 = 19`,
  - non-fermeture multiplicative de `TC`,
  - image quadratique `{1, 19}`,
  - petite table CRT engendrée par `11` et `7`.

## Lecture conceptuelle

- `U30` est le **cadre multiplicatif exact**.
- `TC` est une **configuration privilégiée**, mais **pas un sous-groupe**.
- L’élément `19` apparaît comme **fantôme quadratique / multiplicatif** :
  il est produit par la dynamique interne, sans appartenir à `TC`.

Tout ici est **fini, exact, décidable**.
Aucune revendication analytique n’est faite dans ce fichier.

`RHClaimed = false`.
-/

/-- Les 8 unités de `ℤ/30ℤ`, dans l’ordre naturel croissant. -/
def U30 : Finset (ZMod 30) := {1, 7, 11, 13, 17, 19, 23, 29}

/-- Le triplet de Couret : sous-configuration distinguée de `U30`. -/
def TC : Finset (ZMod 30) := {1, 11, 29}

-- ═══════════════════════════════════════════════════════════
-- Cardinalités et inclusion de base
-- ═══════════════════════════════════════════════════════════

/-- `U30` contient exactement 8 éléments. -/
theorem card_U30 : U30.card = 8 := by native_decide

/-- Le triplet `TC` contient exactement 3 éléments. -/
theorem card_TC : TC.card = 3 := by native_decide

/-- Alias de card_TC. -/
theorem TC_card : TC.card = 3 := card_TC

/-- Le triplet de Couret est inclus dans l’ensemble des unités mod 30. -/
theorem TC_subset : TC ⊆ U30 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Produit fantôme : 11 · 29 = 19
-- ═══════════════════════════════════════════════════════════

/-- Produit fantôme central : `11 * 29 = 19` dans `ZMod 30`. -/
theorem phantom_product : (11 * 29 : ZMod 30) = 19 := by native_decide

/-- L’élément fantôme `19` n’appartient pas au triplet `TC`. -/
theorem phantom_not_in_TC : (19 : ZMod 30) ∉ TC := by native_decide

/--
Le triplet `TC` n’est pas stable par multiplication :
il ne forme donc pas un sous-groupe multiplicatif de `U30`.
-/
theorem TC_not_subgroup : ¬(∀ a b : ZMod 30, a ∈ TC → b ∈ TC → a * b ∈ TC) := by
  intro h
  have h1 := h 11 29 (by native_decide) (by native_decide)
  rw [phantom_product] at h1
  exact phantom_not_in_TC h1

-- ═══════════════════════════════════════════════════════════
-- Carrés dans U30
-- ═══════════════════════════════════════════════════════════

/-- Carré de `1`. -/
theorem sq_1  : (1  * 1  : ZMod 30) = 1  := by native_decide

/-- Carré de `7` : apparition du fantôme quadratique `19`. -/
theorem sq_7  : (7  * 7  : ZMod 30) = 19 := by native_decide

/-- Carré de `11`. -/
theorem sq_11 : (11 * 11 : ZMod 30) = 1  := by native_decide

/-- Carré de `29`. -/
theorem sq_29 : (29 * 29 : ZMod 30) = 1  := by native_decide

/-- Image quadratique de `U30` : ensemble des carrés des unités mod 30. -/
def squareImage : Finset (ZMod 30) := U30.image (fun x => x * x)

/-- Les seuls carrés des unités mod 30 sont `1` et `19`. -/
theorem squareImage_eq : squareImage = {1, 19} := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Ordres multiplicatifs et génération CRT
-- ═══════════════════════════════════════════════════════════

/-- `11` est d’ordre 2 modulo 30. -/
theorem order_11 : (11 : ZMod 30) ^ 2 = 1 := by native_decide

/-- `7` est d’ordre 4 modulo 30. -/
theorem order_7  : (7 : ZMod 30) ^ 4 = 1 := by native_decide

/--
Table CRT explicite :
les 8 éléments `11^a * 7^b` avec `a ∈ {0,1}` et `b ∈ {0,1,2,3}`
reconstituent exactement `U30`.
-/
theorem crt_table :
    ({(11 : ZMod 30)^0 * 7^0, 11^0 * 7^1, 11^0 * 7^2, 11^0 * 7^3,
      11^1 * 7^0, 11^1 * 7^1, 11^1 * 7^2, 11^1 * 7^3} : Finset (ZMod 30))
    = U30 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Fonctions indicatrices de structure
-- ═══════════════════════════════════════════════════════════

/-- Valeur de l’indicatrice d’Euler en 30, 210 et 2310. -/
theorem phi_30   : Nat.totient 30   = 8   := by native_decide
theorem phi_210  : Nat.totient 210  = 48  := by native_decide
theorem phi_2310 : Nat.totient 2310 = 480 := by native_decide

/--
`TC` a une cardinalité impaire.

Lecture symbolique : la configuration Couret minimale n’est pas
pairable en deux blocs de même taille.
-/
theorem TC_dim_odd : ¬ 2 ∣ TC.card := by native_decide

/-- `U30` a une cardinalité paire. -/
theorem U30_dim_even : 2 ∣ U30.card := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Caractérisation explicite de l’appartenance à U30
-- ═══════════════════════════════════════════════════════════

/--
Caractérisation exhaustive de l’appartenance à `U30`.

Cette forme est utile pour les réécritures élémentaires,
les preuves par cas, et les ponts vers des couches plus explicites.
-/
theorem mem_U30_iff (x : ZMod 30) :
    x ∈ U30 ↔
      x = 1 ∨ x = 7 ∨ x = 11 ∨ x = 13 ∨ x = 17 ∨ x = 19 ∨ x = 23 ∨ x = 29 := by
  simp [U30]

-- ═══════════════════════════════════════════════════════════
-- Garde épistémique
-- ═══════════════════════════════════════════════════════════

/-- Garde épistémique : ce fichier ne revendique aucun résultat sur RH/GRH. -/
def RHClaimed : Bool := false

/-- Vérification formelle de la garde épistémique. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Core