/-
Copyright (c) 2026 Alexandre Couret. Tous droits réservés.

# Core/SophieGermainHecke.lean — SG-shift mod 30

Noyau fini pour le décalage de Sophie Germain

    T_SG : r ↦ 2r + 1   (mod 30)

sur les huit classes admissibles modulo 30.

Ce fichier fournit uniquement des faits finis, décidables, indépendants de
l'analyse globale :

  * les trois sources Sophie Germain : 11, 23, 29 ;
  * leurs images par T_SG : 11 → 23, 23 → 17, 29 → 29 ;
  * les cinq sorties inactives : 1 → 3, 7 → 15, 13 → 27, 17 → 5, 19 → 9 ;
  * deux petites matrices d'adjacence :
      - restriction aux sources SG {11, 23, 29} ;
      - bloc en chaîne {11, 17, 23}, utilisé par `Residue/SGShiftSqrt2.lean` ;
  * un caractère fini `epsilon30` modulo 30, absent du dépôt d'accueil au
    moment de l'intégration.

Statut : [D] fini / décidable.
Aucun `sorry`, aucun `axiom`, aucun `admit`.
RHClaimed = false.
-/

import CouretUnification.Core.Mod30
import CouretUnification.Core.SophieGermainMod30
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CouretUnification
namespace Core
namespace SophieGermainHecke

/-! ## Section 1 — Décalage de Sophie Germain modulo 30 -/

/-- Application de Sophie Germain sur les résidus modulo 30. -/
def heckeT2 (r : Nat) : Nat :=
  (2 * r + 1) % 30

/-- Les trois classes sources admissibles pour les nombres de Sophie Germain. -/
def sgSourceResidue : Fin 3 → Nat
  | ⟨0, _⟩ => 11
  | ⟨1, _⟩ => 23
  | ⟨2, _⟩ => 29

/-- Les trois nœuds de la chaîne non triviale 11 → 23 → 17.  L'ordre choisi
    est celui du bloc matriciel utilisé dans `SGShiftSqrt2.lean` :
    0 ↦ 11, 1 ↦ 17, 2 ↦ 23. -/
def sgChainResidue : Fin 3 → Nat
  | ⟨0, _⟩ => 11
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 23

/-- Chaque source SG appartient bien à la liste `sgResidues = [11, 23, 29]`. -/
theorem sgSourceResidue_mem (i : Fin 3) :
    sgSourceResidue i ∈ sgResidues := by
  fin_cases i <;> decide

/-! ## Section 2 — Images actives et sorties inactives -/

/-- Branche active : 11 → 23. -/
theorem heckeT2_active_11 : heckeT2 11 = 23 := by
  native_decide

/-- Branche active : 23 → 17.  La cible reste dans U₃₀, mais sort des
    sources SG {11, 23, 29}. -/
theorem heckeT2_active_23 : heckeT2 23 = 17 := by
  native_decide

/-- Branche active : 29 → 29, point fixe. -/
theorem heckeT2_active_29 : heckeT2 29 = 29 := by
  native_decide

/-- Les images des trois sources SG restent dans les huit classes admissibles
    modulo 30. -/
theorem heckeT2_sgSource_mem_R30 (i : Fin 3) :
    heckeT2 (sgSourceResidue i) ∈ admissibleResidues := by
  fin_cases i <;> decide

/-- Sortie inactive : 1 → 3, donc hors de U₃₀. -/
theorem heckeT2_inactive_1 : heckeT2 1 = 3 := by
  native_decide

/-- Sortie inactive : 7 → 15, donc hors de U₃₀. -/
theorem heckeT2_inactive_7 : heckeT2 7 = 15 := by
  native_decide

/-- Sortie inactive : 13 → 27, donc hors de U₃₀. -/
theorem heckeT2_inactive_13 : heckeT2 13 = 27 := by
  native_decide

/-- Sortie inactive : 17 → 5, donc hors de U₃₀. -/
theorem heckeT2_inactive_17 : heckeT2 17 = 5 := by
  native_decide

/-- Sortie inactive : 19 → 9, donc hors de U₃₀. -/
theorem heckeT2_inactive_19 : heckeT2 19 = 9 := by
  native_decide

/-- Les cinq sorties inactives ne sont pas dans les huit classes admissibles
    modulo 30. -/
theorem heckeT2_inactive_not_R30 :
    heckeT2 1 ∉ admissibleResidues ∧
    heckeT2 7 ∉ admissibleResidues ∧
    heckeT2 13 ∉ admissibleResidues ∧
    heckeT2 17 ∉ admissibleResidues ∧
    heckeT2 19 ∉ admissibleResidues := by
  decide

/-! ## Section 3 — Matrices finies d'adjacence -/

/-- Matrice de `T_SG` restreinte aux sources SG {11, 23, 29}.

    Convention : ligne = source, colonne = cible dans le même espace source.
    Ainsi 11 → 23 donne l'entrée `(0,1) = 1`, 29 → 29 donne `(2,2) = 1`,
    et 23 → 17 est une sortie hors du sous-espace source, donc non encodée. -/
def heckeT2_SG_matrix : Fin 3 → Fin 3 → Nat
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | _, _ => 0

/-- Entrée matricielle correspondant à 11 → 23. -/
theorem heckeT2_SG_matrix_11_23 :
    heckeT2_SG_matrix ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by
  decide

/-- Entrée matricielle correspondant au point fixe 29 → 29. -/
theorem heckeT2_SG_matrix_29_29 :
    heckeT2_SG_matrix ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 := by
  decide

/-- La branche 23 → 17 sort de l'espace source {11, 23, 29}. -/
theorem heckeT2_SG_matrix_23_no_internal_target :
    heckeT2_SG_matrix ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 ∧
    heckeT2_SG_matrix ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
    heckeT2_SG_matrix ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 := by
  decide

/-- Matrice orientée du bloc en chaîne sur les nœuds ordonnés
    `(11, 17, 23)`.  Elle encode 11 → 23 et 23 → 17.

    Sa symétrisation `(A + Aᵀ)/2` est exactement le bloc rationnel étudié
    dans `Residue/SGShiftSqrt2.lean`, d'où l'invariant algébrique 1/√2. -/
def sgChainHeckeMatrix : Fin 3 → Fin 3 → Nat
  | ⟨0, _⟩, ⟨2, _⟩ => 1   -- 11 → 23
  | ⟨2, _⟩, ⟨1, _⟩ => 1   -- 23 → 17
  | _, _ => 0

/-- Entrée de chaîne : 11 → 23. -/
theorem sgChainHeckeMatrix_11_23 :
    sgChainHeckeMatrix ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 := by
  decide

/-- Entrée de chaîne : 23 → 17. -/
theorem sgChainHeckeMatrix_23_17 :
    sgChainHeckeMatrix ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 := by
  decide

/-! ## Section 4 — Caractère fini ε₃₀ -/

/-- Caractère fini modulo 30 à valeurs entières.

    Cette version entière est la source canonique. Les versions rationnelle ou
    réelle peuvent être obtenues par coercion. -/
def epsilon30Int (p : Nat) : Int :=
  match p % 30 with
  | 1  =>  1
  | 7  =>  1
  | 11 => -1
  | 13 =>  1
  | 17 => -1
  | 19 =>  1
  | 23 => -1
  | 29 =>  1
  | _  =>  0

/-- Version réelle de `epsilon30Int`, utile pour les futurs ponts spectraux. -/
noncomputable def epsilon30 (p : Nat) : Real :=
  (epsilon30Int p : Real)

/-- Valeur de ε₃₀ sur S.11. -/
theorem epsilon30_S11 : epsilon30 11 = -1 := by
  norm_num [epsilon30, epsilon30Int]

/-- Valeur de ε₃₀ sur S.23. -/
theorem epsilon30_S23 : epsilon30 23 = -1 := by
  norm_num [epsilon30, epsilon30Int]

/-- Valeur de ε₃₀ sur S.29. -/
theorem epsilon30_S29 : epsilon30 29 = 1 := by
  norm_num [epsilon30, epsilon30Int]

/-- Somme de ε₃₀ sur les trois sources SG : -1. -/
theorem epsilon30_sum_active :
    epsilon30 11 + epsilon30 23 + epsilon30 29 = -1 := by
  norm_num [epsilon30, epsilon30Int]

/-- Diagonale ε₃₀ sur l'espace source SG {11, 23, 29}. -/
noncomputable def D_epsilon_SG : Fin 3 → Real
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ =>  1

/-- La diagonale `D_epsilon_SG` coïncide avec ε₃₀ évalué sur les sources SG. -/
theorem D_epsilon_SG_eq_epsilon30 (i : Fin 3) :
    D_epsilon_SG i = epsilon30 (sgSourceResidue i) := by
  fin_cases i <;> norm_num [D_epsilon_SG, epsilon30, epsilon30Int, sgSourceResidue]

/-!
## Clôture doctrinale

Ce fichier ferme le noyau fini du SG-shift modulo 30.

Établi, statut [D] :
  * `heckeT2 r = (2*r+1) % 30` ;
  * branches actives 11 → 23, 23 → 17, 29 → 29 ;
  * sorties inactives hors de U₃₀ ;
  * deux matrices d'adjacence finies ;
  * caractère fini ε₃₀ modulo 30.

Non établi ici :
  * aucune statistique sur les transitions empiriques ;
  * aucun résultat spectral global ;
  * aucun pont Euler infini ;
  * aucune revendication RH.

Le fichier est destiné à être importé par les couches suivantes sans dépendre
d'elles : `Logic/SophieGermainMatrix.lean`, `Residue/SGShiftSqrt2.lean`,
et un éventuel pont legacy `SophieGermain/SophieGermainSpectral.lean`.
-/

end SophieGermainHecke
end Core
end CouretUnification
