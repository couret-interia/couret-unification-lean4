/-
Copyright (c) 2026 A. Couret. Tous droits réservés.
Programme : Couret-Unification
Fichier   : CouretUnification/Residue/SGShiftSqrt2.lean
Date      : 2026-05-04

# Invariant structurel √2 du SG-shift

Invariant structurel fini pour le décalage de Sophie Germain

    T_SG : a ↦ 2a + 1   (mod 30)

restreint au graphe fini des résidus dans U₃₀ = (ℤ/30ℤ)*.

Le SG-shift reste dans U₃₀ seulement en trois points :

    11 → 23,    23 → 17,    29 → 29.

(Tous les autres éléments de U₃₀ sont envoyés vers des résidus partageant
un facteur avec 30.)

Le bloc en chaîne non trivial à trois nœuds de l'opérateur **symétrisé**
M = (T_SG + T_SGᵀ) / 2, restreint aux indices (11, 17, 23), est la matrice
rationnelle

        ⎛ 0    0    1/2 ⎞
    M = ⎜ 0    0    1/2 ⎟  ∈  Matrix (Fin 3) (Fin 3) ℚ.
        ⎝ 1/2  1/2  0   ⎠

Ce fichier démontre l'**identité cubique** finie

    M³ = (1 / 2 : ℚ) · M,

équivalemment `2 · M³ = M`, ou encore `M · (2 M² − I) = 0`.

Par le théorème de Cayley–Hamilton sur ℚ ⊂ ℝ ⊂ ℂ, toute valeur propre λ
de M satisfait l'annulateur polynomial 2 λ³ − λ = 0, c'est-à-dire
λ · (2 λ² − 1) = 0. Les racines réelles sont λ ∈ {0, +1/√2, −1/√2}.
Ainsi, le module spectral non nul du bloc symétrisé du SG-shift est
exactement **1/√2**.

Cet invariant est **indépendant du caractère** : tout twist diagonal de signes
E ∈ {±1}³ agit sur M par conjugaison E · M · E (avec E² = I), ce qui
préserve le polynôme caractéristique. Les valeurs singulières non nulles
sont donc un invariant intrinsèque du graphe SG-shift sur U₃₀.

Ce fichier relève uniquement de l'**algèbre rationnelle finie**. Il ne contient
aucun prolongement analytique, aucune revendication globale, et aucun usage de
`Real.sqrt`. Le √2 apparaît seulement dans l'interprétation doctrinale qui suit
l'identité cubique démontrée.

Transition du registre de statut : [P → D] — sceau formel de l'observation
empirique dans la campagne multi-q de chiralité (Phase 1, 2026-05-04).

Ce fichier ne traite **pas** l'invariant conjecturé `1/√7` de l'opérateur
empirique Δ̃_SG. Voir `NO_GO_SG_1SQRT7.md` dans le registre du programme :
cette hypothèse a été rétrogradée à [O] non reproduite.

`RHClaimed = false`.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

namespace CouretUnification.Residue

open Matrix

/-- Le bloc en chaîne symétrisé 3 × 3 du SG-shift sur les indices
    (11, 17, 23).

    Les entrées hors diagonale valent 1/2 aux positions
    `(0, 2)`, `(1, 2)`, `(2, 0)`, `(2, 1)`. -/
def sgShiftBlock : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0,    0,    1/2 ;
     0,    0,    1/2 ;
     1/2,  1/2,  0   ]

/-- Le bloc est symétrique : `Mᵀ = M`. -/
theorem sgShiftBlock_isSymm : sgShiftBlock.transpose = sgShiftBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.transpose_apply]

/-- Carré du bloc en chaîne :
    `M² = !![1/4, 1/4, 0 ; 1/4, 1/4, 0 ; 0, 0, 1/2]`. -/
theorem sgShiftBlock_sq :
    sgShiftBlock * sgShiftBlock =
      !![1/4, 1/4, 0   ;
         1/4, 1/4, 0   ;
         0,   0,   1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- Cube du bloc en chaîne :
    `M³ = !![0, 0, 1/4 ; 0, 0, 1/4 ; 1/4, 1/4, 0]`. -/
theorem sgShiftBlock_cube :
    sgShiftBlock * sgShiftBlock * sgShiftBlock =
      !![0,   0,   1/4 ;
         0,   0,   1/4 ;
         1/4, 1/4, 0  ] := by
  rw [sgShiftBlock_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- **Identité cubique principale** : `M · M · M = (1/2 : ℚ) • M`.

    C'est l'identité structurelle finie qui contraint le spectre non trivial
    du bloc symétrisé du SG-shift aux racines de X(2X² − 1). -/
theorem sgShiftBlock_cubic_identity :
    sgShiftBlock * sgShiftBlock * sgShiftBlock = (1/2 : ℚ) • sgShiftBlock := by
  rw [sgShiftBlock_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.smul_apply] <;> norm_num

/-- Forme entière équivalente : `2 · M³ = M`. -/
theorem sgShiftBlock_two_smul_cube :
    (2 : ℚ) • (sgShiftBlock * sgShiftBlock * sgShiftBlock) = sgShiftBlock := by
  rw [sgShiftBlock_cubic_identity, smul_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.smul_apply]

/-- Forme factorisée : `M · (2 · M² − I) = 0`.

    Cette forme affiche explicitement l'annulateur polynomial de `sgShiftBlock`
    sur son image : `X · (2 X² − 1) = 0`. -/
theorem sgShiftBlock_factored_zero :
    sgShiftBlock * ((2 : ℚ) • (sgShiftBlock * sgShiftBlock) - 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgShiftBlock, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_three] <;> norm_num

/-- Le bloc en chaîne n'est **pas** la matrice nulle. Ce contrôle de cohérence
    exclut le spectre dégénéré `{0, 0, 0}` et confirme que l'identité cubique
    ci-dessus porte un contenu non trivial. -/
theorem sgShiftBlock_ne_zero : sgShiftBlock ≠ 0 := by
  intro h
  have h02 : sgShiftBlock 0 2 = (0 : Matrix (Fin 3) (Fin 3) ℚ) 0 2 := by rw [h]
  simp [sgShiftBlock, Matrix.zero_apply] at h02

/-!
## Interprétation spectrale (doctrinale)

Par le théorème de Cayley–Hamilton sur ℚ, toute valeur propre λ de
`sgShiftBlock`, dans toute extension algébrique — en particulier dans ℝ ou ℂ —,
satisfait l'annulateur polynomial

    2 λ³ − λ = 0

équivalemment

    λ · (2 λ² − 1) = 0.

Les racines réelles sont exactement λ ∈ { 0, +1/√2, −1/√2 }. Ainsi, le module
spectral non nul du bloc en chaîne symétrisé du SG-shift est

    |λ_nonzero| = 1/√2.

Ce résultat est indépendant de tout twist de caractère sur `sgShiftBlock`, car
la conjugaison par une diagonale de signes préserve le polynôme caractéristique.

Ce √2 n'est **pas** le 1/√7 conjecturé de l'opérateur empirique Δ̃_SG.
Voir la note de registre `NO_GO_SG_1SQRT7.md` : l'hypothèse 1/√7 est
rétrogradée à `[O] non reproduite` dans toute lecture honnête de la chaîne de
Markov empirique twistée par un caractère de Dirichlet réel modulo 30.

Les deux constantes vivent dans des objets différents :

* `1/√2` — invariant algébrique fini de `sgShiftBlock`,
            démontré ici sans `Real.sqrt`.
* `1/√7` — invariant géométrique sur le 7-simplexe Δ⁷,
            sans lien avec la chaîne empirique SG.

Statut : ce fichier fournit le **sceau algébrique** pour `1/√2` comme invariant
structurel du graphe SG-shift sur U₃₀.

L'énoncé spectral complet (`λ ∈ {0, ±1/√2}` avec multiplicités `1, 1, 1`)
requiert Cayley–Hamilton sur un corps, puis la résolution du polynôme
`2 X² − 1` sur ℝ ou ℂ ; ces deux étapes sont des applications directes de
Mathlib et sont prévues comme suite dans `SGShiftSpectrum.lean`.
-/

end CouretUnification.Residue