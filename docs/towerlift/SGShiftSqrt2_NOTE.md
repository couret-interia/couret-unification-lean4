# SGShiftSqrt2.lean — Note compagnon

**Programme :** Couret-Unification
**Date :** 2026-05-04
**Fichier :** `lean/CouretUnification/Residue/SGShiftSqrt2.lean`
**Statut :** Sceau algébrique — `[P → D]` pour l’invariant structurel 1/√2

---

## Objet

Ce fichier Lean 4 fournit le sceau algébrique de l’invariant structurel
**1/√2** du graphe SG-shift symétrisé sur U₃₀, identifié empiriquement
dans la campagne multi-q de chiralité — Phase 1.

La preuve relève d’une **algèbre rationnelle finie pure** :
pas de `Real.sqrt`, pas de continuation analytique, pas de revendication
globale.

---

## Contenu mathématique

### La matrice

Le décalage de Sophie Germain `T_SG : a ↦ 2a + 1 (mod 30)`, restreint à
`U₃₀ = (ℤ/30ℤ)*`, possède seulement trois orbites dans U₃₀ :

```
11 → 23 → 17     (chaîne)
29 → 29          (point fixe)
```

Le bloc non trivial de chaîne de l’opérateur symétrisé
`M = (T_SG + T_SGᵀ) / 2` sur les indices `(11, 17, 23)` est

```
       ⎛ 0    0    1/2 ⎞
   M = ⎜ 0    0    1/2 ⎟
       ⎝ 1/2  1/2  0   ⎠
```

### L’identité prouvée

Le fichier prouve sept propositions, toutes par calcul direct sur ℚ :

1. `sgShiftBlock_isSymm`         : `Mᵀ = M`.
2. `sgShiftBlock_sq`             : `M² = !![1/4,1/4,0; 1/4,1/4,0; 0,0,1/2]`.
3. `sgShiftBlock_cube`           : `M³ = !![0,0,1/4; 0,0,1/4; 1/4,1/4,0]`.
4. `sgShiftBlock_cubic_identity` : **`M³ = (1/2 : ℚ) • M`**.
5. `sgShiftBlock_two_smul_cube`  : `2 • M³ = M`.
6. `sgShiftBlock_factored_zero`  : `M · (2 • M² − I) = 0`.
7. `sgShiftBlock_ne_zero`        : `M ≠ 0`.

L’identité centrale (4)/(5)/(6) implique que toute valeur propre λ de M,
dans toute extension algébrique de ℚ, satisfait

```
2 λ³ − λ = 0    ⇔    λ · (2 λ² − 1) = 0.
```

Les racines réelles sont exactement `{0, +1/√2, −1/√2}`. Le module
spectral non nul de M est donc **`1/√2`** — l’invariant structurel
référencé dans `NO_GO_SG_1SQRT7.md`.

---

## Stratégie de preuve

Toutes les preuves utilisent le même schéma robuste :

```lean
ext i j
fin_cases i <;> fin_cases j <;>
  simp [sgShiftBlock, Matrix.mul_apply, Fin.sum_univ_three, ...] ; norm_num
```

Pour chacun des 9 cas `(i, j)`, le développement du produit matriciel via
`Fin.sum_univ_three` produit une expression rationnelle concrète que
`norm_num` clôt. Aucun `sorry`, aucun `decide`, aucune fragilité liée à
l’évaluation par le noyau.

---

## Conséquence pour le registre

Après intégration de ce fichier et passage de la CI au vert :

| Revendication | Avant | Après |
|---|---|---|
| 1/√2 structurel dans `sym(E·T_SG)` | `[P]` numérique | `[P→D]` sceau algébrique |
| Identité cubique `2 M³ = M` | non formalisée | `[D]` prouvée dans Lean |
| Énoncé spectral `λ ∈ {0, ±1/√2}` | implicite | `[O]` ouvert jusqu’à `SGShiftSpectrum.lean` |

L’énoncé spectral complet — Cayley–Hamilton + résolution de
`2 X² − 1` sur ℝ/ℂ — est prévu dans un fichier de suite
`SGShiftSpectrum.lean`. Le fichier actuel établit le noyau algébrique.

---

## Connexion au programme plus large

Ce fichier isole un résultat local net. Sa place dans le programme :

- **Ne remplace rien** : le sous-programme SG possédait déjà l’observable
  empirique de chiralité comme élément primaire.
- **Ajoute** : un invariant algébrique indépendant des caractères et
  certifié formellement.
- **Sépare** : 1/√2 — ici structurel et fini — de 1/√7 — géométrique,
  sur Δ⁷, sans lien direct.
- **Suspend** : la recherche d’un opérateur Δ̃_SG « originel » qui
  récupérerait 1/√7 — voir `NO_GO_SG_1SQRT7.md`.

Le rôle du fichier est le sceau algébrique d’un seul fait étroit, vrai et
localisé. Rien de plus, rien de moins.

`RHClaimed = false`.
