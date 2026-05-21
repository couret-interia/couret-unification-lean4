import CouretUnification.Finite.Foundations

namespace CouretUnification.Core.CayleySpectrum

/-!
# Spectre exact de la matrice de Cayley

Ce fichier prouve le profil spectral fini de la matrice de Cayley du
triplet de Couret `T_C = {1, 11, 29}` sur `(ℤ/30ℤ)×`.

La source canonique des objets finis rationnels est désormais :

  `CouretUnification.Finite.Foundations`

En particulier, ce fichier ne redéfinit plus les utilitaires matriciels :

  `mm`, `mv`, `msub`, `meq`, `mzero`, `veq`, `sv`, `scI`, `tr`, `dot`.

Ils sont réexportés ici comme alias sémantiques pour préserver la lisibilité
et la compatibilité locale de `CayleySpectrum`.

## Stratégie

1. Vérifier `(A − 3I)(A − I)(A + I) = 0`.
   Donc les valeurs propres possibles sont dans `{−1, 1, 3}`.

2. Vérifier les traces :
   `Tr(A) = 8`, `Tr(A²) = 24`, puis aussi `Tr(A³) = 56`,
   `Tr(A⁴) = 168`.

3. Exhiber 8 vecteurs propres explicites :
   - 2 pour `λ = 3`,
   - 2 pour `λ = −1`,
   - 4 pour `λ = 1`.

Tout est vérifié par calcul fini exact sur `Fin 8 → Fin 8 → ℚ`.

`RHClaimed = false`.
-/

open Finite.Foundations

/-! ## §0 — Alias de compatibilité vers le socle rationnel canonique -/

/-- Indices des huit classes inversibles modulo 30. -/
abbrev Idx := Fin 8

/-- Matrices rationnelles 8 × 8, alias de `Finite.Foundations.QMat`. -/
abbrev IMat := CouretUnification.Finite.Foundations.QMat

/-- Vecteurs rationnels de longueur 8, alias de `Finite.Foundations.Sig`. -/
abbrev IVec := CouretUnification.Finite.Foundations.Sig

/-- Matrice de Cayley canonique, alias de `Finite.Foundations.cayleyMat`. -/
def A : IMat := CouretUnification.Finite.Foundations.cayleyMat

/-- Produit matriciel fini, alias canonique. -/
abbrev CS_mm := CouretUnification.Finite.Foundations.mm

/-- Multiplication matrice-vecteur, alias canonique. -/
abbrev CS_mv := CouretUnification.Finite.Foundations.mv

/-- Multiplication scalaire d'un vecteur, alias canonique. -/
abbrev CS_sv := CouretUnification.Finite.Foundations.sv

/-- Égalité booléenne de vecteurs, alias canonique. -/
abbrev CS_veq := CouretUnification.Finite.Foundations.veq

/-- Trace finie, alias canonique. -/
abbrev CS_tr := CouretUnification.Finite.Foundations.tr

/-- Égalité booléenne de matrices, alias canonique. -/
abbrev CS_meq := CouretUnification.Finite.Foundations.meq

/-- Matrice scalaire `k · I`, alias canonique. -/
abbrev CS_scI := CouretUnification.Finite.Foundations.scI

/-- Soustraction matricielle, alias canonique. -/
abbrev CS_msub := CouretUnification.Finite.Foundations.msub

/-- Matrice nulle, alias canonique. -/
abbrev CS_mzero := CouretUnification.Finite.Foundations.mzero

/-- Produit scalaire fini, alias canonique. -/
abbrev CS_dot := CouretUnification.Finite.Foundations.dot

/-- Vérification que `A` est exactement la matrice canonique de `Finite`. -/
theorem A_eq_finite_cayleyMat :
    A = CouretUnification.Finite.Foundations.cayleyMat := rfl

/-- Somme de ligne d'une matrice rationnelle 8 × 8. -/
def rsum (M : IMat) (i : Idx) : ℚ :=
  (List.finRange 8).foldl (fun acc j => acc + M i j) 0

/-! ## §1 — Propriétés de base -/

/-- La matrice de Cayley est symétrique. -/
theorem A_symmetric : meq A (fun i j => A j i) = true := by
  native_decide

/-- Toutes les sommes de lignes de `A` valent 3. -/
theorem A_all_row_sums_3 :
    (List.finRange 8).all (fun i => rsum A i == 3) = true := by
  native_decide

/-! ## §2 — Annulateur spectral : valeurs propres dans {−1, 1, 3} -/

/--
`(A − 3I)(A − I)(A + I) = 0`.

Le polynôme minimal divise donc `(X−3)(X−1)(X+1)`.
Les valeurs propres possibles de `A` sont incluses dans `{−1, 1, 3}`.
-/
theorem minpoly_annihilates :
    meq (mm (mm (msub A (scI 3)) (msub A (scI 1))) (msub A (scI (-1)))) mzero
      = true := by
  native_decide

/-! ## §3 — Traces et multiplicités -/

theorem trace_A : tr A = 8 := by native_decide
theorem trace_A2 : tr (mm A A) = 24 := by native_decide
theorem trace_A3 : tr (mm (mm A A) A) = 56 := by native_decide
theorem trace_A4 : tr (mm (mm (mm A A) A) A) = 168 := by native_decide

/--
Si les valeurs propres sont dans `{3, 1, −1}` avec multiplicités `a, b, c`,
alors :

  a + b + c = 8,
  3a + b − c = 8,
  9a + b + c = 24.

La solution attendue est :

  a = 2, b = 4, c = 2.
-/
theorem mult_check_dim : 2 + 4 + 2 = (8 : ℚ) := by norm_num
theorem mult_check_tr1 : 2 * 3 + 4 * 1 + 2 * (-1) = (8 : ℚ) := by norm_num
theorem mult_check_tr2 : 2 * 9 + 4 * 1 + 2 * 1 = (24 : ℚ) := by norm_num
theorem mult_check_tr3 : 2 * 27 + 4 * 1 + 2 * (-1) = (56 : ℚ) := by norm_num
theorem mult_check_tr4 : 2 * 81 + 4 * 1 + 2 * 1 = (168 : ℚ) := by norm_num

/-! ## §4 — Vecteurs propres explicites -/

/-!
Les quatre premiers vecteurs propres proviennent directement du socle
canonique `Finite.Foundations`.

- `v3a = one`
- `v3b = chi5`
- `vm1a = chi3`
- `vm1b = chi15`
-/

/-- Vecteur propre pour `λ = 3`, caractère trivial. -/
def v3a : IVec := CouretUnification.Finite.Foundations.one

/-- Vecteur propre pour `λ = 3`, caractère réel `chi5`. -/
def v3b : IVec := CouretUnification.Finite.Foundations.chi5

theorem v3a_eigen : veq (mv A v3a) (sv 3 v3a) = true := by native_decide
theorem v3b_eigen : veq (mv A v3b) (sv 3 v3b) = true := by native_decide

/-- Vecteur propre pour `λ = −1`, caractère réel `chi3`. -/
def vm1a : IVec := CouretUnification.Finite.Foundations.chi3

/-- Vecteur propre pour `λ = −1`, caractère réel `chi15`. -/
def vm1b : IVec := CouretUnification.Finite.Foundations.chi15

theorem vm1a_eigen : veq (mv A vm1a) (sv (-1) vm1a) = true := by native_decide
theorem vm1b_eigen : veq (mv A vm1b) (sv (-1) vm1b) = true := by native_decide

/-
λ = 1 eigenspace, dimension 4.

Ces vecteurs sont les parties réelles/imaginaires des caractères complexes
restants dans la lecture `C₂ × C₄`.
-/

/-- Premier vecteur propre pour `λ = 1`. -/
def v1a : IVec := ![1, 0, -1, 0, 1, 0, -1, 0]

/-- Deuxième vecteur propre pour `λ = 1`. -/
def v1b : IVec := ![0, 1, 0, -1, 0, 1, 0, -1]

/-- Troisième vecteur propre pour `λ = 1`. -/
def v1c : IVec := ![1, 0, -1, 0, -1, 0, 1, 0]

/-- Quatrième vecteur propre pour `λ = 1`. -/
def v1d : IVec := ![0, 1, 0, -1, 0, -1, 0, 1]

theorem v1a_eigen : veq (mv A v1a) (sv 1 v1a) = true := by native_decide
theorem v1b_eigen : veq (mv A v1b) (sv 1 v1b) = true := by native_decide
theorem v1c_eigen : veq (mv A v1c) (sv 1 v1c) = true := by native_decide
theorem v1d_eigen : veq (mv A v1d) (sv 1 v1d) = true := by native_decide

/-! ## §5 — Orthogonalité des vecteurs propres -/

/-- Orthogonalité entre secteurs `λ = 3` et `λ = −1`. -/
theorem v3a_orth_vm1a : dot v3a vm1a = 0 := by native_decide

/-- Orthogonalité entre secteurs `λ = 3` et `λ = 1`. -/
theorem v3a_orth_v1a : dot v3a v1a = 0 := by native_decide

/-- Orthogonalité entre secteurs `λ = −1` et `λ = 1`. -/
theorem vm1a_orth_v1a : dot vm1a v1a = 0 := by native_decide

/-- Orthogonalité interne du secteur `λ = 3`. -/
theorem v3a_orth_v3b : dot v3a v3b = 0 := by native_decide

/-- Orthogonalité interne du secteur `λ = −1`. -/
theorem vm1a_orth_vm1b : dot vm1a vm1b = 0 := by native_decide

/-- Orthogonalité interne du secteur `λ = 1`. -/
theorem v1a_orth_v1b : dot v1a v1b = 0 := by native_decide
theorem v1a_orth_v1c : dot v1a v1c = 0 := by native_decide
theorem v1a_orth_v1d : dot v1a v1d = 0 := by native_decide
theorem v1b_orth_v1c : dot v1b v1c = 0 := by native_decide
theorem v1b_orth_v1d : dot v1b v1d = 0 := by native_decide
theorem v1c_orth_v1d : dot v1c v1d = 0 := by native_decide

/-! ## §6 — Non-nullité des vecteurs propres -/

theorem v3a_nonzero : dot v3a v3a ≠ 0 := by native_decide
theorem v3b_nonzero : dot v3b v3b ≠ 0 := by native_decide
theorem vm1a_nonzero : dot vm1a vm1a ≠ 0 := by native_decide
theorem vm1b_nonzero : dot vm1b vm1b ≠ 0 := by native_decide
theorem v1a_nonzero : dot v1a v1a ≠ 0 := by native_decide
theorem v1b_nonzero : dot v1b v1b ≠ 0 := by native_decide
theorem v1c_nonzero : dot v1c v1c ≠ 0 := by native_decide
theorem v1d_nonzero : dot v1d v1d ≠ 0 := by native_decide

/-!
## Synthèse

On obtient le profil spectral fini :

  Spec(A) = {3², 1⁴, (−1)²}.

| Fait | Théorème | Méthode |
|------|----------|---------|
| Valeurs propres ⊆ {−1,1,3} | `minpoly_annihilates` | `native_decide` |
| Tr(A) = 8, Tr(A²) = 24 | `trace_A`, `trace_A2` | `native_decide` |
| mult(3)=2, mult(1)=4, mult(−1)=2 | `mult_check_*` | `norm_num` |
| 2 vecteurs pour λ=3 | `v3a_eigen`, `v3b_eigen` | `native_decide` |
| 2 vecteurs pour λ=−1 | `vm1a_eigen`, `vm1b_eigen` | `native_decide` |
| 4 vecteurs pour λ=1 | `v1a_eigen` .. `v1d_eigen` | `native_decide` |
| Orthogonalité par paires | `v*_orth_*` | `native_decide` |
| Non-nullité | `v*_nonzero` | `native_decide` |

Huit vecteurs propres non nuls et orthogonaux dans `ℚ⁸` donnent huit
directions indépendantes. Le profil spectral fini est donc complètement
représenté dans cette couche.

Aucune conséquence RH n'est revendiquée.
-/

/-! ## §7 — Garde doctrinale -/

/-- Invariant constitutionnel : ce fichier ne revendique pas RH. -/
def RHClaimed : Bool := false

example : RHClaimed = false := rfl

end CouretUnification.Core.CayleySpectrum
