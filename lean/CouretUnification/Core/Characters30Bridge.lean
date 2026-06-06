/-
  CouretUnification/Core/Characters30Bridge.lean — v35.1

  Pont fini entre :
  - l’énumération documentaire de G₃₀,
  - les caractères explicites de Characters30,
  - l’opérateur de convolution fini de Convolution30.

  Statut :
  - 0 sorry.
  - RHClaimed = false.
  - Couche finie exacte.
  - Ne ferme aucun verrou analytique global.

  Règle d’architecture :
  NOTE : ne doit PAS importer CRTEquiv.
  Le fichier reste dans le noyau fini effectif, par énumération et calcul
  explicite sur G₃₀, sans dépendre d’une équivalence CRT externe.
-/
import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30
import CouretUnification.Core.CharacterLemmas

open scoped BigOperators

namespace CouretUnification.Core

/-!
# Pont caractères–convolution sur G₃₀

Ce fichier relie les caractères finis explicites construits dans
`Characters30.lean` à l’opérateur de convolution de `Convolution30.lean`.

L’objectif est de certifier, dans le noyau fini modulo 30, que les caractères
de G₃₀ diagonalisent l’opérateur de convolution :

  convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ.

La preuve repose sur quatre briques finies :

1. une conversion explicite `G30 → Idx`, compatible avec l’ordre documentaire ;
2. une lecture des coordonnées `(Fin 2 × Fin 4)` via `residueCoord` ;
3. la multiplicativité des phases C₂ et C₄ ;
4. la réindexation finie de la somme de convolution.

Le fichier reste volontairement élémentaire et énumératif :
il ne dépend pas de `CRTEquiv`, afin de préserver la séparation stricte du noyau
fini exact.
-/

/-- Convertit un élément de `G30` vers son indice documentaire `Idx`.

L’ordre documentaire est :

  1 ↦ 0,  7 ↦ 1,  11 ↦ 2,  13 ↦ 3,
  17 ↦ 4, 19 ↦ 5, 23 ↦ 6, 29 ↦ 7.

Le dernier cas couvre nécessairement `29`, puisque `G30` ne contient que les
huit unités modulo 30. -/
def g30ToIdx (u : G30) : Idx :=
  if (u : ZMod 30) = 1  then ⟨0, by omega⟩
  else if (u : ZMod 30) = 7  then ⟨1, by omega⟩
  else if (u : ZMod 30) = 11 then ⟨2, by omega⟩
  else if (u : ZMod 30) = 13 then ⟨3, by omega⟩
  else if (u : ZMod 30) = 17 then ⟨4, by omega⟩
  else if (u : ZMod 30) = 19 then ⟨5, by omega⟩
  else if (u : ZMod 30) = 23 then ⟨6, by omega⟩
  else ⟨7, by omega⟩

/-- Caractère explicite sur `G30`, obtenu en évaluant `characterEval`
sur l’indice documentaire associé. -/
def charOnG30 (χ : CharIdx) : FunG30 := fun g => characterEval χ (g30ToIdx g)

/-- Valeur propre associée au noyau de convolution `K` et au caractère `χ`.

La normalisation utilisée est celle de la convolution à droite :

  eigenvalue K χ = ∑ g, K g * χ(g⁻¹). -/
noncomputable def eigenvalue (K : FunG30) (χ : CharIdx) : ℂ :=
  ∑ g : G30, K g * charOnG30 χ g⁻¹

/-- Coordonnées `Fin 2 × Fin 4` d’un élément de `G30`, via son indice documentaire. -/
def g30Coord (g : G30) : Fin 2 × Fin 4 := residueCoord (g30ToIdx g)

/-- Addition coordonnée par coordonnée dans `Fin 2 × Fin 4`. -/
def addCoord (p q : Fin 2 × Fin 4) : Fin 2 × Fin 4 := (p.1 + q.1, p.2 + q.2)

-- Force l’évaluation de l’addition dans `Fin n`
-- (`simp`/`norm_num` ne la réduisent pas toujours assez explicitement).

/-- Évaluation explicite de l’addition dans `Fin 4`. -/
@[simp] lemma fin4_add_eval (a b : Fin 4) :
    (a + b : Fin 4) = ⟨(a.val + b.val) % 4, Nat.mod_lt _ (by decide)⟩ := by ext; rfl

/-- Évaluation explicite de l’addition dans `Fin 2`. -/
@[simp] lemma fin2_add_eval (a b : Fin 2) :
    (a + b : Fin 2) = ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩ := by ext; rfl

-- Puissances concrètes de `I`.
-- `ring` seul ne sait pas normaliser automatiquement `I² = -1`.

/-- `I^3 = -I`. -/
lemma Ip3  : Complex.I ^ (3:ℕ)  = -Complex.I := by
  have : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
  rw [this, Complex.I_sq]; ring

/-- `I^4 = 1`. -/
lemma Ip4  : Complex.I ^ (4:ℕ)  = 1 := by
  have : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^5 = I`. -/
lemma Ip5  : Complex.I ^ (5:ℕ)  = Complex.I := by
  have : Complex.I ^ 5 = (Complex.I ^ 2) ^ 2 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^8 = 1`. -/
lemma Ip8  : Complex.I ^ (8:ℕ)  = 1 := by
  have : Complex.I ^ 8 = (Complex.I ^ 2) ^ 4 := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^6 = -1`. -/
lemma Ip6  : Complex.I ^ (6:ℕ)  = -1 := by
  have : Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^7 = -I`. -/
lemma Ip7  : Complex.I ^ (7:ℕ)  = -Complex.I := by
  have : Complex.I ^ 7 = (Complex.I ^ 2) ^ 3 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^9 = I`. -/
lemma Ip9  : Complex.I ^ (9:ℕ)  = Complex.I := by
  have : Complex.I ^ 9 = (Complex.I ^ 2) ^ 4 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^10 = -1`. -/
lemma Ip10 : Complex.I ^ (10:ℕ) = -1 := by
  have : Complex.I ^ 10 = (Complex.I ^ 2) ^ 5 := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^12 = 1`. -/
lemma Ip12 : Complex.I ^ (12:ℕ) = 1  := by
  have : Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^15 = -I`. -/
lemma Ip15 : Complex.I ^ (15:ℕ) = -Complex.I := by
  have : Complex.I ^ 15 = (Complex.I ^ 2) ^ 7 * Complex.I := by ring
  rw [this, Complex.I_sq]; norm_num

/-- `I^18 = -1`. -/
lemma Ip18 : Complex.I ^ (18:ℕ) = -1 := by
  have : Complex.I ^ 18 = (Complex.I ^ 2) ^ 9 := by ring
  rw [this, Complex.I_sq]; norm_num
-- Inégalités concrètes dans ℂ

-- Inégalités concrètes dans ℂ utilisées pour exclure les caractères non triviaux.

/-- `I ≠ 1` dans `ℂ`. -/
lemma I_ne_one : Complex.I ≠ 1 := by
  intro h; have := congr_arg Complex.im h; simp at this

/-- `-I ≠ 1` dans `ℂ`. -/
lemma neg_I_ne_one : -Complex.I ≠ 1 := by
  intro h; have := congr_arg Complex.im h; simp at this

/-- `-1 ≠ 1` dans `ℂ`. -/
lemma neg_one_ne_one_C : (-1 : ℂ) ≠ 1 := by norm_num

set_option maxHeartbeats 800000 in
/-- Les coordonnées documentaires transforment la multiplication de `G30`
en addition dans `Fin 2 × Fin 4`.

Cette preuve est volontairement finie et exhaustive : on énumère les huit
éléments de `G30` et l’on vérifie la compatibilité produit/addition sans
importer d’équivalence CRT abstraite. -/
theorem g30Coord_mul (a b : G30) :
    g30Coord (a * b) = addCoord (g30Coord a) (g30Coord b) := by
  fin_cases a <;> fin_cases b <;>
    simp [g30Coord, g30ToIdx, residueCoord, addCoord] <;> decide

/-- Formule factorisée de l’évaluation d’un caractère sur `G30`.

Si `g` a coordonnées `(e,k)` et si `χ` a coordonnées `(m,n)`, alors :

  χ(g) = c2Phase m e * c4Phase n k. -/
theorem charOnG30_factor (χ : CharIdx) (g : G30) :
    charOnG30 χ g =
      let (e, k) := g30Coord g
      let (m, n) := charCoord χ
      c2Phase m e * c4Phase n k := by
  simp only [charOnG30, g30Coord, characterEval]

/-- Multiplicativité de la phase C₂ en la variable de droite. -/
theorem c2Phase_mul_right (m : Fin 2) (e₁ e₂ : Fin 2) :
    c2Phase m (e₁ + e₂) = c2Phase m e₁ * c2Phase m e₂ := by
  fin_cases m <;> fin_cases e₁ <;> fin_cases e₂ <;> simp [c2Phase]

/-- Identité locale : `I * I = -1`. -/
lemma I_mul_I : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]

set_option maxHeartbeats 1600000 in
/-- Multiplicativité de la phase C₄ en la variable de droite.

La preuve est exhaustive sur `Fin 4`; les puissances de `I` supérieures à 3
sont normalisées par les lemmes `Ip*` ci-dessus. -/
theorem c4Phase_mul_right (n : Fin 4) (k₁ k₂ : Fin 4) :
    c4Phase n (k₁ + k₂) = c4Phase n k₁ * c4Phase n k₂ := by
  fin_cases n <;> fin_cases k₁ <;> fin_cases k₂ <;>
    simp only [c4Phase, fin4_add_eval] <;> try ring_nf <;>
    -- Objectifs restants : A = I^k avec k ≥ 4 ; on réécrit le membre droit.
    (try rw [Ip18]) <;> (try rw [Ip15]) <;> (try rw [Ip12]) <;>
    (try rw [Ip10]) <;> (try rw [Ip8])  <;>
    (try rw [Ip6])  <;> (try rw [Ip5])  <;> (try rw [Ip4])  <;>
    (try rw [Ip3])  <;> (try rw [Complex.I_sq])

/-- Multiplicativité des caractères explicites sur `G30`.

C’est la fermeture technique principale du pont :
les caractères définis par coordonnées documentaires sont bien des caractères
multiplicatifs de `G30`. -/
theorem charOnG30_mul (χ : CharIdx) (a b : G30) :
    charOnG30 χ (a * b) = charOnG30 χ a * charOnG30 χ b := by
  simp only [charOnG30_factor]
  rw [g30Coord_mul]
  simp only [addCoord]
  rw [c2Phase_mul_right, c4Phase_mul_right]
  ring

/-- Le caractère explicite `charOnG30 χ` vu comme morphisme multiplicatif
`G30 →* ℂ`. -/
def charOnG30AsHom (χ : CharIdx) : G30 →* ℂ where
  toFun := charOnG30 χ
  map_one' := by
    fin_cases χ <;>
      simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]
  map_mul' := charOnG30_mul χ

set_option maxHeartbeats 800000 in
/-- Un caractère non trivial n’est pas le morphisme constant égal à 1.

La preuve énumère les caractères possibles et utilise deux témoins concrets
dans `G30`, correspondant aux classes 7 et 11, pour produire une contradiction
lorsqu’une valeur vaut `I`, `-I` ou `-1` au lieu de `1`. -/
theorem charOnG30AsHom_ne_one (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    charOnG30AsHom χ ≠ 1 := by
  intro h; apply hχ
  fin_cases χ
  · rfl
  all_goals (
    exfalso

    -- Témoins concrets dans G₃₀ permettant de détecter les caractères non triviaux.
    have hidx7 : g30ToIdx (⟨7, 13, by decide, by decide⟩ : G30) = ⟨1, by omega⟩ := by
      simp [g30ToIdx]; decide
    have hidx11 : g30ToIdx (⟨11, 11, by decide, by decide⟩ : G30) = ⟨2, by omega⟩ := by
      simp [g30ToIdx]; decide
    -- Extraction de `charOnG30 χ g = 1` à partir de l’hypothèse `h`.
    have h7 := DFunLike.congr_fun h (⟨7, 13, by decide, by decide⟩ : G30)
    have h11 := DFunLike.congr_fun h (⟨11, 11, by decide, by decide⟩ : G30)
    simp only [charOnG30AsHom, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply] at h7 h11

    -- Évaluation des valeurs de caractères et normalisation des puissances de `I`.
    simp [charOnG30, hidx7, hidx11, characterEval, charCoord, residueCoord,
          c2Phase, c4Phase, Complex.I_sq, Ip6] at h7 h11

    -- Les hypothèses restantes sont de la forme `I=1`, `-I=1`, `-1=1`
    -- ou sont triviales ; on ferme par contradiction.
    first
      | exact absurd h7 I_ne_one
      | exact absurd h7 neg_I_ne_one
      | exact absurd h7 neg_one_ne_one_C
      | exact absurd h11 I_ne_one
      | exact absurd h11 neg_I_ne_one
      | exact absurd h11 neg_one_ne_one_C
  )

/-- La somme d’un caractère non trivial sur `G30` est nulle.

Ce résultat est obtenu en appliquant le lemme abstrait
`sum_char_eq_zero_of_ne_one` au morphisme multiplicatif `charOnG30AsHom χ`. -/
theorem sum_charOnG30_ne_trivial (χ : CharIdx) (hχ : χ ≠ ⟨0, by omega⟩) :
    ∑ g : G30, charOnG30 χ g = 0 := by
  have hne := charOnG30AsHom_ne_one χ hχ
  have key := sum_char_eq_zero_of_ne_one (charOnG30AsHom χ) hne
  convert key using 1

/-- Le caractère d’indice `0` est le caractère trivial : il vaut `1` partout. -/
theorem charOnG30_trivial (g : G30) :
    charOnG30 ⟨0, by omega⟩ g = 1 := by
  simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

/-- Aucun caractère `charOnG30 χ` n’est la fonction nulle.

Il suffit d’évaluer en l’élément neutre de `G30`, où chaque caractère vaut `1`. -/
theorem charOnG30_ne_zero (χ : CharIdx) : charOnG30 χ ≠ 0 := by
  intro h; have h1 : charOnG30 χ (1 : G30) = 0 := congr_fun h _
  fin_cases χ <;>
    simp [charOnG30, g30ToIdx, characterEval, charCoord, residueCoord, c2Phase, c4Phase] at h1

/-- Réindexation finie de la somme par la bijection `y ↦ x * y⁻¹`.

Cette forme est adaptée à la preuve de diagonalisation de la convolution :
elle transforme une somme en `x * y⁻¹` en une somme libre sur `g`. -/
private lemma sum_reindex_mul_inv' (x : G30) (F : G30 → ℂ) :
    (∑ y : G30, F (x * y⁻¹)) = ∑ g : G30, F g := by
  apply Finset.sum_nbij (fun y => x * y⁻¹)
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => by have := mul_left_cancel h; exact inv_injective this)
    (fun g _ => ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩)
    (fun _ _ => rfl)

/-- Forme ponctuelle de la diagonalisation de la convolution.

Pour tout noyau fini `K`, tout caractère `χ` et tout point `x`, on a :

  convolutionOp K (charOnG30 χ) x
    = eigenvalue K χ * charOnG30 χ x.

La preuve utilise :
- la réindexation `y ↦ x * y⁻¹`,
- la multiplicativité de `charOnG30`,
- la factorisation finale de `charOnG30 χ x` hors de la somme. -/
theorem convolution_diag_pointwise (K : FunG30) (χ : CharIdx) (x : G30) :
    convolutionOp K (charOnG30 χ) x = eigenvalue K χ * charOnG30 χ x := by
  simp only [convolutionOp, LinearMap.coe_mk, AddHom.coe_mk, eigenvalue]
  calc ∑ y : G30, K (x * y⁻¹) * charOnG30 χ y
      = ∑ g : G30, K g * charOnG30 χ (g⁻¹ * x) := by
          rw [← sum_reindex_mul_inv' x (fun g => K g * charOnG30 χ (g⁻¹ * x))]
          apply Finset.sum_congr rfl; intro y _; congr 1; congr 1; group
    _ = ∑ g : G30, K g * (charOnG30 χ g⁻¹ * charOnG30 χ x) := by
          apply Finset.sum_congr rfl; intro g _; congr 1; exact charOnG30_mul χ g⁻¹ x
    _ = (∑ g : G30, K g * charOnG30 χ g⁻¹) * charOnG30 χ x := by
          simp_rw [← mul_assoc]; rw [← Finset.sum_mul]

/-- Théorème global de diagonalisation.

Chaque caractère explicite `charOnG30 χ` est un vecteur propre de l’opérateur
de convolution `convolutionOp K`, avec valeur propre `eigenvalue K χ`.

C’est le pont spectral fini attendu :

  convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ. -/
theorem convolution_diagonalizes_character (K : FunG30) (χ : CharIdx) :
    convolutionOp K (charOnG30 χ) = eigenvalue K χ • charOnG30 χ := by
  funext x; exact convolution_diag_pointwise K χ x

end CouretUnification.Core
