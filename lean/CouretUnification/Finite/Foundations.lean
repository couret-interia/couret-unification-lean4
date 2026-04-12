import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Finite

/-!
# Foundations — Noyau spectral fini sur `Fin 8 → ℚ`

Ce fichier fixe le **socle rationnel exact** du noyau fini mod 30
utilisé dans les couches `FiniteDefect` et `Criterion`.

Ordre des indices :
- `0 ↦ 1`
- `1 ↦ 7`
- `2 ↦ 11`
- `3 ↦ 13`
- `4 ↦ 17`
- `5 ↦ 19`
- `6 ↦ 23`
- `7 ↦ 29`

## Doctrine de ce fichier

On travaille ici dans un cadre **strictement fini, exact, décidable**.

On y introduit :

- l’espace des signaux `Sig = Fin 8 → ℚ`,
- le produit scalaire discret et la norme quadratique,
- quatre vecteurs structurants (`one`, `chi5`, `chi3`, `chi15`),
- les projecteurs spectraux `P₃`, `P₁`, `P₋`,
- l’opérateur de Cayley exact associé au triplet de Couret,
- des utilitaires matriciels finis pour les preuves par `native_decide`.

## Lecture spectrale

La matrice de Cayley exacte possède ici trois secteurs :

- `λ = 3` : secteur cohérent engendré par `one` et `chi5`,
- `λ = 1` : secteur neutre récupéré par `p1`,
- `λ = -1` : secteur de défaut engendré par `chi3` et `chi15`.

Le fichier ne revendique **aucun** résultat analytique global.
Il ne contient que le **prototype spectral fini exact**.

`RHClaimed = false`.
-/

/-- Type des signaux finis sur les 8 unités modulo 30. -/
abbrev Sig := Fin 8 → ℚ

-- ═══════════════════════════════════════════════════════════
-- Géométrie euclidienne finie
-- ═══════════════════════════════════════════════════════════

/--
Produit scalaire discret sur `Sig`.

Lecture :
`dot f g = Σ_i f(i) g(i)`.
-/
def dot (f g : Sig) : ℚ :=
  (List.finRange 8).foldl (fun acc i => acc + f i * g i) 0

/-- Norme quadratique discrète : `‖f‖² = ⟨f,f⟩`. -/
def normSq (f : Sig) : ℚ := dot f f

-- ═══════════════════════════════════════════════════════════
-- Base structurante / caractères réels compatibles avec la matrice exacte
-- ═══════════════════════════════════════════════════════════

/--
Vecteur constant.

C’est le témoin trivial du secteur propre `λ = 3`.
-/
def one : Sig := ![1, 1, 1, 1, 1, 1, 1, 1]

/--
Vecteur alterné.

C’est le miroir rationnel du `altVec` du fichier spectral réel
`Spectral/FiniteCore.lean`. Il appartient lui aussi au secteur `λ = 3`.
-/
def chi5 : Sig := ![1, -1, 1, -1, 1, -1, 1, -1]

/--
Premier vecteur du secteur de défaut `λ = -1`.

Il distingue les deux moitiés `{0,1,2,3}` et `{4,5,6,7}`.
-/
def chi3 : Sig := ![1, 1, 1, 1, -1, -1, -1, -1]

/--
Second vecteur du secteur de défaut `λ = -1`.

Il s’interprète comme le produit ponctuel `chi3 * chi5`.
-/
def chi15 : Sig := ![1, -1, 1, -1, -1, 1, -1, 1]

/--
Alias sémantique : dans la couche rationnelle, `altVec` est représenté par `chi5`.
-/
abbrev altVec : Sig := chi5

-- ═══════════════════════════════════════════════════════════
-- Signal distingué de Couret
-- ═══════════════════════════════════════════════════════════

/--
Indicatrice du triplet de Couret `TC = {1, 11, 29}`.

Dans l’ordre des indices choisi, cela correspond à `{0, 2, 7}`.
-/
def tcInd : Sig := ![1, 0, 1, 0, 0, 0, 0, 1]

-- ═══════════════════════════════════════════════════════════
-- Coordonnées spectrales finies
-- ═══════════════════════════════════════════════════════════

/--
Moyenne sur la classe `A = {0,2,4,6}`.

Cette coordonnée intervient dans le projecteur du secteur cohérent `λ = 3`.
-/
def mA (f : Sig) : ℚ := (f 0 + f 2 + f 4 + f 6) / 4

/--
Moyenne sur la classe `B = {1,3,5,7}`.

Cette coordonnée intervient elle aussi dans le projecteur du secteur `λ = 3`.
-/
def mB (f : Sig) : ℚ := (f 1 + f 3 + f 5 + f 7) / 4

/--
Coordonnée signée sur la composante `chi3`.

Elle mesure le contraste entre les deux moitiés `{0,1,2,3}` et `{4,5,6,7}`,
mais restreint ici aux indices pairs.
-/
def alpha (f : Sig) : ℚ := f 0 + f 2 - f 4 - f 6

/--
Coordonnée signée complémentaire sur la composante `chi15`,
restreinte ici aux indices impairs.
-/
def beta (f : Sig) : ℚ := f 1 + f 3 - f 5 - f 7

-- ═══════════════════════════════════════════════════════════
-- Projecteurs spectraux
-- ═══════════════════════════════════════════════════════════

/--
Projecteur cohérent `P₃` sur le secteur propre `λ = 3`.

Image :
- composante portée par `one`,
- plus composante portée par `chi5`.
-/
def p3 (f : Sig) : Sig :=
  let a := mA f
  let b := mB f
  ![a, b, a, b, a, b, a, b]

/--
Projecteur de défaut `P₋` sur le secteur propre `λ = -1`.

Il est engendré par `chi3` et `chi15`.
-/
def pminus (f : Sig) : Sig :=
  let a := alpha f / 4
  let b := beta f / 4
  ![a, b, a, b, -a, -b, -a, -b]

/--
Projecteur neutre `P₁ = Id - P₃ - P₋`.

Il récupère le secteur spectral intermédiaire `λ = 1`.
-/
def p1 (f : Sig) : Sig := fun i => f i - p3 f i - pminus f i

-- ═══════════════════════════════════════════════════════════
-- Canaux quadratiques / observables du défaut
-- ═══════════════════════════════════════════════════════════

/--
Canal `χ₃` : coefficient de Fourier discret de `f` sur `chi3`.
-/
def B3 (f : Sig) : ℚ := dot f chi3

/--
Canal `χ₁₅` : coefficient de Fourier discret de `f` sur `chi15`.
-/
def B15 (f : Sig) : ℚ := dot f chi15

-- ═══════════════════════════════════════════════════════════
-- Opérateur de Cayley exact
-- ═══════════════════════════════════════════════════════════

/--
Translation correspondant au facteur `(1,0)` dans la lecture CRT.
-/
def perm10 : Fin 8 → Fin 8 := ![4, 5, 6, 7, 0, 1, 2, 3]

/--
Translation correspondant au facteur `(1,1)` dans la lecture CRT.
-/
def perm11 : Fin 8 → Fin 8 := ![2, 4, 0, 6, 1, 7, 3, 5]

/--
Translation correspondant au facteur `(2,9)` dans la lecture CRT.
-/
def perm29 : Fin 8 → Fin 8 := ![7, 6, 5, 4, 3, 2, 1, 0]

/--
Translation correspondant au facteur `(1,2)` dans la lecture CRT.
-/
def perm12 : Fin 8 → Fin 8 := ![6, 7, 4, 5, 2, 3, 0, 1]

/--
Action combinatoire exacte du triplet de Couret :

`A_TC(f)(i) = f(i) + f(perm10 i) + f(perm12 i)`.

C’est la version fonctionnelle de la matrice de Cayley.
-/
def A_TC (f : Sig) : Sig := fun i => f i + f (perm10 i) + f (perm12 i)

-- ═══════════════════════════════════════════════════════════
-- Version matricielle finie
-- ═══════════════════════════════════════════════════════════

/-- Type des matrices rationnelles `8 × 8`. -/
abbrev QMat := Fin 8 → Fin 8 → ℚ

/--
Matrice de Cayley exacte du triplet de Couret.

Cette matrice est le miroir rationnel de `Spectral/FiniteCore.cayleyMatrix`.
Chaque ligne contient exactement trois `1`, reflétant la règle
« identité + deux translations ».
-/
def cayleyMat : QMat
  | ⟨0, _⟩ => ![1, 0, 0, 0, 1, 0, 1, 0]
  | ⟨1, _⟩ => ![0, 1, 0, 0, 0, 1, 0, 1]
  | ⟨2, _⟩ => ![0, 0, 1, 0, 1, 0, 1, 0]
  | ⟨3, _⟩ => ![0, 0, 0, 1, 0, 1, 0, 1]
  | ⟨4, _⟩ => ![1, 0, 1, 0, 1, 0, 0, 0]
  | ⟨5, _⟩ => ![0, 1, 0, 1, 0, 1, 0, 0]
  | ⟨6, _⟩ => ![1, 0, 1, 0, 0, 0, 1, 0]
  | ⟨7, _⟩ => ![0, 1, 0, 1, 0, 0, 0, 1]

/--
Action matricielle finie : `Mv`.
-/
def mv (M : QMat) (v : Sig) : Sig :=
  fun i => (List.finRange 8).foldl (fun acc j => acc + M i j * v j) 0

/-- Multiplication scalaire d’un signal. -/
def sv (k : ℚ) (v : Sig) : Sig := fun i => k * v i

/--
Égalité booléenne de deux signaux.

Cette forme est pratique pour les preuves automatisées par `native_decide`.
-/
def veq (u v : Sig) : Bool :=
  (List.finRange 8).all fun i => u i == v i

/-- Produit matriciel fini. -/
def mm (M N : QMat) : QMat :=
  fun i j => (List.finRange 8).foldl (fun acc k => acc + M i k * N k j) 0

/-- Trace finie d’une matrice. -/
def tr (M : QMat) : ℚ :=
  (List.finRange 8).foldl (fun acc i => acc + M i i) 0

/--
Égalité booléenne de matrices.

Là encore, cette présentation est adaptée aux vérifications exhaustives
par décision native.
-/
def meq (M N : QMat) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j => M i j == N i j

/-- Matrice scalaire `k · I`. -/
def scI (k : ℚ) : QMat := fun i j => if i = j then k else 0

/-- Soustraction matricielle. -/
def msub (M N : QMat) : QMat := fun i j => M i j - N i j

/-- Matrice nulle. -/
def mzero : QMat := fun _ _ => 0

-- ═══════════════════════════════════════════════════════════
-- Garde épistémique
-- ═══════════════════════════════════════════════════════════

/--
Garde épistémique : ce fichier ne revendique aucun théorème global
sur RH/GRH ou Hilbert–Pólya.
-/
def RHClaimed : Bool := false

/-- Vérification formelle de la garde épistémique. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Finite