import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Finite

/-!
# Fondations spectrales T1-T7 sur Fin 8 → ℚ
Ordre : 0↦1, 1↦7, 2↦11, 3↦13, 4↦17, 5↦19, 6↦23, 7↦29

Cette version est le miroir rationnel de `Spectral/FiniteCore.lean` :
- même matrice de Cayley exacte ;
- même secteur propre λ = 3 engendré par `one` et `chi5`;
- même secteur propre λ = -1 engendré par `chi3` et `chi15`.
-/

abbrev Sig := Fin 8 → ℚ

-- Produit scalaire et norme
def dot (f g : Sig) : ℚ :=
  (List.finRange 8).foldl (fun acc i => acc + f i * g i) 0

def normSq (f : Sig) : ℚ := dot f f

-- 4 caractères réels compatibles avec la matrice exacte
-- one  : trivial
-- chi5 : vecteur alterné (miroir rationnel de FiniteCore.altVec), λ = 3
-- chi3 : caractère du facteur C2, λ = -1
-- chi15: produit chi3 * chi5, λ = -1
def one   : Sig := ![1,  1,  1,  1,  1,  1,  1,  1]
def chi5  : Sig := ![1, -1,  1, -1,  1, -1,  1, -1]
def chi3  : Sig := ![1,  1,  1,  1, -1, -1, -1, -1]
def chi15 : Sig := ![1, -1,  1, -1, -1,  1, -1,  1]

-- Alias utile vers le fichier spectral réel
abbrev altVec : Sig := chi5

-- Indicatrice TC = {1,11,29} → indices {0,2,7}
def tcInd : Sig := ![1, 0, 1, 0, 0, 0, 0, 1]

-- Coordonnées adaptées au vrai secteur λ = 3 :
--   A = {0,2,4,6}, B = {1,3,5,7}
def mA    (f : Sig) : ℚ := (f 0 + f 2 + f 4 + f 6) / 4
def mB    (f : Sig) : ℚ := (f 1 + f 3 + f 5 + f 7) / 4

-- Coordonnées adaptées au vrai secteur λ = -1
def alpha (f : Sig) : ℚ := f 0 + f 2 - f 4 - f 6
def beta  (f : Sig) : ℚ := f 1 + f 3 - f 5 - f 7

-- Projecteur cohérent P₃ (eigenspace λ = 3 = span{one, chi5})
def p3 (f : Sig) : Sig :=
  let a := mA f
  let b := mB f
  ![a, b, a, b, a, b, a, b]

-- Projecteur de défaut P₋ (eigenspace λ = -1 = span{chi3, chi15})
def pminus (f : Sig) : Sig :=
  let a := alpha f / 4
  let b := beta f / 4
  ![a, b, a, b, -a, -b, -a, -b]

-- Projecteur neutre P₁ = Id - P₃ - P₋
def p1 (f : Sig) : Sig := fun i => f i - p3 f i - pminus f i

-- Canaux quadratiques
def B3  (f : Sig) : ℚ := dot f chi3
def B15 (f : Sig) : ℚ := dot f chi15

-- Opérateur de Cayley exact pour T_C = {(0,0),(1,0),(1,2)}
-- dans l’ordre 0..7 choisi.
def perm10 : Fin 8 → Fin 8 := ![4, 5, 6, 7, 0, 1, 2, 3]
def perm12 : Fin 8 → Fin 8 := ![6, 7, 4, 5, 2, 3, 0, 1]

def A_TC (f : Sig) : Sig := fun i => f i + f (perm10 i) + f (perm12 i)

-- Matrice de Cayley exacte (identique à Spectral/FiniteCore.cayleyMatrix)
abbrev QMat := Fin 8 → Fin 8 → ℚ

def cayleyMat : QMat
  | ⟨0, _⟩ => ![1, 0, 0, 0, 1, 0, 1, 0]
  | ⟨1, _⟩ => ![0, 1, 0, 0, 0, 1, 0, 1]
  | ⟨2, _⟩ => ![0, 0, 1, 0, 1, 0, 1, 0]
  | ⟨3, _⟩ => ![0, 0, 0, 1, 0, 1, 0, 1]
  | ⟨4, _⟩ => ![1, 0, 1, 0, 1, 0, 0, 0]
  | ⟨5, _⟩ => ![0, 1, 0, 1, 0, 1, 0, 0]
  | ⟨6, _⟩ => ![1, 0, 1, 0, 0, 0, 1, 0]
  | ⟨7, _⟩ => ![0, 1, 0, 1, 0, 0, 0, 1]

def mv (M : QMat) (v : Sig) : Sig :=
  fun i => (List.finRange 8).foldl (fun acc j => acc + M i j * v j) 0

def sv (k : ℚ) (v : Sig) : Sig := fun i => k * v i
def veq (u v : Sig) : Bool := (List.finRange 8).all fun i => u i == v i

def mm (M N : QMat) : QMat :=
  fun i j => (List.finRange 8).foldl (fun acc k => acc + M i k * N k j) 0

def tr (M : QMat) : ℚ :=
  (List.finRange 8).foldl (fun acc i => acc + M i i) 0

def meq (M N : QMat) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j => M i j == N i j

def scI (k : ℚ) : QMat := fun i j => if i = j then k else 0
def msub (M N : QMat) : QMat := fun i j => M i j - N i j
def mzero : QMat := fun _ _ => 0

end CouretUnification.Finite