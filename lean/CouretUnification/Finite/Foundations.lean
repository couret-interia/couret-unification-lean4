import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace CouretUnification.Finite

/-!
# Fondations spectrales T1-T7 sur Fin 8 → ℚ
Ordre : 0↦1, 1↦7, 2↦11, 3↦13, 4↦17, 5↦19, 6↦23, 7↦29
Tout est décidable par native_decide.
-/

abbrev Sig := Fin 8 → ℚ

-- Produit scalaire et norme
def dot (f g : Sig) : ℚ :=
  (List.finRange 8).foldl (fun acc i => acc + f i * g i) 0
def normSq (f : Sig) : ℚ := dot f f

-- 4 caractères réels de G₃₀
def one   : Sig := ![1,  1,  1,  1,  1,  1,  1,  1]
def chi5  : Sig := ![1, -1,  1, -1, -1,  1, -1,  1]
def chi3  : Sig := ![1,  1, -1,  1, -1, -1, -1,  1]
def chi15 : Sig := ![1, -1, -1, -1,  1, -1,  1,  1]

-- Indicatrice TC = {1,11,29} → indices {0,2,7}
def tcInd : Sig := ![1, 0, 1, 0, 0, 0, 0, 1]

-- Coordonnées de Couret
def mA    (f : Sig) : ℚ := (f 0 + f 2 + f 5 + f 7) / 4
def mB    (f : Sig) : ℚ := (f 1 + f 3 + f 4 + f 6) / 4
def alpha (f : Sig) : ℚ := f 0 - f 2 + f 5 - f 7
def beta  (f : Sig) : ℚ := f 1 + f 3 - f 4 - f 6

-- Projecteur cohérent P₃ (eigenspace λ=3)
def p3 (f : Sig) : Sig :=
  let a := mA f; let b := mB f
  ![a, b, a, b, b, a, b, a]

-- Projecteur de défaut P₋ (eigenspace λ=−1)
def pminus (f : Sig) : Sig :=
  let a := alpha f / 4; let b := beta f / 4
  ![a, b, -a, b, -b, a, -b, -a]

-- Projecteur neutre P₁ = Id - P₃ - P₋
def p1 (f : Sig) : Sig := fun i => f i - p3 f i - pminus f i

-- Canaux quadratiques
def B3  (f : Sig) : ℚ := dot f chi3
def B15 (f : Sig) : ℚ := dot f chi15

-- Opérateur de Cayley
def perm11 : Fin 8 → Fin 8 := ![2, 4, 0, 6, 1, 7, 3, 5]
def perm29 : Fin 8 → Fin 8 := ![7, 6, 5, 4, 3, 2, 1, 0]
def A_TC (f : Sig) : Sig := fun i => f i + f (perm11 i) + f (perm29 i)

-- Matrice de Cayley (pour vérifications directes)
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
def tr (M : QMat) : ℚ := (List.finRange 8).foldl (fun acc i => acc + M i i) 0
def meq (M N : QMat) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j => M i j == N i j
def scI (k : ℚ) : QMat := fun i j => if i = j then k else 0
def msub (M N : QMat) : QMat := fun i j => M i j - N i j
def mzero : QMat := fun _ _ => 0

end CouretUnification.Finite
