/-
  CouretUnification/Core/LMFDBAlignment.lean
  Alignement entre l'indexation CharIdx du dépôt et la convention Conrey
  utilisée par la LMFDB (www.lmfdb.org).

  La permutation ci-dessous a été calculée par évaluation explicite
  des 8 caractères du dépôt sur les 8 résidus coprimes à 30, et
  matching avec les caractères Conrey :

      χ_{30, n}(m) = (-1)^(a_n · a_m) · i^(b_n · b_m)

  où (a_r, b_r) est la coord Conrey du résidu r :
    a_r = 0 si r ≡ 1 (mod 3), 1 si r ≡ 2 (mod 3)
    b_r = index de (r mod 5) dans le cycle 2^k : 1→0, 2→1, 4→2, 3→3.

  Script de calcul : lmfdb_alignment.py (cf. pack d'avancement).

  RHClaimed = false.
-/

import CouretUnification.Core.Characters30
import CouretUnification.Logic.H3.ParityGamma30

namespace CouretUnification.Core

-- ═══════════════════════════════════════════════════════════════════
-- §1. Résidus coprimes à 30
-- ═══════════════════════════════════════════════════════════════════

/-- Les 8 résidus coprimes à 30, indexés comme entiers naturels.
    Cet ordre (1, 7, 11, 13, 17, 19, 23, 29) est celui du dépôt
    (g30ToIdx et residues_by_idx). -/
def coprime30Residue : Fin 8 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 11
  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17
  | ⟨5, _⟩ => 19
  | ⟨6, _⟩ => 23
  | ⟨7, _⟩ => 29

/-- Le résidu correspondant à un CharIdx (via la permutation). -/
def charIdxToConreyResidue (χ : CharIdx) : ℕ :=
  match χ with
  | ⟨0, _⟩ => 1    -- char trivial
  | ⟨1, _⟩ => 17   -- order 4, even, conductor 15, orbit 30.e
  | ⟨2, _⟩ => 23   -- order 4, even, conductor 15, orbit 30.e
  | ⟨3, _⟩ => 7    -- order 4, odd,  conductor 5,  orbit 30.f
  | ⟨4, _⟩ => 19   -- order 2, even, conductor 5,  orbit 30.b ou 30.c
  | ⟨5, _⟩ => 13   -- order 4, odd,  conductor 5,  orbit 30.f
  | ⟨6, _⟩ => 11   -- order 2, odd,  conductor 3,  orbit 30.c ou 30.d
  | ⟨7, _⟩ => 29   -- order 2, odd,  conductor 15, orbit 30.d

-- ═══════════════════════════════════════════════════════════════════
-- §2. Propriétés élémentaires
-- ═══════════════════════════════════════════════════════════════════

/-- Chaque résidu image est bien coprime à 30. -/
theorem charIdxToConreyResidue_coprime (χ : CharIdx) :
    Nat.Coprime (charIdxToConreyResidue χ) 30 := by
  fin_cases χ <;> decide

/-- Chaque résidu image est dans {1, 7, 11, 13, 17, 19, 23, 29}. -/
theorem charIdxToConreyResidue_mem (χ : CharIdx) :
    charIdxToConreyResidue χ ∈ ({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  fin_cases χ <;> decide

/-- La fonction charIdxToConreyResidue est une bijection entre
    CharIdx et les 8 résidus coprimes à 30. -/
theorem charIdxToConreyResidue_injective :
    Function.Injective charIdxToConreyResidue := by
  intro χ ψ h
  fin_cases χ <;> fin_cases ψ <;> simp [charIdxToConreyResidue] at h <;>
    first | rfl

-- ═══════════════════════════════════════════════════════════════════
-- §3. Ordres, parités, conducteurs
-- ═══════════════════════════════════════════════════════════════════

/-- Ordre du caractère Conrey associé à un CharIdx. -/
def conreyOrder (χ : CharIdx) : ℕ :=
  match χ with
  | ⟨0, _⟩ => 1    -- trivial
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 2

/-- Parité du caractère Conrey. True = even (χ(-1) = 1), False = odd. -/
def conreyIsEven (χ : CharIdx) : Bool :=
  match χ with
  | ⟨0, _⟩ => true   -- trivial
  | ⟨1, _⟩ => true   -- 17, coord (1,1) : (-1)^(1+1) = 1
  | ⟨2, _⟩ => true   -- 23, coord (1,3) : (-1)^(1+3) = 1
  | ⟨3, _⟩ => false  -- 7,  coord (0,1) : (-1)^(0+1) = -1
  | ⟨4, _⟩ => true   -- 19, coord (0,2) : (-1)^(0+2) = 1
  | ⟨5, _⟩ => false  -- 13, coord (0,3) : (-1)^(0+3) = -1
  | ⟨6, _⟩ => false  -- 11, coord (1,0) : (-1)^(1+0) = -1
  | ⟨7, _⟩ => false  -- 29, coord (1,2) : (-1)^(1+2) = -1

/-- Conducteur du caractère Conrey. -/
def conreyConductor (χ : CharIdx) : ℕ :=
  match χ with
  | ⟨0, _⟩ => 1    -- trivial
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 15
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 3
  | ⟨7, _⟩ => 15

-- ═══════════════════════════════════════════════════════════════════
-- §4. Cohérence avec la lecture parityBit du dépôt
-- ═══════════════════════════════════════════════════════════════════
-- Théorème de cohérence : la parité lue par parityBit (doctrine v35.1)
-- coïncide avec la parité Conrey (LMFDB) pour tous les caractères.

/-- Cohérence de la lecture parité : charIsEven (dépôt) ↔ conreyIsEven. -/
theorem parity_coherent (χ : CharIdx) :
    (CouretUnification.Logic.H3.charIsEven χ) ↔ conreyIsEven χ = true := by
  fin_cases χ <;>
    simp [CouretUnification.Logic.H3.charIsEven, CouretUnification.Logic.H3.parityBit,
          conreyIsEven] <;> decide

-- ═══════════════════════════════════════════════════════════════════
-- §5. Orbit Galois
-- ═══════════════════════════════════════════════════════════════════
-- Les 6 orbits Galois des caractères mod 30. Le nommage 30.a à 30.f
-- suit la convention LMFDB sans que les lettres précises (hors 30.a et
-- 30.d) soient validées sans inspection live de lmfdb.org.

/-- Identifiant d'orbit Galois LMFDB. Nommage conjectural sauf 30.a et 30.d. -/
inductive GaloisOrbitLabel
  | a  -- trivial {1}
  | b  -- singleton even ordre 2  — {19} (conjecturé)
  | c  -- singleton odd  ordre 2  — {11} (conjecturé)
  | d  -- singleton odd  ordre 2  — {29} (confirmé par newform 30.3.b.a)
  | e  -- pair even ordre 4       — {17, 23}
  | f  -- pair odd  ordre 4       — {7, 13}
  deriving DecidableEq

def charIdxToOrbit (χ : CharIdx) : GaloisOrbitLabel :=
  match χ with
  | ⟨0, _⟩ => .a
  | ⟨1, _⟩ => .e   -- 17
  | ⟨2, _⟩ => .e   -- 23
  | ⟨3, _⟩ => .f   -- 7
  | ⟨4, _⟩ => .b   -- 19 (conjecturé)
  | ⟨5, _⟩ => .f   -- 13
  | ⟨6, _⟩ => .c   -- 11 (conjecturé)
  | ⟨7, _⟩ => .d   -- 29

end CouretUnification.Core
