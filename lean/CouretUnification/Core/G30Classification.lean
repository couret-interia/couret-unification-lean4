import Mathlib.Tactic

/-!
# Classification spectrale finie des triplets de G₃₀

Couret–Unification — pièce-mère « Classification spectrale finie des triplets de G₃₀ ».
Formalise la PARTIE FINIE par énumération exhaustive sur les 56 triplets.

## Énoncés principaux (tous par `decide` / `native_decide`)

- `dichotomy`     : tout triplet de G₃₀ est de type Q ou de type C.
- `count_Q`       : il y a exactement 24 triplets de type Q (spectre (9,1⁶), ratio 3/5).
- `count_C`       : il y a exactement 32 triplets de type C (spectre (5,5,1⁵)).
- `total_56`      : 24 + 32 = 56 = C(8,3) (aucun autre spectre possible).
- `twoFixed_count`: exactement 2 triplets sont fixes sous Aut(G₃₀).
- `twoFixed_members` : ces deux triplets sont {1,11,29} et {11,19,29}.

## Conventions (ALIGNÉES sur `Core/QuadraticResonance.lean`)

- G₃₀ ≃ ⟨29⟩ × ⟨7⟩ ≃ C₂ × C₄ via `(a, b) ↦ 29^a · 7^b mod 30`.
- `crtCoord` est IDENTIQUE à celle de `QuadraticResonance.lean` (table partagée,
  vérifiée lettre pour lettre).
- Caractères χ_{m,n}(29^a·7^b) = (-1)^(m·a) · i^(n·b), (m,n) ∈ Fin 2 × Fin 4.
- Entiers de Gauss représentés comme `Int × Int` (cohérent avec `Classification63.GI`).

## Statut

[D-computational, local] + hash archivé + ai_lock external_certified.
Périmètre : géométrie spectrale finie de G₃₀. AUCUNE portée sur les premiers réels.
Ne lève pas la quarantaine CUI-Q-014 (transport 3/5 vers les premiers).

## Note de cohérence inter-conventions

La classification (dichotomie, comptages, orbites) est INVARIANTE par le choix de
paramétrisation du groupe dual : le spectre d'un triplet est l'ensemble non ordonné
des 7 énergies non triviales, invariant par relabeling des caractères. La convention
`a3/dlog5` du squelette de rédaction et la convention `crtCoord` du dépôt diffèrent
pour 4 éléments mais donnent rigoureusement les mêmes 56 spectres (vérifié en amont).
On fige ici la convention `crtCoord` du dépôt.
-/

namespace CouretUnification.Core.G30Classification

/-! ## §1. Entiers de Gauss (exacts, pas de flottants) -/

abbrev GZ := Int × Int

@[inline] def gAdd (z w : GZ) : GZ := (z.1 + w.1, z.2 + w.2)
@[inline] def gMul (z w : GZ) : GZ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
@[inline] def gNormSq (z : GZ) : Int := z.1 * z.1 + z.2 * z.2

/-- i^n comme entier de Gauss (période 4). -/
@[inline] def iPow (n : Nat) : GZ :=
  match n % 4 with
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (-1, 0) | _ => (0, -1)

/-- (-1)^n comme entier de Gauss. -/
@[inline] def signPow (n : Nat) : GZ :=
  if n % 2 = 0 then (1, 0) else (-1, 0)

/-! ## §2. Les 8 unités de G₃₀ et leurs coordonnées CRT

Table IDENTIQUE à `QuadraticResonance.crtCoord` (convention 29^a · 7^b mod 30).
-/

/-- Les 8 unités mod 30, dans l'ordre documentaire. -/
def G : List Nat := [1, 7, 11, 13, 17, 19, 23, 29]

/-- Indexation positionnelle 0..7 → valeur de l'unité. -/
@[inline] def unitValue : Fin 8 → Nat
  | ⟨0, _⟩ => 1   | ⟨1, _⟩ => 7   | ⟨2, _⟩ => 11  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17  | ⟨5, _⟩ => 19  | ⟨6, _⟩ => 23  | ⟨7, _⟩ => 29

/-- Coordonnées CRT (a, b) telles que unitValue i = 29^a · 7^b mod 30.
    IDENTIQUE à `QuadraticResonance.crtCoord`. -/
@[inline] def crtCoord : Fin 8 → Nat × Nat
  | ⟨0, _⟩ => (0, 0)  -- 1
  | ⟨1, _⟩ => (0, 1)  -- 7
  | ⟨2, _⟩ => (1, 2)  -- 11
  | ⟨3, _⟩ => (0, 3)  -- 13
  | ⟨4, _⟩ => (1, 3)  -- 17
  | ⟨5, _⟩ => (0, 2)  -- 19
  | ⟨6, _⟩ => (1, 1)  -- 23
  | ⟨7, _⟩ => (1, 0)  -- 29

/-- Vérification CRT : 29^a · 7^b mod 30 = unitValue i. -/
def crt_decomposition_correct : Bool :=
  (List.finRange 8).all fun i =>
    let (a, b) := crtCoord i
    let pow29 := if a = 0 then 1 else 29
    let pow7 := match b with | 0 => 1 | 1 => 7 | 2 => 49 % 30 | 3 => (49 * 7) % 30 | _ => 0
    (pow29 * pow7) % 30 = unitValue i

theorem crt_decomposition : crt_decomposition_correct = true := by native_decide

/-- La table `unitValue` énumère bien des unités mod 30 (coprimes à 30), toutes distinctes. -/
def unitValue_coprime_30 : Bool :=
  (List.finRange 8).all fun i => Nat.gcd (unitValue i) 30 = 1

theorem unitValue_in_G30 : unitValue_coprime_30 = true := by decide

/-! ## §3. Caractères et énergie spectrale -/

abbrev QuadCharIdx := Fin 2 × Fin 4

/-- χ_{m,n}(unité i) = (-1)^(m·a) · i^(n·b), comme entier de Gauss. -/
@[inline] def evalChar (χ : QuadCharIdx) (i : Fin 8) : GZ :=
  let (m, n) := χ
  let (a, b) := crtCoord i
  gMul (signPow (m.val * a)) (iPow (n.val * b))

/-- Les 7 caractères non triviaux. -/
def nonTrivialChars : List QuadCharIdx :=
  [(⟨0,by decide⟩, ⟨1,by decide⟩), (⟨0,by decide⟩, ⟨2,by decide⟩),
   (⟨0,by decide⟩, ⟨3,by decide⟩), (⟨1,by decide⟩, ⟨0,by decide⟩),
   (⟨1,by decide⟩, ⟨1,by decide⟩), (⟨1,by decide⟩, ⟨2,by decide⟩),
   (⟨1,by decide⟩, ⟨3,by decide⟩)]

/-! ## §4. Les 56 triplets (sous-ensembles de taille 3 de Fin 8) -/

/-- Sous-listes de taille 2. -/
def choose2 : List (Fin 8) → List (List (Fin 8))
  | []        => []
  | a :: rest => (rest.map (fun b => [a, b])) ++ choose2 rest

/-- Sous-listes de taille 3. -/
def choose3 : List (Fin 8) → List (List (Fin 8))
  | []        => []
  | a :: rest => ((choose2 rest).map (fun p => a :: p)) ++ choose3 rest

/-- Les 56 triplets, indexés par positions dans Fin 8. -/
def triplets : List (List (Fin 8)) := choose3 (List.finRange 8)

/-- Énergie centrée du triplet T sur le caractère χ : |Σ_{i∈T} χ(i)|².
    (Le centrage 1_T − 3/8 annule le caractère trivial ; sur un caractère non
    trivial, la part constante 3/8 ne contribue pas.) -/
def energy (T : List (Fin 8)) (χ : QuadCharIdx) : Int :=
  gNormSq (T.foldl (fun acc i => gAdd acc (evalChar χ i)) (0, 0))

/-- Le spectre non trivial : les 7 énergies. -/
def spectrum (T : List (Fin 8)) : List Int := nonTrivialChars.map (energy T)

/-! ## §5. Dichotomie spectrale -/

/-- Type Q : spectre (9, 1, 1, 1, 1, 1, 1) — ratio dominant 3/5. -/
def isTypeQ (T : List (Fin 8)) : Bool :=
  ((spectrum T).countP (· == 9) == 1) && ((spectrum T).countP (· == 1) == 6)

/-- Type C : spectre (5, 5, 1, 1, 1, 1, 1) — ratio dominant 1/3. -/
def isTypeC (T : List (Fin 8)) : Bool :=
  ((spectrum T).countP (· == 5) == 2) && ((spectrum T).countP (· == 1) == 5)

/-- **THÉORÈME (dichotomie).** Tout triplet de G₃₀ est de type Q ou de type C. -/
theorem dichotomy :
    (triplets.all (fun T => isTypeQ T || isTypeC T)) = true := by
  native_decide

/-- **THÉORÈME.** Exactement 24 triplets de type Q. -/
theorem count_Q : (triplets.filter isTypeQ).length = 24 := by native_decide

/-- **THÉORÈME.** Exactement 32 triplets de type C. -/
theorem count_C : (triplets.filter isTypeC).length = 32 := by native_decide

/-- **THÉORÈME.** 24 + 32 = 56 = C(8,3) : la dichotomie est exhaustive. -/
theorem total_56 :
    (triplets.filter isTypeQ).length + (triplets.filter isTypeC).length = 56 := by
  native_decide

/-- **THÉORÈME.** L'énergie totale non triviale est constante = 15 (Parseval). -/
def total_energy_const : Bool :=
  triplets.all (fun T => (spectrum T).foldl (· + ·) 0 == 15)

theorem parseval_total_15 : total_energy_const = true := by native_decide

/-! ## §6. Aut(G₃₀) et rigidité — les deux triplets fixes -/

/-- Les 8 automorphismes de G₃₀, donnés par l'image de
    [1, 7, 11, 13, 17, 19, 23, 29] (table positionnelle alignée sur `G`). -/
def autTable : List (List Nat) :=
  [ [1,  7, 11, 13, 17, 19, 23, 29],
    [1,  7, 29, 13, 23, 19, 17, 11],
    [1, 13, 11,  7, 23, 19, 17, 29],
    [1, 13, 29,  7, 17, 19, 23, 11],
    [1, 17, 11, 23,  7, 19, 13, 29],
    [1, 17, 29, 23, 13, 19,  7, 11],
    [1, 23, 11, 17, 13, 19,  7, 29],
    [1, 23, 29, 17,  7, 19, 13, 11] ]

/-- Image de la valeur x par l'automorphisme s (table positionnelle alignée sur G). -/
def applyAut (s : List Nat) (x : Nat) : Nat :=
  (((G.zip s).find? (fun p => p.1 == x)).map (·.2)).getD x

/-- T (valeurs) est fixé ensemblistement par s ssi chaque image est dans T. -/
def fixedBy (s : List Nat) (Tvals : List Nat) : Bool :=
  (Tvals.map (applyAut s)).all (fun y => Tvals.contains y)

/-- T (valeurs) est fixé par tous les automorphismes. -/
def fixedByAll (Tvals : List Nat) : Bool := autTable.all (fun s => fixedBy s Tvals)

/-- Les 56 triplets en VALEURS (pour le test de fixité). -/
def tripletsVals : List (List Nat) := triplets.map (fun T => T.map unitValue)

/-- **THÉORÈME (rigidité).** Exactement 2 triplets sont fixes sous Aut(G₃₀). -/
theorem twoFixed_count : (tripletsVals.filter fixedByAll).length = 2 := by native_decide

/-- **THÉORÈME.** Les deux triplets fixes sont {1,11,29} et {11,19,29}. -/
theorem twoFixed_members :
    fixedByAll [1, 11, 29] = true ∧ fixedByAll [11, 19, 29] = true := by decide

/-! ## §7bis. Lecture documentaire du triplet Couret T_C = {1, 11, 29}

`T_C = {1, 11, 29}` n'est NI unique par énergie (il est l'un des 24 triplets de
type Q), NI l'unique triplet fixe (il y en a deux). Sa spécificité est
DOCUMENTAIRE (corpus Couret), non une unicité mathématique. Ce qu'on gagne est
une rigidité finie, pas une loi globale.
-/

/-- T_C = {1, 11, 29} est de type Q. -/
theorem TC_is_typeQ : isTypeQ [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩] = true := by
  native_decide

/-! ## §8. Caractérisation conceptuelle — Type Q ⟺ fibre quadratique − un point

La dichotomie des §5 est énumérative (comptage des spectres). Le cœur conceptuel de
la pièce-mère est la RÉCIPROQUE STRUCTURELLE : un triplet est de type Q si et seulement
s'il est contenu dans une fibre d'un caractère quadratique (= fibre quadratique privée
d'un point). Cette caractérisation est elle-même finie, donc énumérable.

Les 3 caractères quadratiques de G₃₀ sont χ_{0,2}, χ_{1,0}, χ_{1,2} (valeurs ±1).
Une fibre quadratique est {i : χ(i) = ε} pour χ quadratique, ε ∈ {+1, −1} (taille 4).
-/

/-- Les 3 indices de caractères quadratiques (valeurs réelles ±1). -/
def quadraticChars : List QuadCharIdx :=
  [(⟨0,by decide⟩, ⟨2,by decide⟩), (⟨1,by decide⟩, ⟨0,by decide⟩),
   (⟨1,by decide⟩, ⟨2,by decide⟩)]

/-- χ(i) vaut-il ε ∈ {+1,−1} ? (sur un caractère quadratique, evalChar est (±1,0)). -/
@[inline] def charEqualsSign (χ : QuadCharIdx) (i : Fin 8) (ε : Int) : Bool :=
  evalChar χ i == (ε, 0)

/-- Le triplet T (positions) est-il contenu dans une fibre d'un caractère quadratique ? -/
def inSomeQuadFiber (T : List (Fin 8)) : Bool :=
  quadraticChars.any fun χ =>
    ([(1 : Int), -1]).any fun ε =>
      T.all fun i => charEqualsSign χ i ε

/-- **THÉORÈME (caractérisation structurelle).** Un triplet est de type Q si et
    seulement s'il est contenu dans une fibre quadratique (= fibre quadratique privée
    d'un point). C'est le cœur de la pièce-mère (réciproque de CUI-D-007). -/
theorem typeQ_iff_quadratic_fiber :
    triplets.all (fun T => isTypeQ T == inSomeQuadFiber T) = true := by
  native_decide

/-! ## §9. Ancre doctrinale

Selon la convention de fin de fichier du dépôt (`RHClaimed_false_AlgebraTC : True := trivial`),
ce théorème ne prouve aucun contenu mathématique supplémentaire. Il sert uniquement de
marqueur documentaire SI le fichier compile dans le périmètre Frozen — la certification
effective vient du `lake build` de Thomas et de l'archivage du hash, pas de la présence
de ce marqueur.

Périmètre : G₃₀ fini. AUCUN transport vers les premiers réels.
Ne lève pas CUI-Q-014.

Invariants préservés : RHClaimed = false. ScopeExpansionClaimed = false.
-/
theorem G30Classification_machine_anchor : True := trivial

end CouretUnification.Core.G30Classification
