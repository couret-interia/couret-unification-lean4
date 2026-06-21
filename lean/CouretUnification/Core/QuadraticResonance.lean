import CouretUnification.Core.Classification63
import Mathlib.Tactic

-- Verrouillage doctrinal : QuadraticResonance dépend du choix Classification63.GI = Int × Int
example : (CouretUnification.Core.Classification63.GI) = (Int × Int) := rfl

/-!
# Résonance quadratique du triplet canonique

Couret–Unification, théorème A.4 (rapport v1.3 §6.4bis).

## Énoncé principal

Pour le triplet canonique `T_C = {1, 11, 29} ⊂ G₃₀ = (ℤ/30ℤ)ˣ`, le noyau
centré `k_A := 𝟙_{T_C} - 3/8` possède une énergie de Fourier égale à 9 sur le
caractère quadratique χ_{0,2}, et une énergie égale à 1 sur chacun des six
autres caractères non triviaux :

  |k̂_A(χ_{0,2})|² = 9,   |k̂_A(χ)|² = 1   pour les six autres.

Énergie non triviale totale : 15.  Dominance : 9/15 = 3/5.

## Énoncé complémentaire (A.4')

Pour l’orbite quadratique complète `A₄ = {1, 11, 19, 29} = QR₅ ∩ G₃₀`, le noyau
centré `k_{A₄} := 𝟙_{A₄} - 1/2` EST exactement proportionnel au caractère
quadratique : `k_{A₄}(x) = (1/2) · (x/5)` pour tout x ∈ G₃₀.

Ainsi |k̂_{A₄}(χ_{0,2})|² = 16, toutes les six autres énergies non triviales = 0,
dominance 1 (alignement total).

## Conventions

- Nous utilisons la décomposition CRT `G₃₀ ≃ ⟨29⟩ × ⟨7⟩ ≃ C₂ × C₄`
  via l’application de coordonnées `(a, b) ↦ 29^a · 7^b mod 30`.
- Les caractères sont indexés par `(m, n) ∈ Fin 2 × Fin 4` avec
  `χ_{m,n}(29^a · 7^b) = (-1)^(m·a) · i^(n·b)`.
- Pour rester dans `ℤ`, nous travaillons avec les coefficients de Fourier de
  `8 · k_A`, qui sont des entiers gaussiens (nous représentons ℤ[i] par
  `Int × Int`).

## Statut

[D] après compilation de ce fichier (post-v1.3 chantier 3).
La preuve se fait par `native_decide` sur une énumération finie.

## Emplacement du module

`CouretUnification.Core.QuadraticResonance` (nouveau fichier).
-/

namespace CouretUnification.Core.QuadraticResonance

/-! ## §1. Arithmétique des entiers gaussiens -/

@[inline] def gi_zero : CouretUnification.Core.Classification63.GI := (0, 0)
@[inline] def gi_add (z w : CouretUnification.Core.Classification63.GI) : CouretUnification.Core.Classification63.GI := (z.1 + w.1, z.2 + w.2)
@[inline] def gi_sub (z w : CouretUnification.Core.Classification63.GI) : CouretUnification.Core.Classification63.GI := (z.1 - w.1, z.2 - w.2)
@[inline] def gi_mul (z w : CouretUnification.Core.Classification63.GI) : CouretUnification.Core.Classification63.GI := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
@[inline] def gi_normSq (z : CouretUnification.Core.Classification63.GI) : Int := z.1 * z.1 + z.2 * z.2

/-- `i^n` comme entier gaussien (période 4). -/
@[inline] def gi_iPow (n : Nat) : CouretUnification.Core.Classification63.GI :=
  match n % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

/-- `(-1)^n` comme entier gaussien. -/
@[inline] def gi_signPow (n : Nat) : CouretUnification.Core.Classification63.GI :=
  if n % 2 = 0 then (1, 0) else (-1, 0)

/-! ## §2. Coordonnées CRT G₃₀ ≃ ⟨29⟩ × ⟨7⟩

Les 8 unités modulo 30 listées dans l’ordre documentaire [1, 7, 11, 13, 17, 19, 23, 29]
ont pour coordonnées CRT (a, b) ∈ {0,1} × {0,1,2,3} telles que x = 29^a · 7^b mod 30.

Calcul :
  29^0 · 7^0 =  1   → (0, 0)
  29^0 · 7^1 =  7   → (0, 1)
  29^0 · 7^2 = 19   → (0, 2)
  29^0 · 7^3 = 13   → (0, 3)
  29^1 · 7^0 = 29   → (1, 0)
  29^1 · 7^1 = 23   → (1, 1)
  29^1 · 7^2 = 11   → (1, 2)
  29^1 · 7^3 = 17   → (1, 3)
-/

/-- Indexe les 8 unités de G₃₀ par leur position dans la liste documentaire
    [1, 7, 11, 13, 17, 19, 23, 29]. -/
@[inline] def unitValue : Fin 8 → Nat
  | ⟨0, _⟩ => 1   | ⟨1, _⟩ => 7   | ⟨2, _⟩ => 11  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17  | ⟨5, _⟩ => 19  | ⟨6, _⟩ => 23  | ⟨7, _⟩ => 29

/-- Coordonnées CRT (a, b) pour chaque unité, par position. -/
@[inline] def crtCoord : Fin 8 → Nat × Nat
  | ⟨0, _⟩ => (0, 0)  -- 1
  | ⟨1, _⟩ => (0, 1)  -- 7
  | ⟨2, _⟩ => (1, 2)  -- 11
  | ⟨3, _⟩ => (0, 3)  -- 13
  | ⟨4, _⟩ => (1, 3)  -- 17
  | ⟨5, _⟩ => (0, 2)  -- 19
  | ⟨6, _⟩ => (1, 1)  -- 23
  | ⟨7, _⟩ => (1, 0)  -- 29

/-- Vérification de la décomposition CRT : 29^a · 7^b mod 30 correspond à unitValue. -/
def crt_decomposition_correct : Bool :=
  (List.finRange 8).all fun i =>
    let (a, b) := crtCoord i
    let pow29 := if a = 0 then 1 else 29
    let pow7 := match b with | 0 => 1 | 1 => 7 | 2 => 49 % 30 | 3 => (49 * 7) % 30 | _ => 0
    (pow29 * pow7) % 30 = unitValue i

theorem crt_decomposition : crt_decomposition_correct = true := by native_decide

/-! ## §3. Caractères et évaluation -/

/-- Indice de caractère χ_{m,n} pour (m, n) ∈ Fin 2 × Fin 4. -/
abbrev QuadCharIdx := Fin 2 × Fin 4

/-- Évalue χ_{m,n} sur l’unité indexée par i ∈ Fin 8, comme entier gaussien.
    χ_{m,n}(29^a · 7^b) = (-1)^(m·a) · i^(n·b). -/
@[inline] def evalChar (χ : QuadCharIdx) (i : Fin 8) : CouretUnification.Core.Classification63.GI :=
  let (m, n) := χ
  let (a, b) := crtCoord i
  gi_mul (gi_signPow (m.val * a)) (gi_iPow (n.val * b))

/-- L’indice du caractère quadratique χ_{0,2}. -/
@[inline] def chiQuadratic : QuadCharIdx := (⟨0, by decide⟩, ⟨2, by decide⟩)

/-- L’indice du caractère trivial χ_{0,0}. -/
@[inline] def chiTrivial : QuadCharIdx := (⟨0, by decide⟩, ⟨0, by decide⟩)

/-! ## §4. Le triplet canonique T_C = {1, 11, 29} -/

/-- Prédicat d’appartenance à T_C dans l’indexation par position. -/
@[inline] def memTC (i : Fin 8) : Bool :=
  unitValue i = 1 ∨ unitValue i = 11 ∨ unitValue i = 29

/-- Transformée de Fourier de 𝟙_{T_C} : somme des χ(t) pour t ∈ T_C, comme entier gaussien. -/
def fourierTC (χ : QuadCharIdx) : CouretUnification.Core.Classification63.GI :=
  (List.finRange 8).foldl
    (fun acc i => if memTC i then gi_add acc (evalChar χ i) else acc)
    gi_zero

/-- Transformée de Fourier du noyau centré 8·k_A = 8·𝟙_{T_C} - 3·𝟙_G₃₀,
    de sorte que 8·k̂_A(χ) = 8·𝟙̂_{T_C}(χ) - 3·8·δ_{χ trivial}. -/
def fourierCenteredTC (χ : QuadCharIdx) : CouretUnification.Core.Classification63.GI :=
  let raw := fourierTC χ
  -- multiplication par 8 pour éliminer les dénominateurs
  let raw8 : CouretUnification.Core.Classification63.GI := (8 * raw.1, 8 * raw.2)
  if χ = chiTrivial then gi_sub raw8 (3 * 8, 0) else raw8

/-- Norme au carré du coefficient de Fourier (mise à l’échelle par 8²=64).
    |8·k̂_A(χ)|² = 64 · |k̂_A(χ)|². -/
def fourierNormSq_scaled (χ : QuadCharIdx) : Int :=
  gi_normSq (fourierCenteredTC χ)

/-! ## §5. Théorèmes principaux pour A.4 -/

/-- Le coefficient de Fourier |8·k̂_A(χ_{0,2})|² vaut 64·9 = 576. -/
theorem fourier_quadratic_dominant :
    fourierNormSq_scaled chiQuadratic = 576 := by native_decide

/-- Pour chacun des six caractères non triviaux et non quadratiques,
    |8·k̂_A(χ)|² vaut 64·1 = 64. -/
theorem fourier_other_nontrivial_eq_64 :
    ∀ χ : QuadCharIdx, χ ≠ chiTrivial → χ ≠ chiQuadratic →
    fourierNormSq_scaled χ = 64 := by decide

/-- Le caractère trivial est annulé par le centrage. -/
theorem fourier_trivial_eq_zero :
    fourierNormSq_scaled chiTrivial = 0 := by native_decide

/-- Somme des normes au carré sur les sept caractères non triviaux, mise à l’échelle par 64.
    Elle vaut 64·(9 + 6·1) = 64·15 = 960. -/
def totalEnergyNonTrivial_scaled : Int :=
  (List.finRange 2).foldl (fun acc m =>
    (List.finRange 4).foldl (fun acc' n =>
      let χ : QuadCharIdx := (m, n)
      if χ = chiTrivial then acc' else acc' + fourierNormSq_scaled χ
    ) acc
  ) 0

theorem total_energy_eq_960 : totalEnergyNonTrivial_scaled = 960 := by native_decide

/-- **THÉORÈME PRINCIPAL A.4 (résonance quadratique de T_C).**

    Le rapport entre l’énergie portée par χ_{0,2} et l’énergie non triviale totale vaut 3/5.

    Sous forme entière : 5 · |8·k̂_A(χ_{0,2})|² = 3 · totalEnergyNonTrivial_scaled,
    c’est-à-dire 5 · 576 = 2880 = 3 · 960. -/
theorem quadratic_resonance_three_fifths :
    5 * fourierNormSq_scaled chiQuadratic = 3 * totalEnergyNonTrivial_scaled := by
  rw [fourier_quadratic_dominant, total_energy_eq_960]
  norm_num

/-! ## §6. χ_{0,2} comme symbole de Legendre modulo 5 -/

/-- Symbole de Legendre (a/5) comme Int (renvoie 0, 1 ou -1). -/
@[inline] def legendreMod5 (a : Nat) : Int :=
  match a % 5 with
  | 0 => 0
  | 1 => 1
  | 4 => 1
  | _ => -1  -- 2 et 3 sont des non-résidus

/-- χ_{0,2} évalué sur l’unité i ∈ Fin 8 est égal au symbole de Legendre de unitValue i modulo 5. -/
theorem chi_quadratic_eq_legendre_mod5 :
    ∀ i : Fin 8, evalChar chiQuadratic i = (legendreMod5 (unitValue i), 0) := by decide

/-! ## §7. Complément A.4' — orbite quadratique complète A₄ = {1, 11, 19, 29} -/

/-- Prédicat d’appartenance à A₄ = QR mod 5 ∩ G₃₀. -/
@[inline] def memA4 (i : Fin 8) : Bool :=
  let v := unitValue i
  v = 1 ∨ v = 11 ∨ v = 19 ∨ v = 29

/-- Transformée de Fourier de 𝟙_{A₄}. -/
def fourierA4 (χ : QuadCharIdx) : CouretUnification.Core.Classification63.GI :=
  (List.finRange 8).foldl
    (fun acc i => if memA4 i then gi_add acc (evalChar χ i) else acc)
    gi_zero

/-- Transformée de Fourier centrée de A₄, mise à l’échelle par 8 :
    8·k̂_{A₄}(χ) = 8·𝟙̂_{A₄}(χ) - 4·8·δ_{χ trivial}.
    (Comme |A₄| = 4, la constante à soustraire est 4/8 → 4·8 = 32 après mise à l’échelle par 8.) -/
def fourierCenteredA4 (χ : QuadCharIdx) : CouretUnification.Core.Classification63.GI :=
  let raw := fourierA4 χ
  let raw8 : CouretUnification.Core.Classification63.GI := (8 * raw.1, 8 * raw.2)
  if χ = chiTrivial then gi_sub raw8 (32, 0) else raw8

/-- **THÉORÈME A.4' (orbite quadratique complète).** Tous les coefficients de Fourier
    non triviaux de k_{A₄} s’annulent sauf sur χ_{0,2}, où la valeur est exactement 4
    (donc |·|² = 16).
    Mise à l’échelle par 8 : la valeur est 32, |·|² = 1024. -/
theorem A4_pure_quadratic :
    fourierCenteredA4 chiQuadratic = (32, 0) ∧
    ∀ χ : QuadCharIdx, χ ≠ chiTrivial → χ ≠ chiQuadratic →
      fourierCenteredA4 χ = (0, 0) := by
  refine ⟨by native_decide, ?_⟩
  decide

/-- **CONSÉQUENCE STRUCTURELLE.** Sur G₃₀, l’indicatrice centrée de A₄ est exactement
    égale à la moitié du caractère quadratique modulo 5 :

      (8·k_{A₄})(i) = 4 · legendreMod5 (unitValue i)   pour tout i ∈ Fin 8.

    c’est-à-dire k_{A₄}(x) = (1/2) · (x/5).
-/
def kA4_scaled (i : Fin 8) : Int :=
  if memA4 i then 8 - 4 else 0 - 4  -- 8·𝟙_{A₄} - 4

theorem kA4_eq_four_times_legendre :
    ∀ i : Fin 8, kA4_scaled i = 4 * legendreMod5 (unitValue i) := by decide

/-! ## §8. Ancre de synthèse -/

/-- Ancre doctrinale : vérification machine de A.4 et A.4'.

    Selon la convention utilisée à la fin de `AlgebraTC.lean`
    (RHClaimed_false_AlgebraTC True trivial), ce théorème sert de
    marqueur topologique plutôt que de théorème de contenu. Sa présence dans le
    module compilé atteste que tous les théorèmes ci-dessus ont été vérifiés par
    la machine et que le fichier compile dans le périmètre doctrinal gelé.

    Mise à jour du registre : A.4 passe de [P→D] à [D] après succès du
    `lake build` de ce module.

    Invariants préservés : RHClaimed = false. ScopeExpansionClaimed = false.
-/
theorem AFourStatus_machine_verified : True := trivial

end CouretUnification.Core.QuadraticResonance
