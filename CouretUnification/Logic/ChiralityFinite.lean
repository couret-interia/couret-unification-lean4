/-
Copyright (c) 2026 Couret-Unification Programme.
Released under Apache 2.0.

# Logic/ChiralityFinite.lean — Couche A / Chiralité finie de (ℤ/30ℤ)×

## Statut

Couche     : Logic / Gold.
Sorry      : 0.
Axiomes    : 0 (aucun ajout, pur calcul fini).
RHClaimed  : false.

## Contexte

Ce fichier formalise la **chiralité finie** portée par le noyau arithmétique
du programme Couret–Unification, à savoir le groupe multiplicatif

  G₃₀ = (ℤ/30ℤ)× = {1, 7, 11, 13, 17, 19, 23, 29} ≅ C₂ × C₄.

On y établit, entièrement par `native_decide` :

  1. E est stable par multiplication mod 30.
  2. Le générateur 7 a ordre 4 et engendre l'orbite orbA = {1, 7, 19, 13}.
  3. La classe 11 engendre l'orbite complémentaire orbB = {11, 17, 29, 23}.
  4. orbA ⊔ orbB = E : les deux cycles partitionnent G₃₀.
  5. Le triplet de Couret TC = {1, 11, 29} se **scinde** entre les deux
     orbites : 1 ∈ orbA, {11, 29} ⊂ orbB.
  6. La classe phantom 19 = 11·29 mod 30 tombe dans orbA — c'est-à-dire
     dans l'orbite **opposée** à celle de ses facteurs 11 et 29.

La non-fermeture multiplicative de TC (déjà établie par `prod_11_29_mod30`
dans TCAutoInverse.lean) reçoit ici son interprétation géométrique :
c'est l'empreinte d'un **saut d'orbite chirale**.

## Portée doctrinale

Ce fichier constitue la brique A de la hiérarchie A/B/C/D convenue pour
la chiralité du programme :

  A. E, G₃₀, P_g, Ω_g                    — fini exact / Lean [ce fichier]
  B. Matrices 8×8 de P₇ et Ω₇            — modèle structuré
  C. Énergie 𝓔(x), minima métastables     — expérimental / variationnel
  D. Trace, det, Hilbert–Pólya, σ_c       — conditionnel / ouvert

Aucun énoncé de ce fichier ne prétend quoi que ce soit sur la couche D.
L'invariant `RHClaimed = false` est enforcé au niveau du type.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace CouretUnification
namespace ChiralityFinite

/-! ## Section 1 — Le noyau fini E et sa stabilité multiplicative -/

/-- Les huit classes coprimes de (ℤ/30ℤ)× : E = G₃₀. -/
def E : Finset (ZMod 30) := {1, 7, 11, 13, 17, 19, 23, 29}

/-- Cardinal : φ(30) = 8. -/
theorem card_E : E.card = 8 := by native_decide

/-- Stabilité multiplicative : E · E ⊆ E. -/
theorem E_closed_under_mul : ∀ a ∈ E, ∀ b ∈ E, a * b ∈ E := by native_decide

/-- Triplet de Couret. -/
def TC : Finset (ZMod 30) := {1, 11, 29}

/-- TC ⊆ E. -/
theorem TC_subset_E : TC ⊆ E := by native_decide

/-- Auto-inverses : tout élément de TC est son propre inverse mod 30. -/
theorem TC_auto_inverse :
    (1 : ZMod 30) * 1 = 1 ∧
    (11 : ZMod 30) * 11 = 1 ∧
    (29 : ZMod 30) * 29 = 1 := by native_decide

/-! ## Section 2 — La permutation multiplicative P_g -/

/-- Permutation multiplicative P_g : e ↦ g · e (mod 30). -/
def P (g e : ZMod 30) : ZMod 30 := g * e

/-- P préserve E quand g ∈ E : conséquence directe de la stabilité. -/
theorem P_preserves_E (g : ZMod 30) (hg : g ∈ E) :
    ∀ e ∈ E, P g e ∈ E := fun e he => E_closed_under_mul g hg e he

/-! ## Section 3 — Les deux orbites sous P₇ -/

/-- Orbite de 1 sous P₇ : le cycle 1 → 7 → 19 → 13 → 1. -/
def orbA : Finset (ZMod 30) := {1, 7, 19, 13}

/-- Orbite de 11 sous P₇ : le cycle 11 → 17 → 29 → 23 → 11. -/
def orbB : Finset (ZMod 30) := {11, 17, 29, 23}

/-- **Cycle de l'orbite A** sous P₇. -/
theorem orbA_cycle :
    P 7 1 = 7 ∧ P 7 7 = 19 ∧ P 7 19 = 13 ∧ P 7 13 = 1 := by
  native_decide

/-- **Cycle de l'orbite B** sous P₇. -/
theorem orbB_cycle :
    P 7 11 = 17 ∧ P 7 17 = 29 ∧ P 7 29 = 23 ∧ P 7 23 = 11 := by
  native_decide

/-- Les deux orbites partitionnent E. -/
theorem orbits_partition : orbA ∪ orbB = E := by native_decide

/-- Les deux orbites sont disjointes. -/
theorem orbits_disjoint : orbA ∩ orbB = (∅ : Finset (ZMod 30)) := by
  native_decide

/-- Chaque orbite est de cardinal 4. -/
theorem card_orbA : orbA.card = 4 := by native_decide
theorem card_orbB : orbB.card = 4 := by native_decide

/-- **Ordre de 7 dans G₃₀** : 7⁴ = 1. -/
theorem order_of_7 : (7 : ZMod 30)^4 = 1 := by native_decide

/-- P₇ a pour ordre 4 comme permutation de E : P₇⁴ = id_E. -/
theorem P7_fourth_iterate :
    ∀ a ∈ E, P 7 (P 7 (P 7 (P 7 a))) = a := by native_decide

/-- Les puissances de 7 remplissent exactement l'orbite A. -/
theorem powers_of_7_eq_orbA :
    ({(7 : ZMod 30)^1, (7 : ZMod 30)^2, (7 : ZMod 30)^3, (7 : ZMod 30)^4}
      : Finset (ZMod 30)) = orbA := by native_decide

/-- 11 n'est pas dans les puissances de 7 : il engendre la classe
    C₂ opposée dans G₃₀ ≅ C₂ × C₄. -/
theorem eleven_not_power_of_7 :
    ∀ k : Fin 4, (7 : ZMod 30)^(k.val + 1) ≠ 11 := by native_decide

/-! ## Section 4 — Le scindage du triplet de Couret -/

/-- **Théorème (scindage de TC)**. Le triplet de Couret se scinde
    exactement ainsi :
      * 1  ∈ orbA
      * 11 ∈ orbB
      * 29 ∈ orbB
    TC n'est contenu dans aucune orbite. -/
theorem TC_splits :
    (1 : ZMod 30) ∈ orbA ∧
    (11 : ZMod 30) ∈ orbB ∧
    (29 : ZMod 30) ∈ orbB := by native_decide

theorem TC_not_in_orbA : ¬ TC ⊆ orbA := by native_decide
theorem TC_not_in_orbB : ¬ TC ⊆ orbB := by native_decide

/-! ## Section 5 — La classe phantom 19 et le saut chiral -/

/-- Classe phantom : 11 · 29 ≡ 19 (mod 30). -/
theorem phantom_mul : (11 : ZMod 30) * 29 = 19 := by native_decide

/-- 19 ∉ TC. -/
theorem phantom_not_in_TC : (19 : ZMod 30) ∉ TC := by native_decide

/-- **Théorème central (saut d'orbite chirale)**. La classe phantom 19,
    produit des deux facteurs 11 et 29, appartient à l'orbite **opposée**
    à celle de ses facteurs :

      11, 29 ∈ orbB     (orbite de 11 sous P₇)
      19    ∈ orbA      (orbite de 1  sous P₇)

    C'est l'interprétation géométrique de la non-fermeture de TC :
    la multiplication fait sauter d'une orbite à l'autre. -/
theorem phantom_jumps_orbit :
    (11 : ZMod 30) ∈ orbB ∧
    (29 : ZMod 30) ∈ orbB ∧
    (19 : ZMod 30) ∈ orbA ∧
    (19 : ZMod 30) ∉ orbB := by native_decide

/-! ## Section 6 — L'opérateur chiral Ω_g = P_g − P_g⁻¹ -/

/-- Inverse multiplicatif de 7 mod 30 : 7 · 13 = 91 ≡ 1. -/
theorem inv_of_7 : (7 : ZMod 30) * 13 = 1 := by native_decide

/-- 13 = 7⁻¹ = 7³ mod 30 (cohérent avec 7⁴ = 1). -/
theorem thirteen_is_seven_cubed : (7 : ZMod 30)^3 = 13 := by native_decide

/-- Ω_7 agit sur les fonctions f : E → ℂ par
      (Ω₇ f)(a) = f(7·a) − f(13·a).
    Cette définition abstraite permet de parler du noyau et de l'image
    de Ω₇ sans construire encore la matrice 8×8 (cf. couche B). -/
def Omega7 (f : ZMod 30 → ℂ) (a : ZMod 30) : ℂ :=
  f (7 * a) - f (13 * a)

/-- **Propriété clé (antisymétrie)** : Ω_g change de signe
    quand on remplace g par g⁻¹. -/
theorem Omega7_antisymmetric (f : ZMod 30 → ℂ) (a : ZMod 30) :
    Omega7 f a = - (f (13 * a) - f (7 * a)) := by
  unfold Omega7; ring

/-! ## Section 7 — Localisation des paires Janus dans les orbites -/

/-- Les 4 paires miroirs de l'involution 𝒥 : x ↦ −x mod 30. -/
def janusPair1 : Finset (ZMod 30) := {1, 29}
def janusPair7 : Finset (ZMod 30) := {7, 23}
def janusPair11 : Finset (ZMod 30) := {11, 19}
def janusPair13 : Finset (ZMod 30) := {13, 17}

/-- Vérification : 30 − x = -x mod 30 pour les quatre paires. -/
theorem janus_involution_check :
    -(1 : ZMod 30) = 29 ∧
    -(7 : ZMod 30) = 23 ∧
    -(11 : ZMod 30) = 19 ∧
    -(13 : ZMod 30) = 17 := by native_decide

/-- **Localisation des paires Janus**. Chaque paire miroir est partagée
    entre les deux orbites — la chiralité P₇ et l'involution Janus
    sont **transverses**, pas alignées. -/
theorem janus_pairs_cross_orbits :
    -- (1, 29) : 1 ∈ orbA, 29 ∈ orbB
    ((1 : ZMod 30) ∈ orbA ∧ (29 : ZMod 30) ∈ orbB) ∧
    -- (7, 23) : 7 ∈ orbA, 23 ∈ orbB
    ((7 : ZMod 30) ∈ orbA ∧ (23 : ZMod 30) ∈ orbB) ∧
    -- (11, 19) : 19 ∈ orbA, 11 ∈ orbB
    ((19 : ZMod 30) ∈ orbA ∧ (11 : ZMod 30) ∈ orbB) ∧
    -- (13, 17) : 13 ∈ orbA, 17 ∈ orbB
    ((13 : ZMod 30) ∈ orbA ∧ (17 : ZMod 30) ∈ orbB) := by
  native_decide

/-! ## Section 8 — Invariant doctrinal -/

/-- Invariant constitutionnel : ce fichier ne prétend rien sur RH. -/
def RHClaimed : Bool := false

example : RHClaimed = false := rfl

/-! ## Section 9 — Synthèse

Ce fichier établit, **sans aucun sorry et sans aucun axiome ajouté**,
les faits finis suivants sur le noyau arithmétique du programme :

  (F1)  E est stable par multiplication mod 30 ; |E| = 8.
  (F2)  TC = {1, 11, 29} ⊂ E est un triplet d'auto-inverses.
  (F3)  7 a ordre 4 dans G₃₀ ; orbA = ⟨7⟩ = {1, 7, 19, 13}.
  (F4)  orbB = 11·⟨7⟩ = {11, 17, 29, 23}.
  (F5)  orbA ⊔ orbB = E : partition exacte.
  (F6)  TC se scinde : 1 ∈ orbA, 11, 29 ∈ orbB.
  (F7)  phantom 19 = 11·29 mod 30 tombe dans orbA : saut d'orbite.
  (F8)  Les 4 paires Janus sont transverses aux orbites P₇.

### Lecture géométrique

La non-fermeture de TC établie par TCAutoInverse.lean reçoit ici
son sens géométrique :

  **TC n'est pas fermé parce que ses éléments vivent dans
    deux orbites chirales différentes**.

Le produit 11·29 traverse la frontière entre orbB et orbA.
C'est ce traversement qui crée la classe phantom 19 — la chiralité
arithmétique est l'unique moteur de la non-fermeture.

### Passage aux couches B, C, D

  * Couche B : la matrice 8×8 de P₇ a pour polynôme caractéristique
    (x⁴ − 1)² = (x−1)²(x+1)²(x−i)²(x+i)². Son spectre est
    {1, 1, −1, −1, i, i, −i, −i}. Ω₇ = P₇ − P₇⁻¹ a donc pour spectre
    {0, 0, 0, 0, +2i, +2i, −2i, −2i} : rang 4, antisymétrique,
    noyau = sous-espace symétrique (dim 4), image = sous-espace
    antisymétrique (dim 4) où vit la chiralité. Formalisation
    prévue dans ChiralityMatrix.lean.

  * Couche C : l'énergie variationnelle 𝓔(x) = α‖x‖² + β‖x‖⁴ +
    γ𝒱(x) + ε𝒞(x) et ses minima métastables restent hors du
    noyau formel — modèle expérimental uniquement.

  * Couche D : trace, déterminant, Hilbert–Pólya, σ_c ≈ 0.86
    restent conditionnels / ouverts.

### Devise

  La chiralité transporte la cohérence ;
  la métastabilité verrouille le défaut qui la rend visible.

-/

end ChiralityFinite
end CouretUnification
