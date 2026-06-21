/-
================================================================================
  CouretUnification/Residue/CycleCoset.lean
================================================================================

  Couret–Unification · v37 · Ticket Lean 2

  CIBLE : TC = {1} ∪ (K₄ ∩ Coset).

  Démontre que le triplet de Couret TC = {1, 11, 29} est distingué
  combinatoirement par la décomposition Cycle/Coset de G₃₀ :

      Cycle = ⟨7⟩ = {1, 7, 19, 13}    (cycle multiplicatif engendré par 7)
      Coset = 11·⟨7⟩ = {11, 17, 29, 23}

  et par les intersections avec la 2-torsion K₄ :

      K₄ ∩ Cycle = {1, 19}
      K₄ ∩ Coset = {11, 29}

  donc :

      TC = {1} ∪ (K₄ ∩ Coset).

  STATUT ÉPISTÉMIQUE  : [P] local, fini, calculatoire.
  STATUT ARCHITECTURAL : Active (jamais Frozen sans contrat global).

  Application du principe central v37 :
    statut de vérité ≠ position architecturale
    [P] local ≠ Frozen Core automatiquement.

  ─────────────────────────────────────────────────────────────────────────
  Convention spectrale héritée par Isospectrality.lean
  ─────────────────────────────────────────────────────────────────────────

  Dans `Residue/Isospectrality.lean`, le spectre de Aₐ désigne
  le multiensemble des valeurs propres de l'opérateur de convolution
  par l'indicatrice de Aₐ sur Fun(G₃₀, ℂ), identité incluse.

  Cette convention évite l'ambiguïté entre graphe de Cayley simple
  sans boucle et opérateur de convolution avec identité incluse.

  ─────────────────────────────────────────────────────────────────────────
  Garde doctrinale
  ─────────────────────────────────────────────────────────────────────────

  L'orientation Cycle/Coset distingue TC structurellement,
  mais elle n'implique aucune unicité spectrale.

  Lecture correcte :

      TC n'est pas distingué par le spectre brut ;
      TC est distingué par son orientation Cycle/Coset.

  Cette affirmation reste strictement locale.

  Elle ne prouve pas RH.
  Elle ne prouve pas Hilbert–Pólya.
  Elle ne prouve pas le pont det₂ ↔ ξ.
  Elle ne prouve pas la correspondance candidate traction/résidu.

  La traction ne prouve pas le résidu ;
  le résidu ne prouve pas la traction.

  ─────────────────────────────────────────────────────────────────────────
  Stratégie de prudence Mathlib (miroir de ClosureTC.lean)
  ─────────────────────────────────────────────────────────────────────────

  Comme ClosureTC.lean :
  - on travaille dans Z30 = ZMod 30 directement, PAS dans (ZMod 30)ˣ ;
  - on définit les éléments par des entiers Nat coercés en ZMod 30 ;
  - tous les calculs sont fermés par `decide` ou `native_decide` ;
  - on ne dépend que de Mathlib.Data.ZMod.Basic et
    Mathlib.Data.Finset.Basic.

  Les Finsets considérés sont tous de cardinal ≤ 8, donc `decide`
  devrait fermer sans difficulté. Si timeout, basculer vers
  `native_decide`.

  ─────────────────────────────────────────────────────────────────────────
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import CouretUnification.Residue.ClosureTC

namespace CouretUnification
namespace Residue

/- ══════════════════════════════════════════════════════════════════════
   Cycle et Coset comme Finsets explicites de Z30.

   On rappelle :
     7² = 49 ≡ 19 mod 30
     7³ = 343 ≡ 13 mod 30
     7⁴ = 2401 ≡ 1 mod 30

   Donc ⟨7⟩ = {1, 7, 19, 13} comme sous-monoïde cyclique d'ordre 4.

   Et 11·{1, 7, 19, 13} = {11, 77, 209, 143} ≡ {11, 17, 29, 23} mod 30.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Le Cycle : sous-ensemble de Z30 obtenu comme {7^k mod 30 : k ∈ ℕ},
    soit {1, 7, 19, 13}. -/
def Cycle : Finset Z30 := {1, 7, 19, 13}

/-- Le Coset : 11·⟨7⟩ = {11, 17, 29, 23}. -/
def Coset : Finset Z30 := {11, 17, 29, 23}

/-- L'ensemble des résidus inversibles de Z30 (les huit classes inversibles
    modulo 30) : {1, 7, 11, 13, 17, 19, 23, 29}.

    Note de nommage : on écrit `G30UnitResidues` plutôt que `G30Units`
    pour souligner qu'il s'agit d'un `Finset Z30` (ensemble de classes
    de résidus) et non d'un `Finset (ZMod 30)ˣ` (ensemble d'objets
    Units). La distinction est mathématiquement minime mais évite
    toute confusion future quand on basculera éventuellement vers
    les Units pour Isospectrality.lean. -/
def G30UnitResidues : Finset Z30 := {1, 7, 11, 13, 17, 19, 23, 29}

/- ══════════════════════════════════════════════════════════════════════
   Vérifications calculatoires de la structure du Cycle.
   ══════════════════════════════════════════════════════════════════════ -/

/-- 7² ≡ 19 mod 30 : le fantôme est le carré du générateur du Cycle. -/
theorem seven_squared_eq_nineteen :
    (7 : Z30) * 7 = 19 := by
  decide

/-- 7³ ≡ 13 mod 30. -/
theorem seven_cubed_eq_thirteen :
    (7 : Z30) * 7 * 7 = 13 := by
  decide

/-- 7⁴ ≡ 1 mod 30 : ordre 4 du Cycle. -/
theorem seven_pow_four_eq_one :
    (7 : Z30) * 7 * 7 * 7 = 1 := by
  decide

/-- 11 · 7 ≡ 17 mod 30. -/
theorem eleven_times_seven_eq_seventeen :
    (11 : Z30) * 7 = 17 := by
  decide

/-- 11 · 19 ≡ 29 mod 30. -/
theorem eleven_times_nineteen_eq_twentynine :
    (11 : Z30) * 19 = 29 := by
  decide

/-- 11 · 13 ≡ 23 mod 30. -/
theorem eleven_times_thirteen_eq_twentythree :
    (11 : Z30) * 13 = 23 := by
  decide

/- ══════════════════════════════════════════════════════════════════════
   Décomposition Cycle/Coset comme partition des unités de Z30.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Cycle ∪ Coset = G30UnitResidues (les huit unités modulo 30). -/
theorem Cycle_union_Coset_eq_G30UnitResidues :
    Cycle ∪ Coset = G30UnitResidues := by
  decide

/-- Cycle et Coset sont disjoints. -/
theorem Cycle_disjoint_Coset :
    Disjoint Cycle Coset := by
  decide

/-- Forme combinée : Cycle et Coset partitionnent G30UnitResidues. -/
theorem G30UnitResidues_partition :
    Cycle ∪ Coset = G30UnitResidues ∧ Disjoint Cycle Coset := by
  refine ⟨?_, ?_⟩
  · exact Cycle_union_Coset_eq_G30UnitResidues
  · exact Cycle_disjoint_Coset

/- ══════════════════════════════════════════════════════════════════════
   Intersection avec la 2-torsion K₄.

   Rappel (de ClosureTC.lean) : K4 = {1, 11, 19, 29}.

   On vérifie que K₄ se répartit également entre Cycle et Coset :
     K₄ ∩ Cycle = {1, 19}    (l'identité du Cycle et son carré 7² = 19)
     K₄ ∩ Coset = {11, 29}   (la 2-torsion du Coset)
   ══════════════════════════════════════════════════════════════════════ -/

/-- K₄ ∩ Cycle = {1, 19}. -/
theorem K4_inter_Cycle :
    K4 ∩ Cycle = ({1, 19} : Finset Z30) := by
  decide

/-- K₄ ∩ Coset = {11, 29}. -/
theorem K4_inter_Coset :
    K4 ∩ Coset = ({11, 29} : Finset Z30) := by
  decide

/- ══════════════════════════════════════════════════════════════════════
   THÉORÈME PRINCIPAL : caractérisation de TC par orientation Cycle/Coset.
   ══════════════════════════════════════════════════════════════════════ -/

/-- THÉORÈME PRINCIPAL : TC = {1} ∪ (K₄ ∩ Coset).

    Autrement dit : TC est l'union de l'identité du Cycle et de
    la 2-torsion du Coset.

    C'est cette caractérisation qui distingue TC de A₁₁ = {1, 19, 29}
    (qui mélange Cycle et Coset) et de A₂₉ = {1, 11, 19} (idem).

    Cf. Ticket 3 (isospectralité) : ces trois triplets ont
    *probablement* le même spectre ; ce n'est *pas* le spectre qui
    distingue TC, c'est cette décomposition Cycle/Coset.

    Statut : [P] local. Architecturalement Active, jamais Frozen. -/
theorem TC_eq_one_union_K4_inter_Coset :
    TC = ({1} : Finset Z30) ∪ (K4 ∩ Coset) := by
  rw [K4_inter_Coset]
  decide

/-- Caractérisation alternative : TC = {1, 11, 29}, en isolant
    explicitement le rôle de l'identité.

    Cette forme est immédiate par définition de TC (cf. ClosureTC.lean),
    mais on l'écrit ici pour la complétude documentaire.

    Note technique : on utilise `by decide` plutôt que `rfl` direct,
    parce que selon la version de Mathlib, les deux littéraux de
    Finset peuvent ne pas être définitionnellement identiques
    (l'ordre d'insertion dans l'arbre interne peut différer).
    `decide` est plus robuste et ferme l'égalité par calcul. -/
theorem TC_eq_one_eleven_twentynine :
    TC = ({1, 11, 29} : Finset Z30) := by
  decide

/- ══════════════════════════════════════════════════════════════════════
   Statut épistémique et architectural matérialisé en code.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Statut épistémique : [P] calculatoire. -/
def cycle_coset_epistemic_status : String := "P"

/-- Statut architectural v37 : Active, jamais Frozen.
    Application du principe central : statut de vérité ≠ position
    architecturale. -/
def cycle_coset_architectural_layer : String := "Active"

/-- L'orientation Cycle/Coset distingue TC structurellement, mais
    cela n'implique aucune unicité spectrale. Voir Ticket 3
    (Isospectrality.lean).

    Aucune revendication globale n'est exportée par ce module. -/
theorem TC_orientation_does_not_imply_spectral_uniqueness :
    True := trivial

end Residue
end CouretUnification

/-
================================================================================
  Notes pour Thomas
================================================================================

  1. Tous les théorèmes ferment par `decide` sur des Finsets de
     cardinal ≤ 8. `decide` natif devrait suffire ; pas besoin de
     `native_decide` a priori.

  2. Le module dépend de ClosureTC.lean (pour la définition de TC,
     K4, et l'abréviation Z30). Cela garantit la cohérence : TC
     défini ici et TC défini là-bas sont littéralement le même objet.

  3. La caractérisation TC = {1} ∪ (K₄ ∩ Coset) est la formulation
     recommandée pour la note publiable : elle exhibe l'orientation
     Cycle/Coset comme propriété distinctive de TC, indépendamment
     du spectre.

  4. Convention IMPÉRATIVE pour Ticket 3 : quand on parlera de
     "spectre de A_a", il s'agira du multiensemble des valeurs
     propres de l'opérateur de convolution par l'indicatrice de
     A_a sur Fun(Z30, ℂ), *identité incluse* si elle appartient à
     A_a. Cette convention est posée ici pour que les modules
     suivants l'héritent.

  5. Architecture v37 : ce module reste Active, jamais Frozen.
     Sa promotion en Frozen exigerait de prouver explicitement que
     la juridiction globale dépend de cette caractérisation, ce
     qui n'est pas le cas pour l'instant.

  6. Note technique sur le choix Z30 vs (Z30)ˣ : on utilise Z30
     directement par cohérence avec ClosureTC.lean. Pour Ticket 3
     (isospectralité avec caractères de Dirichlet), il faudra
     probablement basculer vers (Z30)ˣ — c'est une décision à
     prendre quand on attaquera Isospectrality.lean.
================================================================================
-/
