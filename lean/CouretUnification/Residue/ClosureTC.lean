/-!
================================================================================
  CouretUnification/Residue/ClosureTC.lean
================================================================================

  Couret–Unification · v37 · Ticket Lean 1

  CIBLE : closure_residue_TC : ρ(TC) = {19} comme [P] calculatoire.

  STATUT ÉPISTÉMIQUE  : [P] local, fini, calculatoire.
  STATUT ARCHITECTURAL : Active (jamais Frozen sans contrat global).

  Application du principe central v37 :
    statut de vérité ≠ position architecturale
    [P] local ≠ Frozen Core automatiquement.

  ─────────────────────────────────────────────────────────────────────────
  Stratégie de prudence Mathlib
  ─────────────────────────────────────────────────────────────────────────

  Cette version est volontairement écrite pour maximiser la robustesse
  aux variations entre versions de Mathlib. Décisions techniques :

  1. On utilise (ZMod 30) directement, PAS (ZMod 30)ˣ.
     Raison : la coercion vers Units demande une preuve de coprimalité
     dont la syntaxe varie entre versions Mathlib. Travailler dans
     ZMod 30 directement évite ce problème, au prix d'une légère
     perte de structure (on n'a pas le groupe Units, mais on a le
     monoïde multiplicatif, ce qui suffit ici).

  2. On définit les éléments par des entiers Nat coercés en ZMod 30.
     Tous les calculs sont fermés par `decide` ou `native_decide`.

  3. On définit la clôture multiplicative comme itération bornée
     d'un step de fermeture par produit. La borne 16 est un sûr-
     majorant pour |ZMod 30| × 2.

  4. On ne dépend que de Mathlib.Data.ZMod.Basic et
     Mathlib.Data.Finset.Basic, qui sont stables depuis longtemps.

  Pour Thomas : si `decide` est trop lent sur `closure_TC_eq_K4`,
  remplacer par `native_decide`.

  ─────────────────────────────────────────────────────────────────────────
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

namespace CouretUnification
namespace Residue

/-- L'anneau Z/30Z. Toute la mathématique du module se passe dedans. -/
abbrev Z30 := ZMod 30

/-- Le triplet de Couret TC = {1, 11, 29} comme Finset Z30. -/
def TC : Finset Z30 := {1, 11, 29}

/-- La 2-torsion K₄ = {1, 11, 19, 29}. C'est l'ensemble des éléments
    inversibles auto-inverses de Z30 (ou de manière équivalente,
    les solutions de x² = 1 parmi les unités). -/
def K4 : Finset Z30 := {1, 11, 19, 29}

/- ══════════════════════════════════════════════════════════════════════
   Vérifications calculatoires de base.

   Ces théorèmes établissent les faits arithmétiques fondamentaux
   sur lesquels repose tout le reste.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Vérification : 11 · 29 = 19 dans Z30. C'est le « fantôme ». -/
theorem eleven_times_twentynine_eq_nineteen :
    (11 : Z30) * 29 = 19 := by
  decide

/-- Vérification : 11² = 1 dans Z30. -/
theorem eleven_squared_eq_one :
    (11 : Z30) * 11 = 1 := by
  decide

/-- Vérification : 19² = 1 dans Z30. -/
theorem nineteen_squared_eq_one :
    (19 : Z30) * 19 = 1 := by
  decide

/-- Vérification : 29² = 1 dans Z30. -/
theorem twentynine_squared_eq_one :
    (29 : Z30) * 29 = 1 := by
  decide

/-- Vérification : 19 ∉ TC (le fantôme n'est pas dans le triplet). -/
theorem nineteen_not_in_TC :
    (19 : Z30) ∉ TC := by
  decide

/-- Vérification : 19 ∈ K₄ (le fantôme est dans la 2-torsion). -/
theorem nineteen_in_K4 :
    (19 : Z30) ∈ K4 := by
  decide

/-- Vérification : TC ⊆ K₄. -/
theorem TC_subset_K4 : TC ⊆ K4 := by
  decide

/- ══════════════════════════════════════════════════════════════════════
   Clôture multiplicative locale.

   Pour TC dont les éléments sont auto-inverses (cf. theorems above),
   il suffit de fermer par produit. La borne d'itération 16 est un
   sûr-majorant.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Un pas de fermeture par produit : on ajoute tous les produits
    a · b avec a, b ∈ S. -/
def stepClosure (S : Finset Z30) : Finset Z30 :=
  S ∪ (S ×ˢ S).image (fun p => p.1 * p.2)

/-- Itération d'un nombre fixe d'étapes. -/
def closureN (n : Nat) (S : Finset Z30) : Finset Z30 :=
  Nat.rec S (fun _ acc => stepClosure acc) n

/-- Clôture multiplicative locale (16 itérations, sûr-majorant). -/
def closure30 (S : Finset Z30) : Finset Z30 :=
  closureN 16 S

/-- Résidu de clôture : ρ(S) = closure30(S) \ S. -/
def closureResidue (S : Finset Z30) : Finset Z30 :=
  closure30 S \ S

/- ══════════════════════════════════════════════════════════════════════
   THÉORÈMES PRINCIPAUX.

   Si `decide` ne ferme pas (timeout), remplacer par `native_decide`.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Lemme B.1 : la clôture multiplicative de TC est K₄. -/
theorem closure_TC_eq_K4 :
    closure30 TC = K4 := by
  decide

/-- Lemme B.2 : K₄ \ TC = {19}. -/
theorem K4_minus_TC :
    K4 \ TC = ({19} : Finset Z30) := by
  decide

/-- THÉORÈME PRINCIPAL : ρ(TC) = {19}.

    C'est la matérialisation Lean du fantôme fini de Couret :
    le résidu de clôture du triplet TC = {1, 11, 29} est
    exactement {19}, élément produit par 11 · 29 = 19 mod 30
    et qui n'appartient pas à TC.

    Statut : [P] local, fini, calculatoire.
    Couche : Active (jamais Frozen sans contrat global). -/
theorem closure_residue_TC :
    closureResidue TC = ({19} : Finset Z30) := by
  unfold closureResidue
  rw [closure_TC_eq_K4]
  exact K4_minus_TC

/- ══════════════════════════════════════════════════════════════════════
   Statut épistémique et architectural matérialisé en code.
   ══════════════════════════════════════════════════════════════════════ -/

/-- Statut épistémique : [P] calculatoire. -/
def closure_tc_epistemic_status : String := "P"

/-- Statut architectural v37 : Active, jamais Frozen.
    Application du principe central : statut de vérité ≠ position
    architecturale. -/
def closure_tc_architectural_layer : String := "Active"

/-- Aucune revendication globale n'est exportée par ce module.
    RHClaimed reste false. -/
theorem no_RH_from_closure_residue : True := trivial

end Residue
end CouretUnification

/-
================================================================================
  Notes pour Thomas
================================================================================

  1. Si `closure_TC_eq_K4` ne ferme pas par `decide` (timeout), remplacer
     par `native_decide`. Acceptable dans Mathlib pour vérifications
     combinatoires sur petits ensembles.

  2. Le module utilise Z30 = ZMod 30 directement, PAS (ZMod 30)ˣ.
     C'est un choix de prudence : Z30 a une multiplication calculable
     stable depuis longtemps. Si l'on veut plus tard travailler avec
     les Units (pour formaliser la structure de groupe), on créera
     un module compagnon.

  3. La borne 16 dans `closure30` est un sûr-majorant. Pour TC
     spécifiquement, un seul pas (`stepClosure TC`) suffirait à
     atteindre K₄, parce que :
       1·1=1, 1·11=11, 1·29=29, 11·11=1, 11·29=19, 29·29=1
     donc stepClosure TC = TC ∪ {19} = K₄.
     Et stepClosure K₄ = K₄ (K₄ est un sous-groupe).

  4. Aucune dépendance vers (ZMod 30)ˣ, ZMod.unitOfCoprime, ou
     toute machinerie Units. Le fichier devrait compiler sur
     n'importe quelle version Mathlib supportant ZMod et Finset
     basiques.

  5. Si la compilation échoue, les points d'attention sont :
     - syntaxe de `Finset` literal `{1, 11, 29}` : devrait fonctionner
       depuis longtemps via `Insert` et `Singleton` ;
     - syntaxe `S ×ˢ S` pour le produit cartésien Finset : alternative
       `Finset.product S S` si problème ;
     - `Nat.rec` : syntaxe standard, devrait être stable.
================================================================================
-/
