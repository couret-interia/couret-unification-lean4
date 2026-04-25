/-
# CouretUnification/Meta/Doctrine.lean

## Rôle
Structures épistémiques du programme Couret-Unification.
Encode l'invariant central `RHClaimed = false` au niveau du système de types.

## Statut
- Version : v35.8.6
- Layer   : Meta (non-mathématique, purement structurel)
- Sorry   : 0
-/

namespace CouretUnification
namespace Meta

/-- Couches géologiques du programme.
    - `A` = Noyau fini (FiniteCore) : algèbre certifiée, combinatoire finie.
    - `B` = Logic : verrous asymptotiques et topologiques (zone de travail actuelle).
    - `C` = Asymptotique terminal (H3/L12) : mur RH, classé `rh_wall`. -/
inductive Layer : Type
  | A : Layer
  | B : Layer
  | C : Layer
  deriving Repr, DecidableEq

/-- Statut de fermeture d'un fichier. -/
inductive Status : Type
  /-- Preuves complètement fermées, zéro sorry autorisé. -/
  | proved      : Status
  /-- Conditionnel à un contrat analytique explicite. -/
  | conditional : Status
  /-- Théorème d'obstruction (no-go). -/
  | nogo        : Status
  /-- Chantier amont de définitions effectives. -/
  | definitional : Status
  deriving Repr, DecidableEq

/-- Identité doctrinale d'un fichier.

    L'invariant `rhClaimed = false` est vérifié à la compilation par
    `no_file_claims_RH` (dans `Logic/OpenLocks.lean`). -/
structure FileIdentity where
  filename   : String
  layer      : Layer
  status     : Status
  sorryCount : Nat
  /-- Invariant doctrinal central : aucun fichier ne prétend prouver RH. -/
  rhClaimed  : Bool
  deriving Repr

/-- Invariant global : aucun `FileIdentity` du programme ne doit porter
    `rhClaimed = true`. -/
def respectsRHInvariant (f : FileIdentity) : Prop :=
  f.rhClaimed = false

end Meta
end CouretUnification
