/-
# CouretUnification/Meta/Doctrine.lean

## v38 — Façade pure
Anciennement (≤ v35.8.5), ce fichier dupliquait `Layer`, `Status` et
`FileIdentity` du module `Meta/Layer.lean`. Cette duplication causait
une collision de constructeurs (`Status.ctorElim`) au build.

Désormais ce fichier réexporte `Meta/Layer` et n'ajoute que l'invariant
doctrinal `respectsRHInvariant`. Toute référence à `Meta.Status.nogo` ou
`Meta.Status.definitional` continue de fonctionner — ces constructeurs
ont été migrés dans `Meta/Layer.lean` (v38).

## Statut
- Layer : Meta
- Sorry : 0
- Axiom : 0
-/

import CouretUnification.Meta.Layer

namespace CouretUnification.Meta

/-- Invariant global : aucun `FileIdentity` ne porte `rhClaimed = true`. -/
def respectsRHInvariant (f : FileIdentity) : Prop :=
  f.rhClaimed = false

end CouretUnification.Meta
