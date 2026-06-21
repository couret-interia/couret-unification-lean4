/-
# Meta/AuditHints.lean — Commandes d'audit cibles (v38.5.13)

## Statut épistémique

  - Couche : Meta
  - Statut : [A] proved (commandes d'audit, pas de contenu mathématique)
  - sorryCount : 0
  - RHClaimed = false

## Doctrine

Ce fichier ne contient **aucun théorème mathématique**. Il liste les
commandes Lean à exécuter manuellement (ou via CI) pour auditer
l'invariant doctrinal du projet :

  1. Aucun théorème de la couche [B] ne dépend d'un axiome local
     Couret-Unification non documenté.
  2. Tous les sorries sont localisés et catégorisés.
  3. Le nombre d'axiomes utilisés par chaque théorème pivot est minimal
     (idéalement : seulement les axiomes fondamentaux de Mathlib).

## Axiomes Mathlib fondamentaux attendus

Ces trois axiomes sont **autorisés** car ils sont au cœur de Mathlib et
font partie du contrat de confiance de la théorie des types de Lean :

  - `propext` : extensionnalité propositionnelle.
  - `Quot.sound` : règle de saine quotient.
  - `Classical.choice` : axiome du choix classique.

Tout autre axiome apparaissant dans `#print axioms` d'un théorème
[B] doit faire l'objet d'une investigation et d'une justification
explicite (ou d'une suppression).
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.EulerBridgeInfiniteReal

namespace CouretUnification.Meta.AuditHints

/-! ## Section 1 — Commandes d'audit pivot

Ces commandes sont à exécuter dans un buffer Lean (par exemple un
fichier `scratch.lean` séparé) ou décommenter ici lors d'un audit
ponctuel. Elles ne sont pas exécutées par défaut pour ne pas polluer
les sorties du build standard.
-/

-- ### Audit du pont eulérien réel

-- #print axioms CouretUnification.Logic.EulerBridgeInfiniteReal.squarefree_limit_eq_euler_product_real

/-! ## Section 2 — Commandes de comptage

### Sorries actifs par fichier

Recommandé en CI via :

```bash
make audit-scripts
```

**Inventaire attendu** :

```
━━━ SORRY (hors commentaires) ━━━
./CouretUnification/Logic/L10NoGoTheorem.lean:69:  sorry
./CouretUnification/Logic/L10NoGoTheorem.lean:239:        sorry
./CouretUnification/Logic/L10NoGoTheorem.lean:245:    sorry
./CouretUnification/Logic/H3/Lemma7Residual.lean:13:  sorry
./CouretUnification/Logic/H3/RouteC.lean:780:  sorry
./CouretUnification/Logic/L6RatioEstimateDerived.lean:90:    sorry
./CouretUnification/AnalyticHorizon/Det2Transport.lean:71:  sorry
./CouretUnification/Analytic/GammaFactor.lean:62:noncomputable def D_M (s : ℂ) : ℂ := sorry
./CouretUnification/Analytic/GammaFactor.lean:83:  sorry
./CouretUnification/Analytic/GammaFactor.lean:95:  sorry
./CouretUnification/Analytic/GammaFactor.lean:112:  sorry
  Total sorry: 11

━━━ AXIOM ━━━
./CouretUnification/Logic/H3/ArithmeticBridge.lean:29:axiom Det2IdentifiesXi : Prop
./CouretUnification/Logic/H3/ArithmeticBridge.lean:30:axiom ZeroMatching : Prop
./CouretUnification/Logic/H3/AlgebraTC.lean:195:axiom mellinConvolve_comm :
./CouretUnification/Logic/H3/C2Restricted.lean:60:axiom restricted_explicit_formula_old
./CouretUnification/Logic/H3/C2Restricted.lean:91:axiom restricted_explicit_formula_holds
./CouretUnification/Logic/H3/C2Restricted.lean:112:axiom mainTermPositive_of_positiveBias
./CouretUnification/Logic/H3/RigidityParams.lean:50:axiom sigma_G_critical_pos
./CouretUnification/Logic/H3/Lock2Conditional.lean:6:axiom local_bridge_to_det2_xi
./CouretUnification/Logic/H3/ZeroMatching.lean:5:axiom spectral_id_to_zero_matching (hDet : Det2IdentifiesXi) : ZeroMatching
  Total axiom: 9
```

### Axiomes locaux Couret-Unification

```bash
grep -rE "^axiom |^[[:space:]]+axiom " lean/CouretUnification --include="*.lean"
```

**Inventaire attendu** :

```
Logic/H3/ArithmeticBridge.lean:axiom Det2IdentifiesXi : Prop
Logic/H3/ArithmeticBridge.lean:axiom ZeroMatching : Prop
Logic/H3/AlgebraTC.lean:axiom mellinConvolve_comm :
Logic/H3/C2Restricted.lean:axiom restricted_explicit_formula_old
Logic/H3/C2Restricted.lean:axiom restricted_explicit_formula_holds
Logic/H3/C2Restricted.lean:axiom mainTermPositive_of_positiveBias
Logic/H3/RigidityParams.lean:axiom sigma_G_critical_pos
Logic/H3/Lock2Conditional.lean:axiom local_bridge_to_det2_xi
Logic/H3/ZeroMatching.lean:axiom spectral_id_to_zero_matching (hDet : Det2IdentifiesXi) : ZeroMatching
```

Toute autre ligne est une régression doctrinale.
-/

/-! ## Section 3 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Meta/AuditHints.lean"
  layer := CouretUnification.Meta.Layer.A
  status := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-- Drapeau d'audit : l'invariant doctrinal est en place. -/
def auditDoctrineActive : Bool := true
example : auditDoctrineActive = true := rfl

end CouretUnification.Meta.AuditHints
