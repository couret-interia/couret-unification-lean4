/-
# CouretUnification/Frozen.lean

## Rôle

Umbrella "frozen" : importe UNIQUEMENT les fichiers à 0 sorry, status
`proved` ou `definitional-closed`, qui constituent le socle stable du
dépôt.

## Invariant

**Ce fichier ne doit JAMAIS échouer au build.** Si un nouveau commit
fait échouer `lake build CouretUnification.Frozen`, le merge doit être
rejeté.

## Statut (v35.8.8)

- Meta/Doctrine                       [0 sorry ✅]
- Logic/OpenLocks                     [0 sorry ✅, porte no_rh_wall_lock_proved]
- Logic/EulerBridgeInfiniteCompat     [0 sorry ✅]
- Logic/C3Weak_Gram                   [0 sorry ✅]
- Logic/ChiralityFinite               [0 sorry ✅]
- Logic/ChiralityLinear               [0 sorry ✅]
- Logic/L6Interface                   [0 sorry ✅]
- Logic/L6Bridge                      [0 sorry ✅]
- Logic/H3/LocalFactor                [0 sorry ✅]
- Logic/H3/CriticalLineTransferSpec   [0 sorry ✅, spec-only]

## À ajouter quand ready

- Logic/TimeBridge/Basic              [LTB-0, 0 sorry]
- Logic/TimeBridge/B2Calibration      [LTB-0, 0 sorry]
- Logic/TimeBridge/ModularFlowSpec    [LTB-0, 0 sorry]

## Note doctrinale

**Aucun fichier listé ici ne peut importer un fichier de Active.lean.**
La direction des dépendances va strictement Frozen → Active, jamais
l'inverse. Si un besoin inverse apparaît, il faut d'abord rétrograder
le fichier Frozen concerné.

Layer : Meta (aggregator)
Sorry : 0 (par construction, aucun fichier importé n'en a)
RHClaimed : false (hérité via OpenLocks.no_rh_wall_lock_proved)
-/

-- Fondations épistémiques
import CouretUnification.Meta.Doctrine

-- Registre doctrinal (porte l'invariant RH au type-check)
import CouretUnification.Logic.OpenLocks

-- Briques analytiques fermées
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import CouretUnification.Logic.C3Weak_Gram

-- Chiralité finie mod 30
import CouretUnification.Logic.ChiralityFinite
import CouretUnification.Logic.ChiralityLinear

-- Interface et pont L6 (partie proved)
import CouretUnification.Logic.L6Interface
import CouretUnification.Logic.L6Bridge

-- Front H3 : briques à 0 sorry uniquement
import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.CriticalLineTransferSpec

-- À activer après livraison LTB-0 (TimeBridge)
-- import CouretUnification.Logic.TimeBridge.Basic
-- import CouretUnification.Logic.TimeBridge.B2Calibration
-- import CouretUnification.Logic.TimeBridge.ModularFlowSpec
