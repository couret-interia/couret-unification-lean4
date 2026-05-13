/-
Copyright (c) 2026 Alexandre Couret. Tous droits réservés.
Publié sous la même licence que le projet Couret-Unification.

# CouretUnification.SophieGermain

Ombrelle Sophie Germain pour Couret–Unification v38x.

Cette façade regroupe les modules stables autour du crible de Sophie Germain
modulo 30, du tower lift primoriel, des matrices empiriques SG déjà présentes,
et de l'invariant algébrique fini du SG-shift.

Statuts :
  * Core/SophieGermainHecke        [D]
  * Core/SophieGermainTowerLift    [D]
  * Residue/SGShiftSqrt2           [D] sceau algébrique fini
  * Residue/SGShiftSpectrum        [O] frontière spectrale
  * Empirical/*                    [M]
  * Numerics/*                     [M]

Cette ombrelle ne revendique aucune identité analytique globale.

Invariants préservés :
  * RHClaimed = false
  * HilbertPolyaClaimed = false
  * L7Established = false

Pour le registre doctrinal complet du sous-programme SG, voir :

  docs/registry/SophieGermain.md
-/

import CouretUnification.Core.SophieGermain
import CouretUnification.Core.SophieGermainMod30
import CouretUnification.Core.SophieGermainHecke
import CouretUnification.Core.SophieGermainTowerLift

import CouretUnification.Logic.SophieGermainMatrix

import CouretUnification.Empirical.SophieGermainExpected
import CouretUnification.Empirical.SophieGermainTransitions

import CouretUnification.Numerics.ScanSummary
import CouretUnification.Numerics.UseScanSummary

import CouretUnification.Residue.SGShiftSqrt2

import CouretUnification.Residue.SGShiftSpectrum

namespace CouretUnification
namespace SophieGermainUmbrella

/-!
## Résumé doctrinal

Cette ombrelle rassemble les briques Sophie Germain actuellement intégrées
dans Couret–Unification v38x.

Le noyau démontré `[D]` comprend :

* le SG-shift modulo 30 ;
* le tower lift primoriel avec règle `ℓ - 2` ;
* l'identité cubique rationnelle `M³ = (1/2)M` du bloc SG-shift.

Les couches empiriques et numériques sont importées comme données ou verdicts
encodés `[M]`, non comme preuves analytiques globales.

La frontière `Residue.SGShiftSpectrum` devra rester séparée du noyau `[D]`
tant que l'énoncé spectral complet `λ ∈ {0, ±1/√2}` avec multiplicités
n'est pas formalisé sans `sorry` ni axiome.
-/

/-- Marqueur de présence de l'ombrelle Sophie Germain. -/
def loaded : Bool := true

/-- Statut doctrinal court de l'ombrelle. -/
def status : String :=
  "[D] core SG + [M] empirical/numerics; RHClaimed = false"

end SophieGermainUmbrella
end CouretUnification
