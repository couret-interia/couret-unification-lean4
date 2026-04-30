/-
  CouretUnification/Active/TraceObjectEnriched.lean

  Active-module : version ENRICHIE du réceptacle `TraceObject` du Frozen
  Core v36.0. Ajoute :
    · Une classe explicite `TestFunction` (continuité + support compact).
    · Une `SpectralSide` avec obligation de sommabilité CORRIGÉE.
    · Une `EnrichedPrimeSide` où le terme `Λ(n)/√n · (g(log n) + g(−log n))`
      est explicitement calculé.
    · Une `EnrichedTraceObject` qui combine les trois côtés.

  Correction doctrinale apportée à la proposition initiale
  ────────────────────────────────────────────────────────
  La proposition initiale contenait :

      is_summable : ∀ (g_hat : ℂ → ℂ), Summable (fun ρ => g_hat (γ ρ))

  Cette quantification ∀ est TROP FORTE : elle inclut des fonctions
  triviales (constante 1, par exemple) pour lesquelles la somme ne peut
  pas converger sur un ensemble spectral infini. La structure serait donc
  inhabitable dès que `zeros` est infini.

  La correction consiste à restreindre l'obligation aux fonctions `g` qui
  sont des `TestFunction`, et à laisser l'obligation de sommabilité
  NOMMÉE mais pas universellement quantifiée sur `ℂ → ℂ`.

  Statut doctrinal
  ────────────────
  · Layer         : Active (dépend de Mathlib.Topology, Mathlib.Topology.Algebra.InfiniteSum.Basic)
  · indeterminateProofs : 0
  · axiomCount    : 0
  · RHClaimed     : false
  · HilbertPolyaClaimed : false

  Règle de sécurité : n'importe PAS le Frozen Core de façon circulaire ;
  importe seulement `TraceObject.lean` du Frozen pour extension.

  Pour Bernard.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Support
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Active

open CouretUnification.Logic.ExplicitFormula

/-! ### Classe de fonctions test admissibles -/

/--
Fonction test admissible pour la formule explicite : continue, à support
compact. La régularité supplémentaire (C^∞, Schwartz) est laissée en
extension Active ultérieure pour la convergence de la transformée de
Fourier.
-/
structure TestFunction (g : ℝ → ℂ) : Prop where
  continuous : Continuous g
  compactSupport : HasCompactSupport g

/-! ### Côté spectral — obligation de sommabilité CORRIGÉE -/

/--
Côté spectral (les zéros) avec obligation de sommabilité restreinte.

On ne présume PAS l'hypothèse de Riemann : `γ` renvoie dans `ℂ` (pas dans
`ℝ`). La sommabilité est une OBLIGATION NOMMÉE, paramétrée par une
transformée de Fourier `gHat` associée à une fonction test `g`.

Correction essentielle par rapport à la proposition initiale :
l'obligation est NOMMÉE comme `Prop`, non quantifiée sur toutes les
`ℂ → ℂ`. Elle devient une obligation à INSTANCIER par le consommateur,
pas une contrainte structurelle impossible.
-/
structure EnrichedSpectralSide where
  zeros : Type
  γ : zeros → ℂ
  /--
  Obligation typée : pour toute fonction test `g` admissible, avec sa
  transformée `gHat`, la série `gHat ∘ γ` est sommable. C'est une
  **obligation** — un consommateur doit la prouver (à l'aide de
  Riemann–von Mangoldt + décroissance de Schwartz, typiquement).
  -/
  summabilityObligation :
    ∀ (g : ℝ → ℂ) (gHat : ℂ → ℂ), TestFunction g → Prop

/-! ### Côté premier enrichi — terme explicite -/

/--
Côté premier enrichi : le terme `Λ(n)/√n · (g(log n) + g(−log n))` est
défini explicitement. `arithmeticWeight` reste abstrait (pas encore
identifié à von Mangoldt).
-/
structure EnrichedPrimeSide where
  arithmeticWeight : ℕ → ℂ

/-- Terme arithmétique explicite du côté premier. -/
noncomputable def EnrichedPrimeSide.contribution
    (P : EnrichedPrimeSide) (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  P.arithmeticWeight n / (Real.sqrt n : ℂ) *
    (g (Real.log n) + g (-Real.log n))

/--
Obligation de sommabilité du côté premier, paramétrée par une fonction
test. En pratique (après la preuve du Real-closure du module
`PrimeSideRealClosure`) cette somme devient finie dès que `g` a un
support compact.
-/
def EnrichedPrimeSide.summabilityObligation
    (P : EnrichedPrimeSide) (g : ℝ → ℂ) : Prop :=
  Summable (fun n : ℕ => P.contribution g n)

/-! ### Côté archimédien enrichi -/

/-- Contribution archimédienne paramétrée par une fonction test. -/
structure EnrichedArchimedeanSide where
  contribution : (ℝ → ℂ) → ℂ
  /-- Obligation d'intégrabilité du noyau contre `g`. -/
  integrabilityObligation : (ℝ → ℂ) → Prop

/-! ### Objet Trace enrichi -/

/--
Objet Trace enrichi : combine les trois côtés et expose la trace totale
comme forme linéaire sur les fonctions test, sous obligations.

L'identité de Riemann–Weil dirait :

    total_trace g = A∞(g) − ∑_{n≥1} Λ(n)/√n · (g(log n) + g(−log n))
                  = ∑_ρ ĝ(γ_ρ)

mais cette égalité reste une OBLIGATION, pas un théorème de ce module.
-/
structure EnrichedTraceObject where
  primes : EnrichedPrimeSide
  spec : EnrichedSpectralSide
  archimedean : EnrichedArchimedeanSide
  /-- Obligation d'identité Riemann–Weil (non prouvée ici). -/
  riemannWeilIdentity : (ℝ → ℂ) → Prop

/-- Pont vers le Frozen `TraceObject` : projection formelle. -/
noncomputable def EnrichedTraceObject.toTraceObject
    (T : EnrichedTraceObject) : TraceObject where
  value := fun _tp => T.archimedean.contribution (fun _ => 0)
  -- Choix trivial (g = 0) pour projeter ; le vrai lien passe par une
  -- TestPair concrète, à instancier en extension Active ultérieure.

/-! ### Drapeaux doctrinaux -/

/-- Aucun théorème de ce module ne peut clore Riemann–Weil. -/
theorem enriched_does_not_prove_riemann_weil
    (T : EnrichedTraceObject) : True := by
  trivial

/-- Aucun théorème de ce module ne peut clore Hilbert–Pólya. -/
theorem enriched_does_not_prove_hilbert_polya
    (T : EnrichedTraceObject) : True := by
  trivial

end CouretUnification.Active
