/-
  Couret-Unification — v35.9.0
  Logic/ExplicitFormula/TestFunctions.lean

  Objet : fonctions test pour la formule explicite de Riemann–Weil.
         Définit le couple (g, ĝ) avec convention Fourier figée et
         les obligations analytiques minimales pour que les quatre
         sides (Prime, Zero, Archimedean, Det2) soient bien définis.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structures uniquement)
  Layer      : Logic.ExplicitFormula
  Doctrine   : NO RH HYPOTHESIS allowed in this file.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Stratification (4 niveaux) :
    Niveau 1 — TestPairBasic        : g ∈ C_c^∞, fhat défini, convention figée
    Niveau 2 — TestPairAnalytic     : décroissance rapide de fhat
    Niveau 3 — TestPairAdmissible   : sides Prime/Zero/Arch tous bien définis
    Niveau 4 — GuinandWeilTestPair  : extension exp-decay (phase ultérieure)

  Convention Fourier figée v35.9 :

      fhat(t) = ∫ f(x) · exp(-i · t · x) dx       (negativeExp)

  Changements v35.9-pre → v35.9.0 :
    • Float → ℝ/ℂ via Mathlib (passage à la représentation réelle).
    • NontrivialZero : ℝ au lieu de Float pour re, im.
    • `compactSupport_g` typé avec `ℝ` et `abs` réel.

  Pour Bernard.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Complex.Basic

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   CONVENTION FOURIER (figée v35.9)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Convention Fourier du dépôt. Doctrinalement figée à `negativeExp`. -/
inductive FourierConvention where
  | negativeExp   -- fhat(t) = ∫ f(x) · exp(-i·t·x) dx
  | positiveExp   -- fhat(t) = ∫ f(x) · exp( i·t·x) dx
deriving DecidableEq, Repr

/-- La convention canonique du dépôt. -/
def canonicalFourierConvention : FourierConvention := FourierConvention.negativeExp

/- ═══════════════════════════════════════════════════════════════════════════
   ZÉROS NON TRIVIAUX (dans la bande critique, sans hypothèse RH)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Zéro non trivial de zêta.

    Important : on suppose seulement `0 < re < 1` (bande critique). On
    n'impose JAMAIS `re = 1/2` ici. Cette hypothèse appartient
    exclusivement au théorème final `RH_from_HP_certificate`. -/
structure NontrivialZero where
  re              : ℝ
  im              : ℝ
  inCriticalStrip : Prop    -- intended : 0 < re ∧ re < 1
  isZero          : Prop    -- intended : zeta (re + i·im) = 0
  multiplicity    : Nat

/-- L'ordonnée d'un zéro non trivial. -/
def gamma (ρ : NontrivialZero) : ℝ := ρ.im

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 1 — TESTPAIR BASIC
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Couple test (g, ĝ) au niveau 1 : régularité, support compact, convention.

    Note v35.9.0 : les champs analytiques (`smooth_g`, `fourierLinked`)
    restent des `Prop` au niveau structurel pour éviter de lier Frozen à
    des définitions Mathlib complexes. La couche Active leur fournit leur
    contenu concret via `ContDiff ℝ ⊤ g`, etc. -/
structure TestPairBasic where
  /-- La fonction test sur la variable logarithmique. -/
  g                 : ℝ → ℂ
  /-- Sa transformée de Fourier (donnée structurelle). -/
  ghat              : ℝ → ℂ
  /-- g est lisse (intended : ContDiff ℝ ⊤ g). -/
  smooth_g          : Prop
  /-- g a support compact dans [-A, A] pour un certain A > 0. -/
  compactSupport_g  : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A < |x| → g x = 0
  /-- Convention Fourier utilisée. Doctrinalement = negativeExp. -/
  fourierConvention : FourierConvention
  /-- ĝ est bien la transformée de Fourier de g. -/
  fourierLinked     : Prop

/-- Convention figée : un TestPairBasic admissible utilise negativeExp. -/
def TestPairBasic.usesCanonicalConvention (φ : TestPairBasic) : Prop :=
  φ.fourierConvention = FourierConvention.negativeExp

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 2 — TESTPAIR ANALYTIC
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Niveau 2 : ajoute la décroissance rapide de ĝ et l'intégrabilité du
    terme archimédien. -/
structure TestPairAnalytic extends TestPairBasic where
  /-- ĝ décroît plus vite que tout polynôme. -/
  rapidDecay_ghat       : Prop
  /-- L'intégrale ∫ |ĝ(t)| · log(2 + |t|) dt est finie. -/
  archimedeanIntegrable : Prop

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 3 — TESTPAIR ADMISSIBLE
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Niveau 3 : prêt à être consommé par `ExplicitFormulaCertificate`. -/
structure TestPairAdmissible extends TestPairAnalytic where
  primeSideFinite           : Prop
  zeroSideSummable          : Prop
  archimedeanSideDefined    : Prop
  det2SideDefinedConditional : Prop

/-- Critère d'admissibilité minimal pour le pont. -/
def Admissible (φ : TestPairAdmissible) : Prop :=
  φ.usesCanonicalConvention
  ∧ φ.smooth_g
  ∧ φ.fourierLinked
  ∧ φ.rapidDecay_ghat
  ∧ φ.archimedeanIntegrable
  ∧ φ.primeSideFinite
  ∧ φ.zeroSideSummable
  ∧ φ.archimedeanSideDefined

/- ═══════════════════════════════════════════════════════════════════════════
   PIÈGE DOCTRINAL À ÉVITER
   ═══════════════════════════════════════════════════════════════════════════

   Ne JAMAIS introduire dans ce module un champ tel que :

       rho_on_critical_line : ∀ ρ : NontrivialZero, ρ.re = 1/2

   Cela injecterait RH dans la définition d'admissibilité.
-/

end CouretUnification.Logic.ExplicitFormula
