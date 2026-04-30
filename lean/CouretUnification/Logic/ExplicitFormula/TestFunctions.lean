/-
  Couret-Unification — v35.9-pre
  Logic/ExplicitFormula/TestFunctions.lean

  Objet : fonctions test pour la formule explicite de Riemann–Weil.
         Définit le couple (g, ĝ) avec convention Fourier figée et
         les obligations analytiques minimales pour que les quatre
         sides (Prime, Zero, Archimedean, Det2) soient bien définis.

  Statut     : Frozen-eligible (0 sorry, structures uniquement)
  Layer      : Logic.ExplicitFormula
  Doctrine   : NO RH HYPOTHESIS allowed in this file.
               In particular, no field may impose `ρ.re = 1/2`.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0

  Stratification (4 niveaux, pour permettre la promotion incrémentale) :

    Niveau 1 — TestPairBasic        : g ∈ C_c^∞, fhat défini, convention figée
    Niveau 2 — TestPairAnalytic     : décroissance rapide de fhat
    Niveau 3 — TestPairAdmissible   : sides Prime/Zero/Arch tous bien définis
    Niveau 4 — GuinandWeilTestPair  : extension exp-decay (phase ultérieure)

  Convention Fourier figée v35.9 :

      fhat(t) = ∫ f(x) · exp(-i · t · x) dx       (negativeExp)

  Aucun module ne doit silencieusement basculer vers la convention
  positiveExp. Cette décision est doctrinale et ne se modifie qu'à
  l'unanimité du dépôt.

  Pour Bernard.
-/

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   CONVENTION FOURIER (figée v35.9)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Convention Fourier du dépôt. Doctrinalement figée à `negativeExp`. -/
inductive FourierConvention where
  | negativeExp   -- fhat(t) = ∫ f(x) · exp(-i·t·x) dx
  | positiveExp   -- fhat(t) = ∫ f(x) · exp( i·t·x) dx
deriving DecidableEq, Repr

/-- La convention canonique du dépôt (lecture seule). -/
def canonicalFourierConvention : FourierConvention := FourierConvention.negativeExp

/- ═══════════════════════════════════════════════════════════════════════════
   ZÉROS NON TRIVIAUX (dans la bande critique, sans hypothèse RH)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Zéro non trivial de zêta.

    Important : on suppose seulement `0 < re < 1` (bande critique). On
    n'impose JAMAIS `re = 1/2` ici. Cette hypothèse appartient
    exclusivement au théorème final `RH_from_HP_certificate` et ne doit
    pas être injectée silencieusement dans la définition d'admissibilité. -/
structure NontrivialZero where
  re             : Float
  im             : Float
  inCriticalStrip : Prop   -- intended : 0 < re ∧ re < 1
  isZero          : Prop   -- intended : zeta (re + i·im) = 0
  multiplicity    : Nat

/-- L'ordonnée d'un zéro non trivial. -/
def gamma (ρ : NontrivialZero) : Float := ρ.im

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 1 — TESTPAIR BASIC
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Couple test (g, ĝ) au niveau 1 : régularité, support compact, convention.

    Tous les champs analytiques (`smooth_g`, `compactSupport_g`,
    `fourierLinked`) sont laissés en `Prop`. Leur définition concrète
    est fournie par la couche Active (qui peut importer Mathlib pour
    `ContDiff`, `HasCompactSupport`, etc.). Ce module ne dépend de rien
    d'autre que de `Float` pour rester aussi léger que possible. -/
structure TestPairBasic where
  /-- La fonction test sur la variable logarithmique. -/
  g                 : Float → Float
  /-- Sa transformée de Fourier (donnée structurelle pour le moment). -/
  ghat              : Float → Float
  /-- g est lisse (intended : ContDiff ℝ ⊤ g). -/
  smooth_g          : Prop
  /-- g a support compact dans [-A, A] pour un certain A > 0. -/
  compactSupport_g  : ∃ A : Float, A > 0 ∧ ∀ x : Float, x.abs > A → g x = 0
  /-- La convention Fourier utilisée pour ĝ. Doctrinalement = negativeExp. -/
  fourierConvention : FourierConvention
  /-- ĝ est bien la transformée de Fourier de g sous cette convention. -/
  fourierLinked     : Prop

/-- Convention figée : un TestPairBasic admissible utilise negativeExp. -/
def TestPairBasic.usesCanonicalConvention (φ : TestPairBasic) : Prop :=
  φ.fourierConvention = FourierConvention.negativeExp

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 2 — TESTPAIR ANALYTIC
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Niveau 2 : ajoute la décroissance rapide de ĝ et l'intégrabilité du
    terme archimédien.

    La décroissance rapide est essentielle pour le ZeroSide : combinée à
    Riemann–von Mangoldt, elle assure la sommabilité absolue
    `∑_ρ |ĝ(γ_ρ)| < ∞`.

    L'intégrabilité archimédienne couvre le terme `∫ |ĝ(t)| · log(2 + |t|) dt`
    issu de la dérivée logarithmique de Γ(s/2 + 1/4) dans la formule de Weil. -/
structure TestPairAnalytic extends TestPairBasic where
  /-- ĝ décroît plus vite que tout polynôme :
      ∀ N, ∃ C, ∀ t, |ĝ(t)| ≤ C / (1 + |t|)^N. -/
  rapidDecay_ghat       : Prop
  /-- L'intégrale ∫ |ĝ(t)| · log(2 + |t|) dt est finie. -/
  archimedeanIntegrable : Prop

/- ═══════════════════════════════════════════════════════════════════════════
   NIVEAU 3 — TESTPAIR ADMISSIBLE (pour le bridge complet)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Niveau 3 : prêt à être consommé par `ExplicitFormulaCertificate`.

    Les quatre sides sont garantis bien définis : PrimeSide est fini
    (par support compact), ZeroSide est sommable (par rapidDecay +
    Riemann–von Mangoldt), ArchimedeanSide est intégrable, Det2Side
    est défini conditionnellement (cf. AnalyticHorizon/Det2Obligations). -/
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
   THÉORÈME-PILIER : SUPPORT COMPACT ⇒ PRIMESIDE FINI
   ═══════════════════════════════════════════════════════════════════════════

   La compression FCI appliquée à la formule explicite. Si supp(g) ⊂ [-A,A],
   alors pour tout n tel que log n > A, on a g(±log n) = 0, et donc le
   terme arithmétique correspondant s'annule.

   La démonstration analytique complète (qui transforme le `tsum` infini
   en `Finset.sum` fini via `Real.exp A`) appartient à
   `Logic/ExplicitFormula/PrimeSide.lean` (Active). Ce module se contente
   d'exposer la *spécification* de cette propriété sous forme typée.
-/

/-- Spécification : pour tout TestPair à support compact, il existe un
    seuil au-delà duquel tous les termes arithmétiques s'annulent. -/
def PrimeSideHasFiniteSupport (φ : TestPairBasic) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N < n →
    -- Le terme primaire à l'indice n s'annule.
    -- Forme symbolique pour spec ; définition concrète dans PrimeSide.lean.
    φ.g (Float.log n.toFloat) = 0 ∧ φ.g (-Float.log n.toFloat) = 0

/- ═══════════════════════════════════════════════════════════════════════════
   PIÈGE DOCTRINAL À ÉVITER (en commentaire, jamais en Lean)
   ═══════════════════════════════════════════════════════════════════════════

   Ne JAMAIS introduire dans ce module un champ tel que :

       rho_on_critical_line : ∀ ρ : NontrivialZero, ρ.re = 1/2

   Cela injecterait RH dans la définition d'admissibilité, créant une
   tautologie qui invaliderait toute revendication ultérieure. La position
   des zéros sur la ligne critique est la *conclusion* du théorème
   `RH_from_HP_certificate`, jamais une *prémisse* de TestPair.

   La somme spectrale `∑_ρ ĝ(γ_ρ)` doit pouvoir s'écrire sur des zéros
   `ρ = β + iγ` avec β quelconque dans (0,1).
-/

end CouretUnification.Logic.ExplicitFormula
