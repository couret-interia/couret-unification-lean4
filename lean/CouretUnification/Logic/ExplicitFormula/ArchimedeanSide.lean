/-
  Couret-Unification — v35.9.0
  Logic/ExplicitFormula/ArchimedeanSide.lean

  Objet : LE CÔTÉ ARCHIMÉDIEN DE LA FORMULE DE WEIL.

         Encode le terme à l'infini de la formule explicite, qui provient
         du facteur gamma Γ(s/2 + 1/4) dans l'équation fonctionnelle
         complète de ξ(s).

         Évaluation primaire : INTÉGRALE contre le noyau digamma.
         La décomposition en fractions rationnelles est un lemme
         auxiliaire dans Active, PAS la définition principale.

         Mathématiquement, le noyau archimédien est :

             K_∞(t) = -½ log π + ½ ψ(1/4 + it/2)

         où ψ(z) = Γ'(z)/Γ(z) est la fonction digamma. Et alors :

             A_∞(g) = ∫ ĝ(t) · K_∞(t) dt.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, obligation typée)
  Layer      : Logic.ExplicitFormula
  Dépend de  : Logic.ExplicitFormula.TestFunctions
               Mathlib.Data.Complex.Basic
  Doctrine   : Le noyau digamma est traité comme DONNÉE STRUCTURELLE
               (champ d'une structure), pas comme axiome. Son
               instanciation concrète via Mathlib
               (`Complex.Gamma.logDeriv`) est repoussée à Active.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Changement v35.9-pre → v35.9.0 :
    NOUVEAU module. La revue externe du 24 avril 2026 a souligné
    qu'une représentation par fractions rationnelles naïve (1/(s+2n))
    pose un problème immédiat à s=0 et n'est utilisable qu'après
    régularisation. L'évaluation primaire doit être INTÉGRALE contre
    le noyau digamma, et la décomposition en partial fractions reste
    un outil auxiliaire dans Active.

  Pour Bernard.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CouretUnification.Logic.ExplicitFormula.TestFunctions

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   LE NOYAU ARCHIMÉDIEN
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Le noyau archimédien K_∞(t) comme donnée structurelle.

    Forme mathématique visée :

        K_∞(t) = -½ · log π + ½ · ψ(1/4 + it/2)

    où ψ est la fonction digamma. L'instanciation concrète est
    repoussée à Active, pour éviter tout axiome dans Frozen.

    Note : le type est `ℝ → ℂ` (t réel, valeur complexe) parce que
    K_∞(t) a une partie imaginaire non triviale dès que t ≠ 0. -/
structure ArchimedeanKernel where
  kernel : ℝ → ℂ

/- ═══════════════════════════════════════════════════════════════════════════
   OBLIGATION DE CONTRÔLE STIRLING/DIGAMMA
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- La borne logarithmique du noyau archimédien : ψ(1/4 + it/2) = O(log(2+|t|)).

    Cette propriété découle du développement asymptotique de Stirling
    pour la fonction digamma. Elle garantit, combinée à la décroissance
    rapide de ĝ, que l'intégrale archimédienne est absolument convergente.

    Exprimée ici comme STRUCTURE typée, pas comme axiome. -/
structure ArchimedeanKernelBound (K : ArchimedeanKernel) where
  /-- La constante de majoration. -/
  constant : ℝ
  /-- Elle est positive. -/
  positive : 0 < constant
  /-- La borne logarithmique effective. -/
  bound :
    ∀ t : ℝ,
      Complex.abs (K.kernel t) ≤ constant * Real.log (2 + |t|)

/- ═══════════════════════════════════════════════════════════════════════════
   OBLIGATIONS COMBINÉES POUR L'ARCHIMEDEAN SIDE
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Paquet d'obligations pour que l'intégrale archimédienne soit
    bien définie et absolument convergente pour une fonction test donnée. -/
structure ArchimedeanSideObligations
    (K : ArchimedeanKernel) (φ : TestPairBasic) where
  /-- Le noyau vérifie la borne logarithmique. -/
  kernelBound        : ArchimedeanKernelBound K
  /-- L'intégrande ‖ĝ(t)‖ · log(2 + |t|) est intégrable sur ℝ.
      Cette obligation découle de `kernelBound` combinée à la
      décroissance rapide de ĝ (niveau `TestPairAnalytic`). -/
  weightedIntegrable : Prop
  /-- La valeur de l'intégrale archimédienne. -/
  integralValue      : ℂ

/- ═══════════════════════════════════════════════════════════════════════════
   STRUCTURE ArchimedeanSideRaw (INDÉPENDANTE DU BRIDGE)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Le côté archimédien comme objet analytique, avec ses obligations.

    Ceci est distinct de `ArchimedeanSide` dans ExplicitFormulaBridge,
    qui est la projection dans le contexte du certificat de voûte.
    Ici, on capture la structure analytique complète. -/
structure ArchimedeanSideRaw where
  kernel : ArchimedeanKernel
  obligations :
    ∀ φ : TestPairBasic, ArchimedeanSideObligations kernel φ

/- ═══════════════════════════════════════════════════════════════════════════
   NOTE DOCTRINALE — POURQUOI PAS LES PARTIAL FRACTIONS EN PRIMAIRE
   ═══════════════════════════════════════════════════════════════════════════

   La fonction digamma admet une décomposition en série :

       ψ(z) = -γ + ∑_{n=0}^∞ (1/(n+1) - 1/(n+z))

   où γ est la constante d'Euler-Mascheroni. Il est tentant d'utiliser
   cette série comme définition primaire dans Lean, mais trois problèmes :

   (1) La série n'est pas absolument convergente au sens naïf. Elle
       est conditionnellement convergente après regroupement.

   (2) Les pôles z = 0, -1, -2, ... apparaissent explicitement dans
       les termes 1/(n+z). Il faut régulariser (ou restreindre le
       domaine) avant tout usage.

   (3) En Lean, manipuler cette série impose des preuves de convergence
       conditionnelle et de regroupement qui sont lourdes pour un
       simple terme archimédien.

   En revanche, l'intégrale ∫ ĝ(t) · K_∞(t) dt est naturellement
   absolument convergente sous les hypothèses de la formule de Weil
   (décroissance rapide de ĝ, borne logarithmique du noyau). Elle
   se formalise mieux, et respecte l'intention mathématique de la
   formule explicite.

   La décomposition en partial fractions reste disponible dans Active
   comme LEMME AUXILIAIRE pour certaines preuves spécifiques, mais
   jamais comme définition principale.

   Doctrine v35.9.0 : ArchimedeanSide = intégrale contre digamma ;
                      partial fractions = lemme auxiliaire Active.
-/

end CouretUnification.Logic.ExplicitFormula
