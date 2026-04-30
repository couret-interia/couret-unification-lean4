/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/ArchimedeanSide.lean

  Objet : CORRECTION PARAMÉTRIQUE v35.9.1.

         v35.9.0 contenait encore une tentation d'introduire
         `constant digamma : ℂ → ℂ` dans Frozen. La revue doctrinale
         finale a tranché : PAS DE constante analytique locale
         dans Frozen.

         En v35.9.1, le noyau archimédien est porté par une structure
         paramétrée `ArchimedeanKernelData`. Le noyau digamma/Stirling
         réel est instancié DANS Active, jamais dans Frozen.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, 0 constante analytique)
  Layer      : Logic.ExplicitFormula
  Dépend de  : TestPair, Mathlib real log
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0
  localConstants         : 0 (NOUVEAU invariant v35.9.1)

  Changement v35.9.0 → v35.9.1 :
    `constant digamma` supprimée. Remplacée par `ArchimedeanKernelData`
    paramétrée qui porte le noyau et sa borne logarithmique comme
    champs structuraux. En Active, on instanciera :
        K_∞(t) = -½ log π + ½ ψ(1/4 + it/2)
    avec ψ = Γ'/Γ pris dans Mathlib.

  Pour Bernard.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CouretUnification.Logic.ExplicitFormula.TestPair
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/-- Données paramétriques du noyau archimédien.

    Frozen ne définit PAS digamma et NE revendique PAS la borne de
    Stirling. Il ne porte que la forme de l'obligation.

    En Active, cette structure pourra être instanciée avec :
        kernel t = -½ log π + ½ ψ(1/4 + it/2)
    et `logarithmicBound` prouvée par Stirling. -/
structure ArchimedeanKernelData where
  kernel           : ℝ → ℂ
  logarithmicBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, Complex.abs (kernel t) ≤ C * Real.log ((2 : ℝ) + |t|)

/-- Obligations du côté archimédien pour un couple test donné.

    `weightedIntegrable` reste typé `Prop` — son contenu effectif
    (intégrabilité de |ĝ(t)| · log(2+|t|)) est réservé à Active où
    Fourier, Schwartz et convergence dominée sont disponibles. -/
structure ArchimedeanSideObligations (φ : TestPair) where
  kernelData         : ArchimedeanKernelData
  weightedIntegrable : Prop

/-- ArchimedeanSide comme FormulaSide paramétré.

    Aucune identification concrète. L'instanciation de
    `side.value = ∫ ĝ(t) · K_∞(t) dt` appartient à Active. -/
structure ArchimedeanSide where
  side        : FormulaSide
  obligations : ∀ φ : TestPair, ArchimedeanSideObligations φ

/-- Certificat que l'ArchimedeanSide coïncide avec le TraceObject.
    Il s'agit d'une forme d'égalité, pas d'un théorème prouvé. -/
structure ArchimedeanEqualsTrace
    (A : ArchimedeanSide) (T : TraceObject) : Prop where
  eq_trace : ∀ φ : TestPair, A.side.value φ = T.value φ

/- ═══════════════════════════════════════════════════════════════════
   NOTE DOCTRINALE v35.9.1
   ═══════════════════════════════════════════════════════════════════

   L'évaluation primaire de l'ArchimedeanSide reste INTÉGRALE contre le
   noyau digamma. La décomposition en partial fractions (ψ(z) = -γ + Σ
   (1/(n+1) - 1/(n+z))) est un LEMME AUXILIAIRE Active, jamais la
   définition principale — elle a un problème immédiat en z=0, -1, -2, …

   Frozen v35.9.1 ne contient donc :
     - ni `constant digamma`,
     - ni série de fractions rationnelles,
     - ni noyau explicite concret.

   Frozen v35.9.1 contient seulement la FORME des obligations :
     - un noyau paramétré `ArchimedeanKernelData.kernel`,
     - une borne logarithmique à instancier par Stirling en Active,
     - une intégrabilité pondérée à établir en Active.
-/

end CouretUnification.Logic.ExplicitFormula
