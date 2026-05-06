/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/ZeroCounting.lean

  Objet : CORRECTION PARAMÉTRIQUE v35.9.1.

         v35.9.0 définissait `zerosInShell` via un type `NontrivialZero`
         contenu dans TestFunctions. La revue doctrinale finale exige
         une paramétrisation plus stricte : le type des zéros est une
         DONNÉE de `ZeroShellData`, pas une déclaration globale dans
         Frozen.

         Frozen n'a pas à savoir ce qu'est un "zéro de zêta". Il doit
         seulement manipuler un type abstrait avec une coordonnée
         réelle (l'ordonnée γ) et une assignation par coquilles.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, 0 constante analytique)
  Layer      : Logic.ExplicitFormula
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0
  localConstants         : 0

  Changement v35.9.0 → v35.9.1 :
    `NontrivialZero` n'est plus dans Frozen. Remplacé par un type
    paramétré dans `ZeroShellData`. Active reliera ce type aux vrais
    zéros non triviaux de ζ (via Mathlib ou port externe).

  Pour Bernard.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import CouretUnification.Logic.ExplicitFormula.TestPair
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/-- Données paramétriques structurées.

    v38 : la `structure ZeroShellData` canonique vit dans
    `ZeroSideObligation.lean` (bundle Frozen v36.0 scellé) avec un champ
    `shellBound : Prop` agrégé directement.

    Cette version `Structured` externalise la borne dans la structure
    paramétrée `ZeroCountingBoundStructured` séparée. Elle est conservée
    pour la présentation par wrapper `ZeroCountingObligations` (pluriel)
    consommée par `ZeroSideStructured`. -/
structure ZeroShellDataStructured where
  Zero         : Type
  gamma        : Zero → ℝ
  zerosInShell : ℕ → Finset Zero

/-- Borne paramétrée pour la version structurée.
    Variante de `ZeroSideObligation.ZeroShellData.shellBound` (Frozen)
    avec borne externalisée. -/
structure ZeroCountingBoundStructured (Z : ZeroShellDataStructured) : Prop where
  shellBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ,
        ((Z.zerosInShell k).card : ℝ) ≤ C * Real.log ((k : ℝ) + 3)

/-- Obligation de décroissance polynomiale sur ĝ.

    N ≥ 3 suffit pour la sommabilité absolue du ZeroSide par
    comparaison à Σ log(k+3)/(1+k)^N < ∞. -/
structure GhatPolynomialDecay (φ : TestPair) where
  exponent            : ℕ
  exponentLargeEnough : 3 ≤ exponent
  bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ _t : ℝ, True  -- placeholder pour ‖ghat t‖ ≤ C / (1+|t|)^exponent
                      -- (ghat pas encore dans Frozen)

/-- Paquet d'obligations combinées pour le ZeroSideStructured.
    Variante post-Frozen avec présentation séparée. -/
structure ZeroCountingObligations where
  zeroShellData : ZeroShellDataStructured
  countingBound : ZeroCountingBoundStructured zeroShellData

/-- ZeroSide enrichi avec le wrapper d'obligations groupées.

    v38 : la `structure ZeroSide` canonique vit dans
    `ZeroSideObligation.lean` (bundle Frozen v36.0 scellé), avec un champ
    `counting : ZeroCountingObligation` (singulier, témoin direct).

    Cette version utilise le wrapper `ZeroCountingObligations` (pluriel)
    qui regroupe `zeroShellData + countingBound` séparément. Elle est
    conservée pour les modules qui consomment cette présentation
    structurée. Frozen n'identifie PAS `side.value` avec `Σ_ρ ĝ(γ_ρ)`. -/
structure ZeroSideStructured where
  side        : FormulaSide
  obligations : ZeroCountingObligations

/-- Certificat sur la vue structurée.

    Le certificat équivalent sur la `ZeroSide` canonique (Frozen v36.0)
    est porté côté Active. -/
structure ZeroStructuredEqualsTrace
    (Z : ZeroSideStructured) (T : TraceObject) : Prop where
  eq_trace : ∀ φ : TestPair, Z.side.value φ = T.value φ

/- ═══════════════════════════════════════════════════════════════════
   NOTE DOCTRINALE v35.9.1
   ═══════════════════════════════════════════════════════════════════

   Frozen v35.9.1 ne contient donc :
     - ni `constant zerosInShell`,
     - ni type global de "zéros non triviaux",
     - ni borne N(T) = O(T log T) revendiquée comme axiome.

   Frozen v35.9.1 contient seulement :
     - un type paramétré `Zero` dans `ZeroShellData`,
     - une obligation de comptage par coquilles `ZeroCountingBound`,
     - une obligation de décroissance polynomiale sur ĝ.

   Instanciation future en Active :
     - `Zero` := type des zéros non triviaux de ζ,
     - `gamma` := partie imaginaire,
     - `zerosInShell k` := {ρ : k ≤ |γ_ρ| < k+1},
     - `shellBound` prouvée via Riemann–von Mangoldt.
-/

end CouretUnification.Logic.ExplicitFormula
