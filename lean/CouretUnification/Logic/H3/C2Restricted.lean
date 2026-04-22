/-
  CouretUnification/Logic/H3/C2Restricted.lean

  Formule explicite restreinte + pont analytique vers MainTermPositive.

  RHClaimed = false.

  ═══════════════════════════════════════════════════════════════════
  CHANGEMENT PAR RAPPORT À v35.1 STRICTE
  ═══════════════════════════════════════════════════════════════════
  La version stricte définissait `M_sigma` et `R_sigma` comme des
  constantes opaques typées par `(ℂ → ℂ) → (CharIdx → ℂ → ℂ) →
  Finset CharIdx → ℝ → H3TestFunction → ℂ`.

  Cette version 2 :
    1. PRÉSERVE ces constantes (pas de break API) ;
    2. AJOUTE les versions réelles `explicitMainTerm` et
       `explicitResidualTerm` typées `ℝ → OperativeTestPacket → ℝ`,
       qui opèrent sur les paquets opératoires et donnent des
       résultats réels (intégrales de fonctions paires à valeurs
       réelles, une fois l'hypothèse de parité donnée) ;
    3. AJOUTE l'axiome `mainTermPositive_of_positiveBias` : c'est
       le pont analytique clef qui relie le biais de positivité
       (certifié dans OperativeTestPacket) à la positivité stricte
       du terme principal (utilisée dans C3Weak).

  C'est ici que les POIDS ARITHMÉTIQUES (8 canaux mod 30) peuvent
  être injectés, via une future généralisation :
      explicitMainTerm_Couret : ℝ → OperativeTestPacket →
                                CouretHarmonicWeight → ℝ
  L'interface actuelle reste neutre (non pondérée), pour ne pas
  préjuger du choix congruences vs caractères.
  ═══════════════════════════════════════════════════════════════════
-/

import CouretUnification.Logic.H3.H3TestSpace
import CouretUnification.Logic.H3.ParityGamma30
import CouretUnification.Logic.H3.RigidityParams

namespace CouretUnification.Logic.H3

open CouretUnification.Core

-- ═══════════════════════════════════════════════════════════════════
-- §1. Compatibilité avec l'API v35.1 stricte (inchangée)
-- ═══════════════════════════════════════════════════════════════════

opaque E_sigma : ℝ → H3TestFunction → ℂ
opaque M_sigma :
  (ℂ → ℂ) → (CharIdx → ℂ → ℂ) → Finset CharIdx → ℝ → H3TestFunction → ℂ
opaque R_sigma :
  (ℂ → ℂ) → (CharIdx → ℂ → ℂ) → Finset CharIdx → ℝ → H3TestFunction → ℂ

def RestrictedExplicitFormulaOld
    (D : ℂ → ℂ) (L : CharIdx → ℂ → ℂ) (chars : Finset CharIdx) : Prop :=
  ∀ ⦃σ : ℝ⦄, 1 < σ →
    ∀ f : H3TestFunction,
      E_sigma σ f = M_sigma D L chars σ f + R_sigma D L chars σ f

axiom restricted_explicit_formula_old
    (D : ℂ → ℂ) (L : CharIdx → ℂ → ℂ) (chars : Finset CharIdx) :
    RestrictedExplicitFormulaOld D L chars

-- ═══════════════════════════════════════════════════════════════════
-- §2. API réelle sur OperativeTestPacket (pour C3Weak_v2)
-- ═══════════════════════════════════════════════════════════════════

/-- Évaluation explicite du test sur un paquet opératoire,
    à valeurs réelles (utilise parité + biais). -/
opaque EvaluateExplicit : OperativeTestPacket → ℝ → ℝ

/-- Terme principal réel M_σ(f) pour un paquet opératoire. -/
opaque explicitMainTerm : ℝ → OperativeTestPacket → ℝ

/-- Terme de reste réel R_σ(f), tronqué à N zéros inclus. -/
opaque explicitResidualTerm : ℕ → ℝ → OperativeTestPacket → ℝ

-- ═══════════════════════════════════════════════════════════════════
-- §3. Formule explicite restreinte (version OperativeTestPacket)
-- ═══════════════════════════════════════════════════════════════════

/-- Formule explicite restreinte sur paquets opératoires : E = M + R.
    Paramétrée par N (troncature) et σ (abscisse). -/
def RestrictedExplicitFormula
    (N : ℕ) (f : OperativeTestPacket) (σ : ℝ) : Prop :=
  EvaluateExplicit f σ =
    explicitMainTerm σ f + explicitResidualTerm N σ f

/-- Axiome : la formule explicite restreinte tient pour σ > 1.
    Ce résultat analytique sera dérivé hors Lean, via Perron/Mellin. -/
axiom restricted_explicit_formula_holds
    (N : ℕ) (f : OperativeTestPacket) {σ : ℝ} (hσ : 1 < σ) :
    RestrictedExplicitFormula N f σ

-- ═══════════════════════════════════════════════════════════════════
-- §4. Pont analytique CLEF : biais de positivité → M_σ > 0
-- ═══════════════════════════════════════════════════════════════════
-- C'est LE lemme qui fait le travail analytique. Sa preuve hors
-- Lean utilise :
--   (a) la parité de f (symétrie d'inversion ⇒ intégrale sur ℝ₊*
--       symétrique, partie imaginaire nulle) ;
--   (b) le biais de positivité certifié dans OperativeTestPacket
--       (PositiveBiasAt σ ⇒ intégrande strictement positive
--        presque partout) ;
--   (c) la décroissance rapide de la Mellin (contrôle uniforme
--       des queues d'intégration).
-- Dans Lean, c'est un axiome : la difficulté analytique est
-- déportée hors du vérificateur.

/-- Pont analytique : si un paquet possède le biais de positivité à
    σ > 1, alors son terme principal est strictement positif. -/
axiom mainTermPositive_of_positiveBias
    (f : OperativeTestPacket) (σ : ℝ) (hσ : 1 < σ) :
    PositiveBiasAt σ f.toH3TestFunction →
    0 < explicitMainTerm σ f

end CouretUnification.Logic.H3
