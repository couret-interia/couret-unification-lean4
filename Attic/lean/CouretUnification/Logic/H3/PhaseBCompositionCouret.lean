/-
  CouretUnification/Logic/H3/PhaseBCompositionCouret.lean

  Spécialisations Couret de la composition Phase B.

  ═══════════════════════════════════════════════════════════════════
  RÔLE DE CE FICHIER
  ═══════════════════════════════════════════════════════════════════
  Ce fichier étend `PhaseBComposition` avec **cinq branches
  spécialisées au triplet de Couret** TC = {1, 11, 29}, qui
  consomment les pierres angulaires de la pile arithmético-spectrale
  (Lambda, Parseval, ParsevalL5, T1_to_T7, FiniteCore) et les
  câblent à la chaîne H3.

  Ces branches sont structurellement disjointes (pas de chaîne
  unifiée à composer), mais leur agrégation dans ce fichier rend
  visible que chaque résultat est désormais consommé par la
  frontière H3 du programme.

  Les cinq branches Couret-spécifiques :

    C-α — Pythagoréité du triplet
          ‖tcInd‖² = ‖p3 tcInd‖² + ‖p1 tcInd‖² + ‖pminus tcInd‖²
          Consume : FiniteDefect/T1_to_T7

    C-β — Gap coercif κ = 2
          ∀ x ∈ Centered8, GoodSubspace x → 2·‖x‖² ≤ Q(x)
          Consume : Spectral/FiniteCore

    C-γ — Parseval = 24
          parsevalMass = 24
          Consume : Core/Parseval (et transitivement SpectralProfile)

    C-δ — Tour Parseval + invariant normalisé E/|TC_cop| = 1
          parsevalMass {30, 210, 2310} = {24, 144, 960}
          normalizedEnergy {30, 210, 2310} = {1, 1, 1}
          Consume : Core/ParsevalL5

    C-ε — Invariant emblématique λ² = 1/7
          lambda8 ^ 2 = 1/7
          Consume : Core/Lambda

  ═══════════════════════════════════════════════════════════════════
  EFFETS ATTENDUS SUR LE GRAPHE DE COMPILATION
  ═══════════════════════════════════════════════════════════════════
  Ce fichier importe les cinq cibles directes plus PhaseBComposition
  (déjà câblé). Il tire transitivement :

    via Lambda                  : Lambda
    via Parseval                : Parseval, SpectralProfile
    via ParsevalL5              : ParsevalL5
    via FiniteDefect.T1_to_T7   : T1_to_T7, Finite/Foundations
    via Spectral.FiniteCore     : FiniteCore (et ses dépendances Mathlib)
    via PhaseBComposition       : (héritage des 13 modules Logic.H3)

  Audit (AlgebraTC, RouteC, PhaseBComposition, PhaseBCompositionCouret)
  attendu : passage de 30 modules atteints à environ 37-40.

  ═══════════════════════════════════════════════════════════════════
  GARDE DOCTRINALE
  ═══════════════════════════════════════════════════════════════════
  RHClaimed = false. Aucun sorry consommé par les cinq branches
  Couret (toutes sont des réexpositions de théorèmes prouvés). Les
  sorries doctrinaux du programme restent localisés dans
  Lemma7Residual (consommé seulement par PhaseBComposition.β.2),
  RouteC, et CayleyG30 (chaîne arithmétique indépendante).
  ═══════════════════════════════════════════════════════════════════
-/

import CouretUnification.Logic.H3.PhaseBComposition
import CouretUnification.Core.Lambda
import CouretUnification.Core.Parseval
import CouretUnification.Core.ParsevalL5
import CouretUnification.FiniteDefect.T1_to_T7
import CouretUnification.Spectral.FiniteCore

namespace CouretUnification.Logic.H3.PhaseBCompositionCouret

-- ═══════════════════════════════════════════════════════════════════
-- §1. Branche C-α — Pythagoréité du triplet de Couret
-- ═══════════════════════════════════════════════════════════════════

/-- **Branche C-α — Pythagoréité du triplet.**

    L'indicatrice du triplet `tcInd` se décompose orthogonalement
    sur les trois secteurs propres :

      ‖tcInd‖² = ‖p3 tcInd‖² + ‖p1 tcInd‖² + ‖pminus tcInd‖²

    Soit explicitement : 3 = 5/4 + 1/2 + 5/4.

    Aucun sorry, aucun axiome. Réexposition de
    `T7_pythagoras_tc` (preuve par `native_decide`). -/
theorem branch_pythagoras_couret :
    CouretUnification.Finite.normSq CouretUnification.Finite.tcInd =
      CouretUnification.Finite.normSq
          (CouretUnification.Finite.p3 CouretUnification.Finite.tcInd)
      + CouretUnification.Finite.normSq
          (CouretUnification.Finite.p1 CouretUnification.Finite.tcInd)
      + CouretUnification.Finite.normSq
          (CouretUnification.Finite.pminus CouretUnification.Finite.tcInd) :=
  CouretUnification.FiniteDefect.T7_pythagoras_tc

-- ═══════════════════════════════════════════════════════════════════
-- §2. Branche C-β — Gap coercif κ = 2
-- ═══════════════════════════════════════════════════════════════════

/-- **Branche C-β — Gap coercif κ = 2.**

    Sur le sous-espace centré `Centered8` (∑ x_i = 0) et coercif
    (`GoodSubspace x ↔ ⟨x, altVec⟩ = 0`), la forme quadratique
    `Q(x) = ⟨Lx, x⟩` du laplacien centré `L = 3I − M` admet la
    borne inférieure :

      2 · ‖x‖² ≤ Q(x)

    Aucun sorry, aucun axiome. Réexposition de
    `finite_exact_gap_kappa_two` (preuve par factorisation explicite
    + `nlinarith` sur les sommes de blocs aSum/bSum/cSum/dSum). -/
theorem branch_coercive_gap
    (x : CouretUnification.FiniteCore.Centered8)
    (hx : CouretUnification.FiniteCore.GoodSubspace x) :
    2 * x.normSq ≤ CouretUnification.FiniteCore.quadratic x.1 :=
  CouretUnification.FiniteCore.finite_exact_gap_kappa_two x hx

-- ═══════════════════════════════════════════════════════════════════
-- §3. Branche C-γ — Parseval = 24 (cas Couret)
-- ═══════════════════════════════════════════════════════════════════

/-- **Branche C-γ — Parseval = 24.**

    Pour le triplet de Couret TC = {1, 11, 29} sur (ℤ/30ℤ)×, la
    masse de Parseval vaut exactement :

      P = φ(30) · |TC| = 8 · 3 = 24

    Aucun sorry, aucun axiome. Réexposition de
    `parsevalMass_eq_24` (preuve par `simpa` sur l'identité
    `TCParsevalMass_eq` du module SpectralProfile). -/
theorem branch_parseval_couret :
    CouretUnification.Core.parsevalMass = 24 :=
  CouretUnification.Core.parsevalMass_eq_24

-- ═══════════════════════════════════════════════════════════════════
-- §4. Branche C-δ — Tour Parseval + invariant normalisé
-- ═══════════════════════════════════════════════════════════════════

/-- **Branche C-δ.1 — Tour de Parseval mod q ∈ {30, 210, 2310}.**

    Aux trois premiers niveaux de la tour primorielle, la masse de
    Parseval vaut respectivement 24, 144 et 960. La rupture entre L4
    et L5 vient du fait que `gcd(11, 2310) = 11 ≠ 1`, donc 11 sort
    de (ℤ/2310ℤ)× et |TC_cop(2310)| = 2 (au lieu de 3).

    C'est la **correction v17→v18** du programme : la valeur 1440
    annoncée naïvement (3·φ(2310)) est fausse ; la valeur correcte
    est 960.

    Aucun sorry, aucun axiome. Réexposition de trois théorèmes
    `parseval_30`, `parseval_210`, `parseval_2310` (preuves par
    `native_decide`). -/
theorem branch_parseval_tower :
    CouretUnification.Core.ParsevalL5.parsevalMass 30 = 24 ∧
    CouretUnification.Core.ParsevalL5.parsevalMass 210 = 144 ∧
    CouretUnification.Core.ParsevalL5.parsevalMass 2310 = 960 :=
  ⟨CouretUnification.Core.ParsevalL5.parseval_30,
   CouretUnification.Core.ParsevalL5.parseval_210,
   CouretUnification.Core.ParsevalL5.parseval_2310⟩

/-- **Branche C-δ.2 — Invariant normalisé E/|TC_cop| = 1.**

    Bien que l'énergie brute E = P/φ ne soit pas constante le long
    de la tour (3, 3, 2 aux niveaux 30, 210, 2310), l'invariant
    normalisé E/|TC_cop| vaut **exactement 1** aux trois niveaux.

    C'est l'invariant doctrinal stable du programme : la masse
    normalisée par le nombre de représentants effectifs du triplet
    est conservée le long de la tour primorielle.

    Aucun sorry, aucun axiome. Réexposition de
    `normalized_energy_30`, `normalized_energy_210`,
    `normalized_energy_2310`. -/
theorem branch_normalized_energy_invariant :
    CouretUnification.Core.ParsevalL5.normalizedEnergy 30 = 1 ∧
    CouretUnification.Core.ParsevalL5.normalizedEnergy 210 = 1 ∧
    CouretUnification.Core.ParsevalL5.normalizedEnergy 2310 = 1 :=
  ⟨CouretUnification.Core.ParsevalL5.normalized_energy_30,
   CouretUnification.Core.ParsevalL5.normalized_energy_210,
   CouretUnification.Core.ParsevalL5.normalized_energy_2310⟩

-- ═══════════════════════════════════════════════════════════════════
-- §5. Branche C-ε — Invariant emblématique λ² = 1/7
-- ═══════════════════════════════════════════════════════════════════

/-- **Branche C-ε — Invariant λ² = 1/7.**

    L'invariant `λ = 1/√7` du programme satisfait l'identité
    élémentaire mais structurante :

      λ² = 1/7

    Cette valeur est l'**échelle géométrique canonique** issue de
    la dimension dim(H°) = 7 du sous-espace centré (Centered8 a
    pour dimension 8 - 1 = 7).

    Aucun sorry, aucun axiome. Réexposition de `lambda8_sq`
    (preuve par `field_simp` + `nlinarith` sur `Real.sq_sqrt`). -/
theorem branch_lambda_invariant :
    CouretUnification.Core.lambda8 ^ 2 = 1 / 7 :=
  CouretUnification.Core.lambda8_sq

-- ═══════════════════════════════════════════════════════════════════
-- §6. Garde doctrinale
-- ═══════════════════════════════════════════════════════════════════

/-- Marqueur doctrinal : ce fichier ne revendique pas RH. -/
def RHClaimed : Bool := false

/-- Vérification triviale : RHClaimed est false par construction. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Logic.H3.PhaseBCompositionCouret
