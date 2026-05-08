/-
================================================================================
  FCI/CausalSupportImmunity.lean
================================================================================
  Programme Couret-Unification · Couche FCI (théorème central abstrait)
  Cible effective : Lean 4.29.1 / Mathlib4

  RÔLE ──────────────────────────────────────────────────────────────────────────

  Théorème maître d'immunité FCI par restriction du support causal :

      ∀ L_IA, supp K^FCI ⊆ U_safe ∪ {u⊥} ⇒ x₀ ∈ S ⇒ x_t ∈ S, ∀ t ≥ 0

  Lecture doctrinale :
      « FCI ne contraint pas le générateur cognitif ; il contraint le support
        causal de son image physique. »

  STATUT ÉPISTÉMIQUE PAR SECTION ────────────────────────────────────────────────

  §1 Types abstraits                          [P] (par construction)
  §2 Politique candidate K_θ                  [P] (axiomatique, abstraite)
  §3 Certificat σ et admissibilité            [P] (par construction)
  §4 Gate filtré K_θ^FCI                      [P] (par construction)
  §5 supp_K_FCI_subset                        [P] (théorème central support)
  §6 Viabilité (Nagumo abstrait)              [C] (axiomatisé pour cette version)
  §7 Théorème d'immunité                      [P] modulo §6
  §8 Spécialisation ModThirtyChecker          [C] (lien avec checker mod 30)

  Note : le générateur informationnel L_IA (variété statistique, Fisher, Amari)
  N'APPARAÎT PAS dans ce fichier. Il est délibérément invisible :
  c'est précisément le contenu mathématique de la doctrine. La preuve
  d'immunité est universellement quantifiée sur tout K_θ — peu importe
  comment il a été engendré.

  CONTRAT DOCTRINAL ─────────────────────────────────────────────────────────────

  Ce module est ABSTRAIT. Il ne dépend ni de FiniteCore, ni de la doctrine λ,
  ni d'aucune hypothèse sur la nature du décideur surveillé. Il s'instancie sur
  tout système (X, U, f, S) muni d'un certificat décidable et d'une action sûre
  u⊥ vérifiant la condition de Nagumo.

  RHClaimed = false.
-/

import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Set

namespace FCI
namespace CausalSupportImmunity

/-! ## §1. Types abstraits -/

class HasSafeAction (U : Type*) where
  safe : U

notation "u⊥" => HasSafeAction.safe

/--
Politique candidate abstraite.

Dans cette version v38, on ne modélise pas encore un noyau de Markov complet.
On ne garde que l'objet utile à la preuve FCI : le support causal possible
des actions physiques.
-/
structure CandidatePolicy (X U T : Type*) where
  causalSupport : X → T → Set U

/--
Certificat de permission. Décidable par construction.
-/
structure Certificate (X U T : Type*) where
  cert : X → U → T → Prop
  decidable : ∀ x u t, Decidable (cert x u t)

attribute [instance] Certificate.decidable

/-- Ensemble admissible local : actions certifiées en `(x, t)`. -/
def admissibleSet {X U T : Type*}
    (σ : Certificate X U T) (x : X) (t : T) : Set U :=
  {u | σ.cert x u t}

/--
L'ensemble admissible est mesurable sous hypothèse explicite.
Cette classe est gardée pour tracer la future version mesure-théorique.
-/
class CertMeasurable {X U T : Type*} [MeasurableSpace U]
    (σ : Certificate X U T) : Prop where
  measurable : ∀ x t, MeasurableSet (admissibleSet σ x t)

/-! ## §4. Gate filtré K_θ^FCI, version support-level -/

/--
Support causal filtré FCI.

Dans la version support-level, le gate remplace tout support candidat par :

    admissibleSet σ x t ∪ {u⊥}

C'est exactement l'information nécessaire au théorème d'immunité.
La version mesure-théorique complète pourra être ajoutée ensuite dans un
fichier séparé.
-/
def gatedKernel {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) : Set U :=
  (K.causalSupport x t ∩ admissibleSet σ x t) ∪ {(u⊥ : U)}

theorem gatedKernel_is_causal_filter {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    gatedKernel K σ x t =
      (K.causalSupport x t ∩ admissibleSet σ x t) ∪ {(u⊥ : U)} := by
  rfl

/-! ## §5. Théorème central : restriction du support -/

theorem supp_gatedKernel_subset {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    gatedKernel K σ x t ⊆ admissibleSet σ x t ∪ {(u⊥ : U)} := by
  intro u hu
  rcases hu with h_candidate_adm | h_safe
  · left
    exact h_candidate_adm.2
  · right
    exact h_safe

/-! ## §6. Viabilité : interface abstraite (Nagumo)

On axiomatise la condition de Nagumo plutôt que de la prouver depuis les
cônes tangents de Bouligand : ce serait un travail Mathlib indépendant
substantiel. Les hypothèses sont rendues EXPLICITES, jamais cachées.
-/

/-- Domaine sûr. Ensemble fermé de l'espace d'état physique. -/
structure SafeDomain (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  isClosed : IsClosed carrier

/-- Condition de viabilité de Nagumo, abstraite.

    Une action `u` est viable en `(x, t)` si la dynamique `f(x, u, t)`
    appartient au cône tangent de la variété sûre en `x`.

    On axiomatise ici l'existence d'un prédicat `viable`, sans entrer dans
    les détails du cône de Bouligand (qui demanderait une partie non triviale
    de Mathlib sur l'analyse non-lisse). -/
structure ViabilityStructure (X U T : Type*) [TopologicalSpace X] where
  S : SafeDomain X
  /-- Dynamique physique f(x, u, t) -/
  f : X → U → T → X
  /-- Prédicat de viabilité : f(x, u, t) appartient au cône tangent de S en x -/
  viable : X → U → T → Prop
  /-- Hypothèse Nagumo : si u est viable en tout point du bord et u⊥ aussi,
      alors S est positivement invariant pour toute trajectoire ne passant que
      par des actions viables. -/
  nagumo_invariance :
    ∀ (x₀ : X) (φ : T → X) (u : T → U),
      x₀ ∈ S.carrier →
      (∀ t, viable (φ t) (u t) t) →
      (∀ t, φ t ∈ S.carrier)

/-- Ensemble des actions viables (U_safe) en (x, t). -/
def viableActions {X U T : Type*}
    [TopologicalSpace X]
    (V : ViabilityStructure X U T) (x : X) (t : T) : Set U :=
  {u | V.viable x u t}

/-! ## §7. Théorème d'immunité FCI

Synthèse : les hypothèses (i) admissible ⊆ viable et (ii) u⊥ viable
impliquent que toute trajectoire physique reste dans le domaine sûr,
indépendamment du générateur cognitif L_IA.
-/

/-- **Théorème d'immunité FCI par restriction du support causal**.

    Hypothèses :
      H1 : Toute action admissible est viable.        (A_σ ⊆ U_safe)
      H2 : L'action sûre u⊥ est viable.              (u⊥ ∈ U_safe)
      H3 : Toute actuation passe par K^FCI.           (Exclusivité du Gate)

    Conclusion :
      Toute trajectoire physique reste dans S, ∀ générateur cognitif L_IA.

    C'est l'énoncé compact :
      ∀ L_IA, supp K^FCI ⊆ U_safe ⇒ x₀ ∈ S ⇒ x_t ∈ S
-/
theorem fci_immunity {X U T : Type*}
    [TopologicalSpace X]
    [HasSafeAction U]
    [MeasurableSpace U]
    (V : ViabilityStructure X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    -- H1 : admissible ⊆ viable, en tout (x, t)
    (h_adm_viable : ∀ x t, admissibleSet σ x t ⊆ viableActions V x t)
    -- H2 : u⊥ est viable en tout (x, t)
    (h_safe_viable : ∀ x t, (u⊥ : U) ∈ viableActions V x t)
    -- Trajectoire engendrée par actions tirées de K^FCI
    (x₀ : X) (φ : T → X) (u : T → U)
    (K : CandidatePolicy X U T)
    -- H3 : actions effectivement tirées du noyau filtré
    (h_action_in_supp : ∀ t, u t ∈ gatedKernel K σ (φ t) t)
    (h_x0 : x₀ ∈ V.S.carrier) :
    ∀ t, φ t ∈ V.S.carrier := by
  -- Stratégie : montrer que toute action u t est viable, puis appliquer Nagumo
  apply V.nagumo_invariance x₀ φ u h_x0
  intro t
  -- u t ∈ supp K^FCI ⊆ admissibleSet ∪ {u⊥}  (par §5)
  have h_supp : u t ∈ admissibleSet σ (φ t) t ∪ {(u⊥ : U)} :=
    supp_gatedKernel_subset K σ (φ t) t (h_action_in_supp t)
  -- Cas : u t admissible OU u t = u⊥
  rcases h_supp with h_adm | h_safe
  · -- Cas admissible : H1 donne viable
    exact h_adm_viable (φ t) t h_adm
  · -- Cas u⊥ : H2 donne viable
    have hEq : u t = (u⊥ : U) := Set.mem_singleton_iff.mp h_safe
    rw [hEq]
    exact h_safe_viable (φ t) t

/-! ## §8. Spécialisation : raccord avec ModThirtyChecker

Le ModThirtyChecker est une instance particulière où :
  - U = espace des sorties cryptographiques candidates
  - σ.cert (x, u, t) ⟺ "kappa²(u) ≤ kappaThresholdCritical"

Le théorème `checker_never_forces_allow` (déjà prouvé dans le module
ModThirtyChecker.lean) établit que cette spécialisation respecte la non-
interférence avec l'autorisation : le checker ne peut que rétrécir
l'admissible, jamais l'élargir.

Ce point est important doctrinalement : l'immunité globale (théorème §7)
est préservée même si le checker est défaillant, car un checker défaillant
ne fait que réduire `admissibleSet`, et un sous-ensemble d'un ensemble
viable reste viable.
-/

/-- Compatibilité de l'immunité avec la composition de certificats.

    Si σ₁ ≤ σ₂ (le premier certificat est plus restrictif), alors
    admissibleSet σ₁ ⊆ admissibleSet σ₂. Donc si admissibleSet σ₂ ⊆ viable,
    a fortiori admissibleSet σ₁ ⊆ viable. -/
theorem fci_immunity_monotone {X U T : Type*}
    (σ₁ σ₂ : Certificate X U T)
    (h_le : ∀ x u t, σ₁.cert x u t → σ₂.cert x u t) :
    ∀ x t, admissibleSet σ₁ x t ⊆ admissibleSet σ₂ x t := by
  intro x t u hu
  exact h_le x u t hu

/-! ## §9. Théorèmes de cohérence doctrinale -/

/-- **Non-interférence avec l'autorisation**.

    Formellement : il n'existe aucune entrée (x, u, t) telle que
    K^FCI puisse mettre du poids sur u sans que u soit admissible
    ou u = u⊥.

    C'est la version support-level du théorème `checker_never_forces_allow`
    de ModThirtyChecker. -/
theorem gate_never_forces_allow {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) (u : U)
    (h_in_supp : u ∈ gatedKernel K σ x t) :
    σ.cert x u t ∨ u = u⊥ := by
  have h_subset := supp_gatedKernel_subset K σ x t h_in_supp
  rcases h_subset with h_adm | h_safe
  · left
    exact h_adm
  · right
    exact Set.mem_singleton_iff.mp h_safe

/-- **Préservation de P1 (refuse-by-default)**.

    Si l'ensemble admissible est vide en (x, t), alors le noyau filtré
    place toute sa masse sur u⊥. -/
theorem empty_admissible_forces_safe {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T)
    (h_empty : admissibleSet σ x t = ∅) :
    gatedKernel K σ x t ⊆ {(u⊥ : U)} := by
  intro u hu
  have h := supp_gatedKernel_subset K σ x t hu
  rcases h with h_adm | h_safe
  · rw [h_empty] at h_adm
    exact False.elim (by simp at h_adm)
  · exact h_safe

/-! ## §10. Extensions & TODO

  Le raccord mesure-théorique support-level est porté par :
    FCI/CausalSupportMeasureBridge.lean

  Les futures extensions concernent :
    - une preuve Nagumo depuis les cônes tangents ;
    - une instance physique concrète ;
    - une reconstruction analytique complète restrict + dirac + support réel
      dans un bridge ultérieur, si Mathlib le permet.

  [TODO-V1] Remplacer `ViabilityStructure.nagumo_invariance` par une preuve
            depuis les cônes de Bouligand (Mathlib.Analysis.Calculus.TangentCone),
            si l'API Mathlib disponible devient suffisante.

  [TODO-S1] Spécialisation explicite : module FCI/CarmatInstance.lean qui
            instancie ce squelette pour CARMAT ou pour une autre cible
            physique contrôlée.

  [TODO-D1] Document de raccord avec le dossier FCI Partie V (P1–P5) :
            ce théorème est-il une preuve alternative de la suffisance de
            P1–P5, ou une preuve indépendante qui les renforce ?

  [DOCTRINE] Le générateur L_IA, la métrique de Fisher, le tenseur d'Amari-
             Chentsov et les connexions α-duales sont explicitement absents
             de ce module. C'est un choix doctrinal, pas un oubli.

-/

end CausalSupportImmunity
end FCI
