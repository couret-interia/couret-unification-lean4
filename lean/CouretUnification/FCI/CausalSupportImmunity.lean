/-
================================================================================
  FCI/CausalSupportImmunity.lean
================================================================================
  Programme Couret-Unification · Couche FCI (théorème central abstrait)
  Cible : Lean 4.30.0-rc1 / Mathlib4 (tag récent)

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

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

open scoped MeasureTheory
open MeasureTheory Set

namespace FCI
namespace CausalSupportImmunity

/-! ## §1. Types abstraits

On modélise les espaces d'état physique `X`, d'action `U`, et de temps `T`
comme des espaces mesurables génériques. La théorie est entièrement abstraite.
-/

variable (X U T : Type*)
variable [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace T]

/-- Action sûre par défaut (fail-close).
    C'est le `u⊥` du formalisme, point distingué de l'espace d'action. -/
class HasSafeAction (U : Type*) where
  safe : U

notation "u⊥" => HasSafeAction.safe

/-! ## §2. Politique candidate K_θ

Une politique candidate est un noyau de Markov de `X × T` vers `U`.
Sa source mathématique (générateur L_IA, variété statistique, etc.) est
HORS-CHAMP par construction : on ne suppose RIEN sur sa structure interne.
-/

/-- Noyau de Markov : pour chaque (x, t), une mesure de probabilité sur U.
    On utilise `Measure U` ici plutôt qu'une `kernel` formelle de Mathlib pour
    garder le squelette lisible. -/
structure CandidatePolicy where
  kernel : X → T → Measure U
  isProbability : ∀ x t, IsProbabilityMeasure (kernel x t)

/-! ## §3. Certificat σ et admissibilité

Le certificat est un prédicat décidable sur (x, u, t).
La décidabilité est ESSENTIELLE pour la doctrine FCI : un certificat
non décidable ne peut pas être implémenté en O(1) dans le bloc D du
pipeline EADX, donc viole P4 (WCET).
-/

/-- Certificat de permission. Décidable par construction.
    Le paramètre `π` (PolicyPack) est implicite dans le prédicat. -/
structure Certificate where
  cert : X → U → T → Prop
  decidable : ∀ x u t, Decidable (cert x u t)

attribute [instance] Certificate.decidable

variable {X U T}

/-- Ensemble admissible local : actions certifiées en (x, t). -/
def admissibleSet (σ : Certificate X U T) (x : X) (t : T) : Set U :=
  {u | σ.cert x u t}

/-- L'ensemble admissible est mesurable (sous hypothèse de mesurabilité du
    certificat). Cette hypothèse est tracée plutôt qu'assumée silencieusement. -/
class CertMeasurable (σ : Certificate X U T) : Prop where
  measurable : ∀ x t, MeasurableSet (admissibleSet σ x t)

/-! ## §4. Gate filtré K_θ^FCI

Définition centrale du noyau filtré FCI :

    K^FCI(B | x, t) = K(B ∩ A_σ(x,t) | x, t)
                    + (1 - K(A_σ(x,t) | x, t)) · 𝟙_B(u⊥)

Cette construction garantit deux propriétés cruciales :
  (1) K^FCI reste une mesure de probabilité (masse totale = 1)
  (2) supp K^FCI ⊆ A_σ(x,t) ∪ {u⊥}  (théorème central §5)
-/

variable [HasSafeAction U]

/-- Noyau filtré FCI. Construction explicite.

    Note : on utilise `Measure.restrict` pour la partie admissible et un Dirac
    pondéré pour la masse rejetée vers u⊥. -/
noncomputable def gatedKernel
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) : Measure U :=
  let admissible := admissibleSet σ x t
  let Z := (K.kernel x t) admissible      -- masse admissible Z_σπ(x,t)
  let restricted := (K.kernel x t).restrict admissible
  let safeMass := (1 - Z) • Measure.dirac (u⊥ : U)
  restricted + safeMass

/-- Le noyau filtré est une mesure de probabilité (masse totale = 1).

    Preuve laissée en sorry technique : nécessite manipulation des sommes de
    mesures et du fait que `Z + (1 - Z) = 1`. Standard mais pas trivial. -/
theorem gatedKernel_isProbability
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    IsProbabilityMeasure (gatedKernel K σ x t) := by
  sorry  -- [TODO-T1] Standard : Measure.add_apply + restrict_apply + dirac_apply

/-! ## §5. Théorème central : restriction du support

C'est LE théorème de la doctrine FCI :
le support causal de l'image physique est inclus dans l'admissible ∪ {u⊥}.
-/

/-- **Théorème central de restriction du support causal**.

    Pour tout générateur cognitif (peu importe sa nature : L_IA, gradient
    naturel, géodésique sur variété de Fisher, modèle stochastique...),
    le support du noyau filtré est inclus dans l'admissible ∪ {u⊥}.

    Mathématiquement :
      ∀ K, supp(K^FCI(· | x, t)) ⊆ admissibleSet σ x t ∪ {u⊥}

    Doctrinalement :
      « L'IA peut générer hors sûreté ; le monde ne reçoit jamais hors sûreté. »
-/
theorem supp_gatedKernel_subset
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    (gatedKernel K σ x t).support ⊆ admissibleSet σ x t ∪ {u⊥} := by
  sorry  -- [TODO-T2] Décomposition restricted + dirac.
         -- supp(restricted) ⊆ admissibleSet par def de restrict
         -- supp(safeMass) ⊆ {u⊥} par def du dirac
         -- supp(somme) ⊆ union des supports.

/-! ## §6. Viabilité : interface abstraite (Nagumo)

On axiomatise la condition de Nagumo plutôt que de la prouver depuis les
cônes tangents de Bouligand : ce serait un travail Mathlib indépendant
substantiel. Les hypothèses sont rendues EXPLICITES, jamais cachées.
-/

variable {X}

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
def viableActions
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
theorem fci_immunity
    [TopologicalSpace X]
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
    (h_action_in_supp : ∀ t, u t ∈ (gatedKernel K σ (φ t) t).support)
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
    rw [Set.mem_singleton_iff] at h_safe
    rw [h_safe]
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
theorem fci_immunity_monotone
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

    C'est la version mesurable du théorème `checker_never_forces_allow`
    de ModThirtyChecker. -/
theorem gate_never_forces_allow
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) (u : U)
    (h_in_supp : u ∈ (gatedKernel K σ x t).support) :
    σ.cert x u t ∨ u = u⊥ := by
  have h_subset := supp_gatedKernel_subset K σ x t h_in_supp
  rcases h_subset with h_adm | h_safe
  · left; exact h_adm
  · right; exact Set.mem_singleton_iff.mp h_safe

/-- **Préservation de P1 (refuse-by-default)**.

    Si l'ensemble admissible est vide en (x, t), alors le noyau filtré
    place toute sa masse sur u⊥. -/
theorem empty_admissible_forces_safe
    (K : CandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T)
    (h_empty : admissibleSet σ x t = ∅) :
    (gatedKernel K σ x t).support ⊆ {(u⊥ : U)} := by
  intro u hu
  have h := supp_gatedKernel_subset K σ x t hu
  rcases h with h_adm | h_safe
  · exfalso
    rw [h_empty] at h_adm
    exact h_adm
  · exact h_safe

/-! ## §10. TODO post-rédaction

  [TODO-T1] gatedKernel_isProbability : preuve technique standard via
            Measure.add_apply + restrict_apply + dirac_apply. ~30 lignes.

  [TODO-T2] supp_gatedKernel_subset : décomposition support de somme,
            support de restrict, support de dirac. ~50 lignes.
            C'est le COEUR technique du module.

  [TODO-V1] Remplacer `ViabilityStructure.nagumo_invariance` par une preuve
            depuis les cônes de Bouligand (Mathlib.Analysis.Calculus.TangentCone).
            Travail substantiel : cf. Aubin-Cellina "Differential Inclusions"
            chapitre 4.

  [TODO-S1] Spécialisation explicite : module FCI/CarmatInstance.lean qui
            instancie ce squelette pour CARMAT (X = état hémodynamique,
            U = commandes pompe, S = enveloppe physiologique).

  [TODO-D1] Document de raccord avec le dossier FCI Partie V (P1–P5) :
            ce théorème est-il une preuve ALTERNATIVE de la suffisance de
            P1–P5, ou une preuve INDÉPENDANTE qui les renforce ?
            À discuter avec Thomas/Riposo avant intégration.

  [DOCTRINE] Le générateur L_IA, la métrique de Fisher, le tenseur d'Amari-
             Chentsov, les connexions α-duales : tout ce matériel est
             EXPLICITEMENT ABSENT de ce module. C'est un choix doctrinal,
             pas un oubli. La preuve d'immunité ne dépend pas de la nature
             du décideur surveillé. Toute tentative d'introduire L_IA dans
             ce fichier doit être refusée comme sur-claim.

-/

end CausalSupportImmunity
end FCI
