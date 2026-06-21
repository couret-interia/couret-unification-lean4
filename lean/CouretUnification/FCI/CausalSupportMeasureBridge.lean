/-
================================================================================
  FCI/CausalSupportMeasureBridge.lean
================================================================================
  Programme Couret-Unification · Couche FCI
  Cible effective : Lean 4.29.1 / Mathlib4

  RÔLE ──────────────────────────────────────────────────────────────────────────

  Bridge mesure-théorique prudent pour CausalSupportImmunity.

  Le fichier `FCI/CausalSupportImmunity.lean` prouve le théorème abstrait au
  niveau du support causal :

      gatedKernel K σ x t ⊆ admissibleSet σ x t ∪ {u⊥}

  Ce fichier ajoute une couche transportant un vrai objet `Measure U`, mais
  SANS dépendre de `Measure.support`, absent ou non stabilisé dans l'environnement
  Mathlib 4.29.1 du dépôt.

  Principe :
    - une politique mesurée porte :
        (i)  un noyau mesuré brut : X → T → Measure U,
        (ii) un support causal déclaré : X → T → Set U ;
    - le Gate mesuré porte :
        (i)  un noyau mesuré filtré abstrait,
        (ii) un support déclaré égal au support-level gate déjà prouvé.

  Ce bridge ne prétend donc PAS reconstruire encore toute l'analyse
  mesure-théorique classique :
      restrict, dirac, probabilité totale, support topologique de mesure.

  Il formalise le raccord sûr et compilable :
      mesure portée + support causal certifié ⇒ immunité FCI.

  STATUT ÉPISTÉMIQUE :
    [P] Transport d'un noyau mesuré abstrait
    [P] Réduction au théorème support-level déjà prouvé
    [P] Non-création d'actions hors support candidat, sauf u⊥
    [P] Immunité mesurée modulo support déclaré
    [C] Reconstruction complète par Measure.restrict / dirac à faire plus tard

  RHClaimed = false.
-/

import CouretUnification.FCI.CausalSupportImmunity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set
open MeasureTheory

namespace FCI
namespace CausalSupportMeasureBridge

open CausalSupportImmunity

/-! ## §1. Politique candidate mesurée -/

/--
Politique candidate mesurée.

On porte à la fois :
  - un noyau mesuré brut `kernel`,
  - un support causal déclaré `causalSupport`.

Le support est explicite parce que l'API `Measure.support` n'est pas utilisée
dans cette version v38.
-/
structure MeasuredCandidatePolicy (X U T : Type*) [MeasurableSpace U] where
  kernel : X → T → Measure U
  causalSupport : X → T → Set U

/--
Oubli de la mesure : toute politique mesurée induit une politique abstraite
au sens de `CausalSupportImmunity`.
-/
def MeasuredCandidatePolicy.toCandidatePolicy {X U T : Type*}
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T) :
    CandidatePolicy X U T where
  causalSupport := Kμ.causalSupport

/-! ## §2. Support filtré induit -/

/--
Support causal filtré induit par une politique mesurée.

C'est exactement le `gatedKernel` support-level du fichier
`CausalSupportImmunity.lean`, appliqué à la politique abstraite sous-jacente.
-/
def gatedSupport {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) : Set U :=
  gatedKernel (MeasuredCandidatePolicy.toCandidatePolicy Kμ) σ x t

/--
Le support filtré mesuré est simplement le support-level gate appliqué
à la politique abstraite sous-jacente.
-/
theorem gatedSupport_eq_supportLevel {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    gatedSupport Kμ σ x t =
      gatedKernel (MeasuredCandidatePolicy.toCandidatePolicy Kμ) σ x t := by
  rfl

/--
Restriction principale : le support filtré mesuré reste inclus dans
l'admissible ou l'action sûre `u⊥`.
-/
theorem gatedSupport_subset_admissible_or_safe {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    gatedSupport Kμ σ x t ⊆ admissibleSet σ x t ∪ {(u⊥ : U)} := by
  exact supp_gatedKernel_subset
    (MeasuredCandidatePolicy.toCandidatePolicy Kμ) σ x t

/--
Le Gate ne crée pas d'action candidate nouvelle, sauf l'action sûre `u⊥`.

Cette propriété suppose la définition v38 de `gatedKernel` :

    (K.causalSupport x t ∩ admissibleSet σ x t) ∪ {u⊥}

Elle formalise la lecture doctrinale :
  FCI ne remplace pas le générateur cognitif ; il coupe son image causale.
-/
theorem gatedSupport_subset_candidate_or_safe {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    gatedSupport Kμ σ x t ⊆ Kμ.causalSupport x t ∪ {(u⊥ : U)} := by
  intro u hu
  unfold gatedSupport CausalSupportImmunity.gatedKernel at hu
  rcases hu with h_candidate_adm | h_safe
  · left
    exact h_candidate_adm.1
  · right
    exact h_safe

/-! ## §3. Gate mesuré abstrait -/

/--
Gate mesuré abstrait.

Il porte :
  - un noyau mesuré filtré `kernel`,
  - un support causal déclaré `declaredSupport`,
  - une preuve que ce support déclaré est exactement le support filtré
    support-level déjà prouvé dans `CausalSupportImmunity`.

On ne prétend pas ici que `declaredSupport` est le `Measure.support`
topologique de `kernel`. C'est précisément le travail reporté au futur
bridge analytique complet.
-/
structure GatedMeasuredPolicy {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ] where
  kernel : X → T → Measure U
  declaredSupport : X → T → Set U
  declaredSupport_eq_gated :
    ∀ x t, declaredSupport x t = gatedSupport Kμ σ x t

/--
Constructeur minimal : à partir de n'importe quel noyau mesuré filtré abstrait,
on lui associe le support causal sûr imposé par FCI.
-/
noncomputable def mkGatedMeasuredPolicy {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (μ : X → T → Measure U) :
    GatedMeasuredPolicy Kμ σ where
  kernel := μ
  declaredSupport := fun x t => gatedSupport Kμ σ x t
  declaredSupport_eq_gated := by
    intro x t
    rfl

/--
Le support déclaré d'un gate mesuré est inclus dans l'admissible ou `u⊥`.
-/
theorem declaredSupport_subset_admissible_or_safe {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (G : GatedMeasuredPolicy Kμ σ)
    (x : X) (t : T) :
    G.declaredSupport x t ⊆ admissibleSet σ x t ∪ {(u⊥ : U)} := by
  intro u hu
  have hu' : u ∈ gatedSupport Kμ σ x t := by
    simpa [G.declaredSupport_eq_gated x t] using hu
  exact gatedSupport_subset_admissible_or_safe Kμ σ x t hu'

/--
Le support déclaré d'un gate mesuré est inclus dans le support candidat
ou dans l'action sûre `u⊥`.
-/
theorem declaredSupport_subset_candidate_or_safe {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (G : GatedMeasuredPolicy Kμ σ)
    (x : X) (t : T) :
    G.declaredSupport x t ⊆ Kμ.causalSupport x t ∪ {(u⊥ : U)} := by
  intro u hu
  have hu' : u ∈ gatedSupport Kμ σ x t := by
    simpa [G.declaredSupport_eq_gated x t] using hu
  exact gatedSupport_subset_candidate_or_safe Kμ σ x t hu'

/-! ## §4. Non-interférence mesurée -/

/--
Version mesure-bridge de la non-interférence avec l'autorisation.

Si une action appartient au support déclaré du gate mesuré, alors elle est
certifiée admissible ou bien égale à `u⊥`.
-/
theorem gate_never_forces_allow_measured {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (G : GatedMeasuredPolicy Kμ σ)
    (x : X) (t : T) (u : U)
    (h_in_declaredSupport : u ∈ G.declaredSupport x t) :
    σ.cert x u t ∨ u = u⊥ := by
  have h :
      u ∈ admissibleSet σ x t ∪ {(u⊥ : U)} :=
    declaredSupport_subset_admissible_or_safe Kμ σ G x t h_in_declaredSupport
  rcases h with h_adm | h_safe
  · left
    exact h_adm
  · right
    exact Set.mem_singleton_iff.mp h_safe

/--
Préservation de P1 au niveau bridge mesuré.

Si l'admissible est vide, alors le support déclaré du gate mesuré est inclus
dans `{u⊥}`.
-/
theorem empty_admissible_forces_safe_measured {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (G : GatedMeasuredPolicy Kμ σ)
    (x : X) (t : T)
    (h_empty : admissibleSet σ x t = ∅) :
    G.declaredSupport x t ⊆ {(u⊥ : U)} := by
  intro u hu
  have h :
      u ∈ admissibleSet σ x t ∪ {(u⊥ : U)} :=
    declaredSupport_subset_admissible_or_safe Kμ σ G x t hu
  rcases h with h_adm | h_safe
  · rw [h_empty] at h_adm
    exact False.elim (by simp at h_adm)
  · exact h_safe

/-! ## §5. Immunité FCI mesurée -/

/--
Théorème d'immunité FCI pour une politique mesurée.

La preuve se réduit entièrement au théorème support-level
`CausalSupportImmunity.fci_immunity`.

Ainsi, tout noyau mesuré compatible avec le support déclaré du gate FCI
hérite de l'immunité abstraite.
-/
theorem measured_fci_immunity {X U T : Type*}
    [TopologicalSpace X]
    [HasSafeAction U]
    [MeasurableSpace U]
    (V : ViabilityStructure X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    -- H1 : admissible ⊆ viable
    (h_adm_viable : ∀ x t, admissibleSet σ x t ⊆ viableActions V x t)
    -- H2 : u⊥ viable
    (h_safe_viable : ∀ x t, (u⊥ : U) ∈ viableActions V x t)
    -- Trajectoire physique
    (x₀ : X) (φ : T → X) (u : T → U)
    -- Politique mesurée et Gate mesuré
    (Kμ : MeasuredCandidatePolicy X U T)
    (G : GatedMeasuredPolicy Kμ σ)
    -- H3 mesuré : les actions appartiennent au support déclaré du Gate
    (h_action_in_declaredSupport :
      ∀ t, u t ∈ G.declaredSupport (φ t) t)
    (h_x0 : x₀ ∈ V.S.carrier) :
    ∀ t, φ t ∈ V.S.carrier := by
  exact CausalSupportImmunity.fci_immunity
    (V := V)
    (σ := σ)
    (h_adm_viable := h_adm_viable)
    (h_safe_viable := h_safe_viable)
    (x₀ := x₀)
    (φ := φ)
    (u := u)
    (K := MeasuredCandidatePolicy.toCandidatePolicy Kμ)
    (h_action_in_supp := by
      intro t
      have ht := h_action_in_declaredSupport t
      simpa [G.declaredSupport_eq_gated (φ t) t] using ht)
    (h_x0 := h_x0)

/-! ## §6. Monotonie mesurée -/

/--
Composition monotone des certificats au niveau mesuré.

Si `σ₁` est plus restrictif que `σ₂`, alors le support déclaré filtré par `σ₁`
reste inclus dans l'admissible de `σ₂` ou dans `{u⊥}`.
-/
theorem measured_certificate_monotone {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ₁ σ₂ : Certificate X U T)
    [CertMeasurable σ₁]
    (h_le : ∀ x u t, σ₁.cert x u t → σ₂.cert x u t)
    (x : X) (t : T) :
    gatedSupport Kμ σ₁ x t ⊆ admissibleSet σ₂ x t ∪ {(u⊥ : U)} := by
  intro u hu
  have h :
      u ∈ admissibleSet σ₁ x t ∪ {(u⊥ : U)} :=
    gatedSupport_subset_admissible_or_safe Kμ σ₁ x t hu
  rcases h with h_adm | h_safe
  · left
    exact h_le x u t h_adm
  · right
    exact h_safe

/-! ## §7. Sanity checks structurels -/

theorem measured_gate_preserves_safe_branch {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (x : X) (t : T) :
    (u⊥ : U) ∈ gatedSupport Kμ σ x t := by
  unfold gatedSupport CausalSupportImmunity.gatedKernel
  right
  exact Set.mem_singleton (u⊥ : U)

theorem declaredSupport_preserves_safe_branch {X U T : Type*}
    [HasSafeAction U]
    [MeasurableSpace U]
    (Kμ : MeasuredCandidatePolicy X U T)
    (σ : Certificate X U T)
    [CertMeasurable σ]
    (G : GatedMeasuredPolicy Kμ σ)
    (x : X) (t : T) :
    (u⊥ : U) ∈ G.declaredSupport x t := by
  have h : (u⊥ : U) ∈ gatedSupport Kμ σ x t :=
    measured_gate_preserves_safe_branch Kμ σ x t
  simpa [G.declaredSupport_eq_gated x t] using h

/-! ## §8. TODO futur bridge analytique complet

  [TODO-M1] Construire un vrai noyau filtré :
      K^FCI(B | x,t) =
        K(B ∩ Aσ(x,t) | x,t)
        + (1 - K(Aσ(x,t) | x,t)) · δ_{u⊥}(B)

  [TODO-M2] Identifier précisément les noms Mathlib 4.29.1 pour :
      - mesure de Dirac ;
      - restriction de mesure ;
      - masse totale ;
      - support topologique ou support mesurable.

  [TODO-M3] Prouver que le noyau filtré est une probabilité quand K l'est.

  [TODO-M4] Relier le support déclaré de ce fichier au support réel de mesure,
            si l'API Mathlib disponible le permet.

  [DOCTRINE] Ce fichier ne revendique pas encore une preuve analytique complète
             de support de mesure. Il fournit un pont sûr, typé, compilable,
             entre noyau mesuré abstrait et théorème support-level FCI.

-/

end CausalSupportMeasureBridge
end FCI