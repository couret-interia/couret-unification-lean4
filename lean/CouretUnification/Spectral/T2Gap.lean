import CouretUnification.Spectral.FiniteCore
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CouretUnification.T2Gap

open FiniteCore

/-!
# T2Gap

Ce fichier empaquette l’inégalité coercive du noyau fini dans la formulation
abstraite `HasTargetGap` utilisée par la couche T2.

Route logique :
1. définir le secteur coercif (`CoerciveSector`) ;
2. définir les données canoniques (`canonicalT2Data`) ;
3. exprimer le trou cible comme proposition abstraite (`HasTargetGap`) ;
4. montrer que cette proposition est équivalente à une borne concrète sur le secteur ;
5. importer la borne inférieure du noyau fini et conclure `HasTargetGap`.
-/

/-!
## 1. Secteur coercif
-/

/-- Secteur coercif : vecteurs centrés orthogonaux à `altVec`. -/
def CoerciveSector : Type :=
  { x : Centered8 // GoodSubspace x }

namespace CoerciveSector

/-- Vecteur centré sous-jacent. -/
def val (x : CoerciveSector) : Centered8 := x.1

/-- Norme au carré héritée de `Centered8`. -/
def normSq (x : CoerciveSector) : ℝ := x.1.normSq

/-- Énergie induite par la forme quadratique du noyau fini. -/
def energy (x : CoerciveSector) : ℝ := quadratic x.1.1

theorem normSq_nonneg (x : CoerciveSector) : 0 ≤ x.normSq := by
  exact x.1.normSq_nonneg

end CoerciveSector

/-!
## 2. Données T2 canoniques
-/

/-- Constante de trou formelle conservée comme constante cible du programme Couret. -/
def kappa : ℝ := 2

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  norm_num

/-- Enveloppe minimale de données T2 pour l’étape légère. -/
structure T2Data where
  Q : CoerciveSector → ℝ
  κ : ℝ
  κ_pos : 0 < κ

/-- Données d’énergie canoniques induites par le noyau fini. -/
def canonicalT2Data : T2Data :=
  { Q := CoerciveSector.energy
    κ := kappa
    κ_pos := kappa_pos }

/-- Énoncé générique de trou attaché à un paquet `T2Data`. -/
def GapStatementFor (T : T2Data) : Prop :=
  ∀ x : CoerciveSector, T.κ * x.normSq ≤ T.Q x

theorem canonical_gap_statement_def :
    GapStatementFor canonicalT2Data =
      ∀ x : CoerciveSector, kappa * x.normSq ≤ x.energy := by
  rfl

/-!
## 3. Proposition cible abstraite
-/

/-- Prédicat abstrait de trou coercif sur le secteur courant. -/
def HasAbstractGap (κ : ℝ) : Prop :=
  ∀ x : CoerciveSector, κ * x.normSq ≤ x.energy

/-- Énoncé coercif cible pour le programme. -/
def HasTargetGap : Prop :=
  HasAbstractGap kappa

theorem HasTargetGap_def :
    HasTargetGap = HasAbstractGap kappa := by
  rfl

theorem energy_def_on_sector (x : CoerciveSector) :
    CoerciveSector.energy x = quadratic x.1.1 := by
  rfl

theorem normSq_def_on_sector (x : CoerciveSector) :
    CoerciveSector.normSq x = x.1.normSq := by
  rfl

theorem canonicalT2Data_Q (x : CoerciveSector) :
    canonicalT2Data.Q x = CoerciveSector.energy x := by
  rfl

theorem canonicalT2Data_kappa :
    canonicalT2Data.κ = kappa := by
  rfl

/-!
## 4. Empaquetage optionnel d’un objet de preuve
-/

structure GapData where
  proof : HasTargetGap

def HasCanonicalGapData : Prop := Nonempty GapData

theorem HasCanonicalGapData_def :
    HasCanonicalGapData ↔ Nonempty GapData := by
  rfl

theorem gapData_implies_target (h : GapData) : HasTargetGap := by
  exact h.proof

def mkGapData (h : HasTargetGap) : GapData := ⟨h⟩

theorem mkGapData_spec (h : HasTargetGap) :
    (mkGapData h).proof = h := by
  rfl

theorem target_of_canonical_gap (h : HasCanonicalGapData) : HasTargetGap := by
  rcases h with ⟨g⟩
  exact gapData_implies_target g

theorem canonicalGapData_of_targetGap (h : HasTargetGap) :
    HasCanonicalGapData := by
  exact ⟨mkGapData h⟩

/-!
## 5. Équivalences entre formulations
-/

theorem hasTargetGap_iff_canonicalGapStatement :
    HasTargetGap ↔ GapStatementFor canonicalT2Data := by
  rfl

theorem canonical_gap_statement_explicit :
    GapStatementFor canonicalT2Data ↔
      ∀ x : CoerciveSector, 2 * x.normSq ≤ x.energy := by
  rw [canonical_gap_statement_def]
  rfl

/-- Les vecteurs du secteur sont orthogonaux à `altVec` par construction. -/
theorem dot_altVec_zero_of_sector (x : CoerciveSector) :
    dot x.1.1 altVec = 0 := by
  exact (goodSubspace_iff_dot_altVec_zero x.1).1 x.2

/-- Un énoncé de trou canonique fournit la borne inférieure concrète sur chaque vecteur du secteur. -/
theorem canonical_gap_statement_on_sector (x : CoerciveSector) :
    GapStatementFor canonicalT2Data →
    2 * x.normSq ≤ quadratic x.1.1 := by
  intro h
  have hx : 2 * x.normSq ≤ x.energy := by
    exact (canonical_gap_statement_explicit.mp h) x
  simpa [normSq_def_on_sector, energy_def_on_sector] using hx

/-- Réciproquement, une borne inférieure concrète sur le secteur fournit l’énoncé de trou canonique. -/
theorem canonical_gap_statement_of_sector_bound
    (h : ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1) :
    GapStatementFor canonicalT2Data := by
  rw [canonical_gap_statement_explicit]
  intro x
  simpa [normSq_def_on_sector, energy_def_on_sector] using h x

/-- Équivalence principale entre l’énoncé de trou canonique et la borne explicite sur le secteur. -/
theorem canonical_gap_statement_iff_sector_bound :
    GapStatementFor canonicalT2Data ↔
      ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1 := by
  constructor
  · intro h x
    exact canonical_gap_statement_on_sector x h
  · intro h
    exact canonical_gap_statement_of_sector_bound h

/-- Reformulation de `HasTargetGap` comme inégalité explicite sur le secteur. -/
theorem hasTargetGap_iff_sector_bound :
    HasTargetGap ↔ ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1 := by
  rw [hasTargetGap_iff_canonicalGapStatement]
  exact canonical_gap_statement_iff_sector_bound

/-- Même reformulation cible, écrite sous la forme exacte souvent utilisée comme objectif. -/
theorem sector_bound_goal_form :
    HasTargetGap ↔
      ∀ x : CoerciveSector, 2 * x.1.normSq ≤ quadratic x.1.1 := by
  simpa using hasTargetGap_iff_sector_bound

/-!
## 6. Import depuis `FiniteCore`
-/

/-- Inégalité coercive du noyau fini, transportée vers le secteur coercif. -/
theorem quadratic_lower_bound_on_sector (x : CoerciveSector) :
    2 * x.normSq ≤ quadratic x.1.1 := by
  simpa using quadratic_lower_bound_on_goodSubspace x.1 x.2

/-- Le trou cible est prouvé par la borne inférieure du noyau fini. -/
theorem hasTargetGap_proved : HasTargetGap := by
  rw [hasTargetGap_iff_sector_bound]
  intro x
  simpa using quadratic_lower_bound_on_sector x

/-- Pont final exporté du noyau fini vers la cible abstraite T2. -/
theorem hasTargetGap_from_finiteCore :
  HasTargetGap := hasTargetGap_proved

/-!
## Trou coercif exact (exporté depuis le noyau fini)
-/

/-- Trou coercif exact en κ = 2, hérité du noyau fini. -/
theorem exact_coercive_gap_kappa_two :
    HasTargetGap := by
  exact hasTargetGap_from_finiteCore

/-- Inégalité coercive explicite sur le secteur. -/
theorem exact_coercive_gap_kappa_two_explicit :
    ∀ x : CoerciveSector, 2 * x.normSq ≤ x.energy := by
  intro x
  exact (canonical_gap_statement_explicit.mp exact_coercive_gap_kappa_two) x

end CouretUnification.T2Gap
