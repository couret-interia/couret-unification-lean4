/-
  CouretUnification.AnalyticHorizon.A8ArchimedeanCorrection
  ════════════════════════════════════════════════════════════════════
  Correction archimédienne typée attachée au résidu combinatoire A8.

  Ce fichier encode un petit résidu fini :
    K₇ possède C(7,2) = 21 arêtes,
    K₆ possède C(6,2) = 15 arêtes,
    la différence finie est donc 6.

  Interprétation doctrinale :
    les six arêtes de réflexion attachées au pôle 29 forment une
    « coquille » combinatoire de correction. Cette coquille est typée
    comme correction du côté de la formule explicite, mais aucun transport
    analytique n'est démontré ici.

  Garde-fous :
    • aucun transport de Sonine n'est prouvé ;
    • aucune origine KMS n'est prouvée ;
    • aucune conséquence RH n'est exportée ;
    • ce fichier encode seulement une correction finie typée.

  Statut :
    couche AnalyticHorizon ;
    résidu combinatoire fini fermé par `native_decide` ;
    interface de correction archimédienne, sans revendication globale.
-/

import Mathlib.Data.Finset.Powerset
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.AnalyticHorizon

open CouretUnification.Logic.ExplicitFormula

/-- Les six sommets actifs après retrait du pôle de réflexion 29. -/
def U30A8 : Finset ℕ :=
  [7, 11, 13, 17, 19, 23].toFinset

/-- Les six arêtes de réflexion attachées au pôle 29. -/
def ReflectionEdges : Finset (ℕ × ℕ) :=
  U30A8.image fun x => (x, 29)

/-- Cardinalité de la coquille de réflexion. -/
theorem reflectionEdges_card_eq_6 :
    ReflectionEdges.card = 6 := by
  native_decide

/-- Nombre brut d'arêtes dans K₇. -/
def M4_raw : ℕ := Nat.choose 7 2

/-- Nombre effectif d'arêtes dans K₆. -/
def M4_eff : ℕ := Nat.choose 6 2

/-- Résidu A8. -/
def R_A8 : ℕ := M4_raw - M4_eff

/-- Le résidu combinatoire fini vaut six. -/
theorem R_A8_eq_6 : R_A8 = 6 := by
  native_decide

/--
Correction typée attachée au résidu A8.

Aucun transport de Sonine n'est prouvé ici.
Aucune origine KMS n'est prouvée ici.
Aucune conséquence RH n'est exportée.
-/
structure A8ArchimedeanCorrection where
  correctionSide : FormulaSide
  residueCard : ℕ
  residueCard_eq_six : residueCard = 6
  no_rh_claim : True

end CouretUnification.AnalyticHorizon
