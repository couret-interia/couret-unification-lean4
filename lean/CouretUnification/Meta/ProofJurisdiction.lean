/-
  Couret-Unification — v35.9-pre
  Meta/ProofJurisdiction.lean

  Objet : juridiction de preuve. Formalise la règle FCI :

           No Certificate  ⇒  No Claim.

  Statut     : Frozen-eligible (0 sorry, structures + théorèmes triviaux)
  Layer      : Meta (no upstream dependency in CouretUnification)
  Doctrine   : carte de promotion Active → Frozen
  RHClaimed              : false (vérifié par frozen_no_rh_claim)
  HilbertPolyaClaimed    : false (vérifié par frozen_no_hp_claim)
  PhysicalClaimed        : false (vérifié par frozen_no_physical_claim)
  sorryCount             : 0

  Règle architecturale stricte :
    Aucun fichier Frozen ne peut promouvoir un claim sans avoir produit,
    et instancié sans sorry, un certificat satisfaisant `admissibleToFrozen`.

    L'invariant de promotion porte sur cinq champs simultanés :
      (1) statut proved ou definitionalClosed ;
      (2) zéro sorry ;
      (3) RHClaimed = false ;
      (4) HilbertPolyaClaimed = false ;
      (5) PhysicalClaimed = false.

    La rupture d'un seul de ces invariants suffit à inhiber la promotion.

  Pour Bernard.
-/

namespace CouretUnification.Meta

/- ═══════════════════════════════════════════════════════════════════════════
   STATUT D'UN CLAIM
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Statut épistémique d'un claim dans le programme.

    `proved`              : preuve Lean complète, 0 sorry, sans axiome local non autorisé.
    `definitionalClosed`  : structure typée close par construction, sans contenu analytique caché.
    `conditional`         : preuve dépend d'obligations typées explicites.
    `specOnly`            : spécification seule (pas d'implémentation).
    `openProblem`         : verrou identifié, route à explorer.
    `falsified`           : claim réfuté (preuve d'impossibilité ou contre-exemple).
    `retiredArtifact`     : route éliminée, archivée pour traçabilité historique.
-/
inductive ClaimStatus where
  | proved
  | definitionalClosed
  | conditional
  | specOnly
  | openProblem
  | falsified
  | retiredArtifact
deriving DecidableEq, Repr

/- ═══════════════════════════════════════════════════════════════════════════
   CLAIMGATE : LE PORTAIL DE PROMOTION
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Un `ClaimGate` est l'objet typé qui circule entre Active et Frozen.

    Tout claim que le programme veut promouvoir vers Frozen doit être
    décrit par une instance de `ClaimGate`. Les cinq booléens
    (`rhClaimed`, `hpClaimed`, `physicalClaimed`) et le compteur
    `sorryCount` sont les *invariants doctrinaux* du dépôt.

    Important : `rhClaimed`, `hpClaimed`, `physicalClaimed` sont des
    `Bool` plutôt que des `Prop` parce qu'ils sont *vérifiables au
    type-check par décidabilité*. C'est ce qui permet à `frozen_no_*_claim`
    d'être prouvé sans aucune inspection de contenu mathématique. -/
structure ClaimGate where
  name             : String
  status           : ClaimStatus
  sorryCount       : Nat
  rhClaimed        : Bool
  hpClaimed        : Bool
  physicalClaimed  : Bool

/- ═══════════════════════════════════════════════════════════════════════════
   ADMISSIBILITÉ DE PROMOTION
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Conjonction des cinq invariants requis pour qu'un claim entre dans Frozen.

    L'ordre des conjonctions est canonique : il est utilisé par les
    théorèmes `frozen_no_*_claim` pour extraire les composantes par
    projection. Ne pas réordonner sans propager. -/
def admissibleToFrozen (c : ClaimGate) : Prop :=
  (c.status = ClaimStatus.proved ∨ c.status = ClaimStatus.definitionalClosed)
  ∧ c.sorryCount = 0
  ∧ c.rhClaimed = false
  ∧ c.hpClaimed = false
  ∧ c.physicalClaimed = false

/-- Statut d'un claim conditionnellement admis dans Active mais sans
    revendication finale. Ces claims peuvent dépendre de Frozen mais
    Frozen ne peut jamais dépendre d'eux. -/
def activeButNotClaimed (c : ClaimGate) : Prop :=
  c.status = ClaimStatus.conditional
  ∨ c.status = ClaimStatus.specOnly
  ∨ c.status = ClaimStatus.openProblem

/-- Statut d'un claim inhibé : ne peut être promu sous aucune condition. -/
def inhibited (c : ClaimGate) : Prop :=
  c.status = ClaimStatus.falsified
  ∨ c.status = ClaimStatus.retiredArtifact

/- ═══════════════════════════════════════════════════════════════════════════
   THÉORÈMES DE JURIDICTION (les trois verrous doctrinaux)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Tout claim admis dans Frozen vérifie `RHClaimed = false`. -/
theorem frozen_no_rh_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.rhClaimed = false := by
  exact h.2.2.1

/-- Tout claim admis dans Frozen vérifie `HilbertPolyaClaimed = false`. -/
theorem frozen_no_hp_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.hpClaimed = false := by
  exact h.2.2.2.1

/-- Tout claim admis dans Frozen vérifie `PhysicalClaimed = false`. -/
theorem frozen_no_physical_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.physicalClaimed = false := by
  exact h.2.2.2.2

/-- Tout claim admis dans Frozen a un compteur de sorry nul. -/
theorem frozen_zero_sorry
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.sorryCount = 0 := by
  exact h.2.1

/-- Un claim inhibé ne peut jamais être admis dans Frozen.

    La preuve repose sur le fait que `falsified` et `retiredArtifact`
    sont distincts de `proved` et `definitionalClosed`. -/
theorem inhibited_not_admissible
    (c : ClaimGate) (h : inhibited c) :
    ¬ admissibleToFrozen c := by
  intro hadm
  rcases h with hf | hr
  · -- falsified
    rcases hadm.1 with hp | hd
    · rw [hf] at hp; cases hp
    · rw [hf] at hd; cases hd
  · -- retiredArtifact
    rcases hadm.1 with hp | hd
    · rw [hr] at hp; cases hp
    · rw [hr] at hd; cases hd

/- ═══════════════════════════════════════════════════════════════════════════
   MAXIME DOCTRINALE
   ═══════════════════════════════════════════════════════════════════════════

   FCI ne prouve pas RH ;
   FCI rend impossible de revendiquer RH sans le certificat spectral complet.

   Version positive :
   notre architecture Lean devient un Gate du plan critique :
   le possible analytique est admis seulement s'il devient
   spectre auto-adjoint certifié.

   Voir Logic/H3/HPCertificate.lean pour la liste exhaustive des
   sept obligations qui composent le certificat HP, et
   Logic/ExplicitFormula/ExplicitFormulaBridge.lean pour le miroir
   arithmético-spectral.
-/

end CouretUnification.Meta
