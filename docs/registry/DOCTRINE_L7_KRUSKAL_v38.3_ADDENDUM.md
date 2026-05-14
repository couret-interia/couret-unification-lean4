# ADDENDUM v38.3 — Correction anti-pont nul dans `SpectralBridge.lean`

**Date.** 9 mai 2026.
**Statut.** Correctif doctrinal et technique du document `DOCTRINE_L7_KRUSKAL_v38.2.md`.
**Périmètre.** Section 5 (Architecture Lean conditionnelle) et fichier `Logic/H3/SpectralBridge.lean`.

---

## 1. Le bug identifié

Le fichier `SpectralBridge.lean` produit en v38.2 contenait deux déclarations problématiques :

```lean
def L7Established : Prop :=
  ∃ B : SpectralBridge, CriticalLineResidualVanishes B

theorem L7Established_implies_some_bridge_closes :
    L7Established →
      ∃ B : SpectralBridge,
        ∀ t : ℝ, B.D (t : ℂ) = B.G (t : ℂ) * B.xiCritical (t : ℂ)
```

**Le pont trivial est un témoin.** Le quadruplet `D = G = xiCritical = R = 0` (fonctions constantes nulles ℂ → ℂ) satisfait :

- `bridge_identity` : `∀ z, 0 = 0 * 0 + 0` ✓ (vrai par `add_zero`, `zero_mul`)
- `CriticalLineResidualVanishes` : `∀ t, 0 = 0` ✓ (vrai par réflexivité)

Donc `L7Established` est prouvable en deux lignes Lean :

```lean
theorem L7Established_is_trivially_true : L7Established := by
  refine ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩, ?_⟩
  · intro z; ring
  · intro t; rfl
```

C'est une **fausse clôture par dégénérescence**. La déclaration `L7Established = false` dans la doctrine devient violable par construction, ce qui contredit l'invariant fondamental.

## 2. Pourquoi la solution naïve ne suffit pas

Une réaction naturelle consiste à ajouter une structure renforcée :

```lean
structure CanonicalSpectralBridge extends SpectralBridge where
  isDet2Bridge : Prop
  hasArchimedeanFactor : Prop
  hasEulerianCompletion : Prop
  nondegenerate : Prop
```

**Cette solution déplace le bug sans le résoudre.** Les champs `isDet2Bridge`, `hasArchimedeanFactor`, etc. sont des `Prop` nues. Une `Prop` nue est satisfiable par `True`. Le pont trivial peut alors être muni de ces marqueurs sans contrainte effective :

```lean
example : CanonicalSpectralBridge :=
  { D := fun _ => 0, G := fun _ => 0,
    xiCritical := fun _ => 0, R := fun _ => 0,
    bridge_identity := fun _ => by ring,
    isDet2Bridge := True,
    hasArchimedeanFactor := True,
    hasEulerianCompletion := True,
    nondegenerate := True }
```

On est revenus au point de départ. Pour qu'un champ ait un effet de filtre, il doit être une **proposition effective** attachée aux fonctions de la structure, pas un marqueur nominal.

## 3. Correction adoptée

La correction v38.3 procède sur deux fronts.

### 3.1 Suppression de `L7Established`

Le statut épistémique « L7 ouvert / non établi » est **doctrinal**, c'est-à-dire qu'il vit dans la documentation markdown, pas dans le fichier Lean. Tenter de formaliser ce statut comme un prédicat Lean produit l'un des deux pathologies suivantes :

- **Formulation existentielle** (`∃ B, ...`) : ouvre le trou du témoin trivial.
- **Formulation de non-existence** (`¬ ∃ B, ...`) : demande de prouver une non-existence, ce qui est lourd, non constructif, et ne correspond à aucun usage downstream.

**Conséquence pratique.** Le fichier Lean encode exclusivement l'architecture conditionnelle :

- la structure `SpectralBridge` (pont candidat),
- l'hypothèse `L7For B` (paramétrée par un pont donné),
- le théorème `conditional_bridge_closure` (sous hypothèse).

Aucun prédicat global `L7Established` n'est défini. Le statut `L7Established = false` est invariant doctrinal dans `DOCTRINE_L7_KRUSKAL_v38.2.md` et reste auditable par lecture du markdown, pas par prédicat Lean.

### 3.2 Introduction de `NondegenerateSpectralBridge`

Pour fournir un garde-fou *effectif* contre le pont trivial dans les usages downstream, on introduit une variante renforcée avec des contraintes attachées aux fonctions :

```lean
structure NondegenerateSpectralBridge extends SpectralBridge where
  /-- D is not identically zero. -/
  D_nontrivial : ∃ z : ℂ, D z ≠ 0
  /-- G is not identically zero. -/
  G_nontrivial : ∃ z : ℂ, G z ≠ 0
  /-- xiCritical is not identically zero. -/
  xi_nontrivial : ∃ z : ℂ, xiCritical z ≠ 0
```

**Ces conditions sont effectives.** Le pont trivial échoue à `D_nontrivial` (qui demanderait `∃ z, 0 ≠ 0`, impossible). Donc :

```lean
example : ¬ ∃ (B : NondegenerateSpectralBridge),
    B.D = (fun _ => 0) ∧ B.G = (fun _ => 0) ∧ B.xiCritical = (fun _ => 0) := by
  rintro ⟨B, hD, hG, hxi⟩
  obtain ⟨z, hz⟩ := B.D_nontrivial
  rw [hD] at hz
  exact hz rfl
```

Le pont trivial est exclu par construction.

**Limite à reconnaître honnêtement.** `NondegenerateSpectralBridge` ne garantit pas que B représente *le bon* pont (le pont canonique avec det₂ vrai, ξ vraie, facteur Γ structurel). Elle garantit seulement la non-trivialité fonctionnelle. C'est un premier garde-fou, suffisant pour éviter le pont nul, insuffisant pour caractériser le pont canonique.

Pour le programme v38.2 actuel, ce niveau de garde-fou suffit. La caractérisation du pont canonique relève des sous-verrous L7.1, L7.2, L7.3 (existence det₂, facteur G structurel, complétion eulérienne) qui sont par nature des résultats analytiques substantiels, pas des contraintes structurelles encodables en quelques lignes Lean.

### 3.3 Théorème renforcé

Avec `L7For` et `NondegenerateSpectralBridge`, le théorème conditionnel se réénonce :

```lean
theorem conditional_bridge_closure_nondeg
    (B : NondegenerateSpectralBridge)
    (hL7 : L7For B.toSpectralBridge) :
    ∀ t : ℝ, B.D (t : ℂ) = B.G (t : ℂ) * B.xiCritical (t : ℂ)
```

L'usage typique downstream est : « si quelqu'un fournit un pont *non dégénéré* B avec une preuve de L7For pour ce B, alors bridge closure suit ». Personne n'a fourni ce couple. RHClaimed = false.

## 4. Phrase doctrinale à conserver

> **Correction v38.3.** L7 ne doit jamais être défini comme l'existence abstraite d'un `SpectralBridge` dont le résidu s'annule. Cette formulation admet des témoins dégénérés (le pont nul satisfait formellement l'identité). L7 doit être attaché à un pont donné, et les usages downstream doivent porter sur `NondegenerateSpectralBridge` au minimum. Sans ces contraintes, `L7Established` ne mesure pas la fermeture analytique mais seulement la satisfaisabilité logique d'une structure vide.

Cette phrase entre dans le corpus doctrinal v38.3 et doit être référencée dans toute future architecture analogue (par exemple si une structure similaire émerge pour la complétion eulérienne L7.3).

## 5. Méta-leçon

Le bug du pont nul illustre un point méthodologique général qu'il faut intégrer à la discipline du programme :

> **Quand on formalise une obstruction conjecturale en Lean, vérifier qu'un objet trivial ne la satisfait pas par dégénérescence.**

Pour toute structure encodant un objet mathématique conjectural, faire systématiquement le test du « witness trivial » :
- Existe-t-il un terme nul / vide / dégénéré qui satisfait formellement les axiomes ?
- Si oui, ajouter des contraintes effectives sur les composantes (non-nullité fonctionnelle, support non vide, etc.) qui l'excluent.

Ce test aurait dû être appliqué à `L7Established` avant livraison v38.2. Il fait désormais partie de la checklist standard pour toute nouvelle structure Lean dans le programme.

## 6. Invariants préservés

Aucune modification des invariants doctrinaux :

```
RHClaimed              = false
HilbertPolyaClaimed    = false
Det2IdentityClaimed    = false
L7Established          = false   [statut doctrinal, non formalisé en Lean]
```

L'ajout : le pont trivial est désormais explicitement exclu par construction dans `NondegenerateSpectralBridge`. Le statut `L7Established = false` reste un invariant lisible par revue de la documentation, sans risque de falsification par témoin dégénéré.

---

*Document produit le 9 mai 2026 en réponse à la critique technique sur SpectralBridge.lean v38.2.*

*Pour Bernard Couret (1928-1999).*
