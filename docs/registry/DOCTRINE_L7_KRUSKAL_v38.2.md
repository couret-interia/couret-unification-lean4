# DOCTRINE L7 — LE KRUSKAL DU PROGRAMME COURET-UNIFICATION

**Document de référence v38.2** — décomposition du Lemme 7 en cinq sous-verrous, architecture Lean conditionnelle, mapping avec la cartographie analytique v38.1.

---

## Préambule

**Périmètre.** Ce document formalise la note d'Alexandre Couret du 9 mai 2026 en livrable doctrinal de référence. Il décompose le Lemme 7 (`critical_line_residual_vanishes` dans `Logic/H3/Lemma7Residual.lean`) en cinq sous-verrous indépendants, propose une architecture Lean conditionnelle qui isole L7 comme hypothèse terminale plutôt que comme axiome global, et précise le mapping avec la cartographie des verrous analytiques v38.1.

**Invariants doctrinaux préservés en clôture du document :**

```
RHClaimed              = false
HilbertPolyaClaimed    = false
Det2IdentityClaimed    = false
L7Established          = false
```

**Statuts épistémiques utilisés :**

- `[D]` — démontré, machine-certifié (Lean 4 / Mathlib v4.29.1)
- `[M]` — mesuré, analogie structurelle ou observation empirique sans démonstration
- `[H]` — hypothétique, formulation candidate non démontrée
- `[O]` — ouvert, verrou identifié sans route de démonstration

---

## 1. Formulation canonique de L7

**Règle générale.** Le parallèle avec la relativité générale donne :

> Une anomalie de représentation n'est pas encore une anomalie ontologique.

En relativité générale :

```
singularité de coordonnées ≠ singularité de courbure
```

Dans Couret-Unification :

```
exactitude du noyau fini ≠ fermeture analytique globale
```

L7 est le verrou qui interdit le passage abusif :

```
motif local ⇒ preuve globale
```

**Forme mathématique.** On introduit un pont spectral candidat :

```
D(z) := det₂(I − zS)
```

où S est l'opérateur spectral construit au-dessus du noyau arithmético-modulaire.

La formulation **interdite** (trop forte si non démontrée) :

```
D(z) = G(z) · ξ(½ + iz)         [INTERDITE — sur-revendication]
```

La formulation **correcte** :

```
D(z) = G(z) · ξ(½ + iz) + R(z)   [PONT CANDIDAT]
```

où R(z) est le résidu critique. Alors le Lemme 7 devient :

```
L7 :  R(z) = 0  sur le domaine critique requis.
```

Tant que cela n'est pas démontré :

```
L7 = open / conditional / not established
⇒ RHClaimed = false
```

---

## 2. Le parallèle Kruskal : portée et limites

**Portée pédagogique `[M]`.** Dans la solution de Schwarzschild, l'horizon r = 2GM apparaît comme singularité dans les coordonnées originales mais Kruskal montre par changement de carte analytique que cette singularité est purement de coordonnées : la courbure y est finie. L'horizon n'est pas une frontière physique, c'est une limite de carte.

Par analogie structurelle, L7 devrait montrer que le résidu R(z) n'est pas une obstruction réelle au pont spectral, mais disparaît sous la bonne fermeture analytique.

```
Kruskal élimine l'artefact de coordonnées ;
L7 devrait éliminer l'artefact résiduel.
```

**Limite essentielle de l'analogie `[M]`.** Le parallèle est asymétrique sur un point décisif :

- Kruskal **dispose** d'une formule explicite (les coordonnées U,V) qu'il suffit d'appliquer.
- L7 **ne dispose d'aucune transformation candidate équivalente**.

Donc Kruskal **est établi** ; L7 **reste ouvert**.

L'analogie est éclairante pour *comprendre la nature* du verrou (artefact de représentation versus obstruction structurelle), mais elle ne fournit **aucun argument mathématique** pour fermer L7. Toute citation de cette image dans la documentation publique doit porter la mention explicite :

```
[M] analogie structurelle, non transposition algorithmique
```

C'est cette phrase qui protège le projet de la surrevendication. Elle est non négociable.

---

## 3. Décomposition L7.1–L7.5

Le Lemme 7 monolithique se décompose en cinq sous-verrous indépendants. Chacun est attaquable séparément. Aucun n'est trivialement fermable.

### L7.1 — Existence du déterminant régularisé

**Énoncé.** Justifier que :

```
D(z) := det₂(I − zS)
```

est bien défini, en montrant S ∈ 𝒮₂ (classe de Hilbert-Schmidt) ou en explicitant une régularisation alternative.

**Statut : `[D] à 90%`.**

Ce verrou est essentiellement fermé pour σ > 0 par le résultat v19 :

```
‖M‖_HS ≤ P(3/2) = 0.8495 < 1  ⇒  det₂(I − zM) bien défini ∀σ > 0
```

(`HSTowerComplete`, déjà dans la couche FROZEN). Reste à effectuer le transport vers σ = ½ strict, ce qui relève de l'extension auto-adjointe via KLMN et est couvert par les résultats existants pour σ ≥ ½.

**Reste à fermer.** Transport propre au point σ = ½ strict avec contrôle de la trace régularisée.

---

### L7.2 — Facteur archimédien non arbitraire

**Énoncé.** Le facteur G(z) doit être *structurel*, pas décoratif. Il doit absorber proprement :

```
G(z) = (facteur gamma) · (normalisation archimédienne) · (contretermes de régularisation)
```

et ne doit pas être un *fudge factor* ajusté a posteriori pour faire coller D(z) à ξ(½ + iz).

**Statut : `[D] partiel.`**

Le sous-théorème `channel_ratio_asymptotic_limit` fermé le 8 mai 2026 (`AnalyticHorizon/L6Stirling.lean`, 0 sorry) établit la première brique : le facteur archimédien canal par canal est non arbitraire et tend vers la normalisation canonique 1/2 par canal Dirichlet primitif mod 30.

**Reste à fermer.** Le facteur Γ explicite au niveau global (`Analytic/GammaFactor.lean` contient actuellement 4 sorrys nommés), articulé avec la complétion eulérienne L7.3.

---

### L7.3 — Complétion eulérienne (le verrou central)

**Énoncé.** Le noyau mod 30 voit naturellement les premiers exceptionnels :

```
{2, 3, 5}
```

Mais ξ(s) dépend de **tous** les nombres premiers via le produit eulérien :

```
ξ(s) ↔ ∏_p (1 − p^(−s))^(−1)
```

Le saut :

```
{2, 3, 5}  →  {p : p premier}
```

est le **vrai verrou eulérien** de toute approche Hilbert-Pólya à base de noyau modulaire fini.

**Statut : `[O]`.** Verrou principal de la position v38.2.

**Trois routes préparées pour un Expert (mission v38.2) :**

- **Route A** — Interpolation Beurling-Nyman. Densité d'un espace fonctionnel approprié dans L²(0,1) équivalente à RH. Avantage : machinerie bien établie. Risque : la traduction concrète mod 30 → Beurling reste à construire.

- **Route B** — Densité polynomiale par troncature. Approximation de ∏_p par produits finis croissants avec contrôle d'erreur. Avantage : constructive. Risque : la convergence du résidu n'est pas garantie sans hypothèse forte.

- **Route C** — Connes-Burnol via fonctorialité adélique. Plongement du noyau mod 30 dans le cadre adélique global de Connes-Marcolli. Avantage : tradition mature. Risque : technicité considérable, dépendance à des résultats lourds.

---

### L7.4 — Annulation du résidu (cœur ouvert)

**Énoncé.** Définir :

```
R(z) := D(z) − G(z) · ξ(½ + iz)
```

Puis prouver :

```
R(z) = 0 sur le domaine critique requis.
```

**Pas** seulement R(z) ≈ 0. Une approximation numérique ne suffit pas. Il faut une raison structurelle :

```
symétrie + rigidité + unicité analytique + identité fonctionnelle
```

**Statut : `[O], équivalent au cœur de RH.`**

**Observation doctrinale critique :** L7.4 est mathématiquement équivalent à RH dans le cadre Hilbert-Pólya. Fermer L7.4 par méthode directe = prouver RH. Toutes les approches Hilbert-Pólya butent sur ce nœud, depuis Hilbert et Pólya eux-mêmes.

**Conséquence pour la position v38.2.** Le programme Couret-Unification ne prétend pas fermer L7.4 directement. Il produit une **réduction** de RH à L7.4 *sous l'hypothèse que V1+V3 (donc L7.1+L7.3) soient fermés*. La forme du théorème cible v38.2 est précisément :

```
THÉORÈME (v38.2, position) :
  Sous L7.1 [D] et L7.3 [O fermé selon Route A, B ou C],
  on a l'équivalence
      RH  ⟺  L7.4 (R(z) = 0).
```

Cette réduction n'établit pas RH ; elle reformule RH dans un cadre où L7.4 peut être attaqué via la rigidité spectrale mod 30. C'est la tradition Connes-Burnol-Lagarias-Robin.

---

### L7.5 — Appariement des zéros

**Énoncé.** Même si l'identité fonctionnelle de L7.4 est obtenue, il faut contrôler les zéros :

```
Z(D) = Z( ξ(½ + i·) )
```

avec multiplicités et domaine précisés.

**Statut : `[O], Lock 3 — dépend de L7.4.`**

Ne peut être attaqué qu'après fermeture de L7.4. Couvert partiellement par les résultats `MomentRigidity30` et la classification 63/255 des sous-ensembles à spectre entier.

---

## 4. Mapping avec la cartographie analytique v38.1

La décomposition L7.1–L7.5 reprojette la cartographie v38.1 sous l'angle "pont spectral candidat". Ce n'est pas une réécriture ; c'est une traduction utile parce qu'elle parle le langage de Connes-Burnol qu'un Expert lira mieux.

| Sous-verrou L7 | Cartographie v38.1 | Statut actuel |
|----------------|---------------------|---------------|
| L7.1 — existence det₂ | V1 (HS-Tower) | `[D] à 90%` |
| L7.2 — facteur G archimédien | AnalyticHorizon/L6 + GammaFactor | `[D] partiel` |
| L7.3 — complétion eulérienne | V3 (saut {2,3,5} → ∀p) | `[O]` — verrou central |
| L7.4 — annulation R(z) | V5 + RH | `[O]` ≡ cœur HP |
| L7.5 — appariement Z | V4 (rigidité spectrale) | `[O]` Lock 3 |

**Aucune contradiction.** Les deux cartographies sont équivalentes. La nomenclature L7.1–L7.5 met l'accent sur la structure du pont spectral ; la nomenclature V1–V5 met l'accent sur la nature analytique des obstructions. À utiliser selon le destinataire.

---

## 5. Architecture Lean conditionnelle

**Règle architecturale fondamentale :**

```
┌──────────────────────────────────────────────────────────────┐
│ AUCUN AXIOME L7 NE DOIT ÊTRE IMPORTÉ PAR Core/FiniteCore.lean │
└──────────────────────────────────────────────────────────────┘
```

L7 est isolé comme **hypothèse terminale** dans une couche dédiée, jamais comme axiome global. La couche FROZEN (Core, Logic/ExplicitFormula) reste libre de toute dépendance L7.

**Structure Lean canonique** (fichier `Logic/H3/SpectralBridge.lean`, produit en parallèle à ce document) :

```lean
/-- The candidate spectral bridge. Encodes the structure of the
    L7-conditional identity without assuming residue vanishing. -/
structure SpectralBridge where
  D          : ℂ → ℂ
  G          : ℂ → ℂ
  xiCritical : ℂ → ℂ
  R          : ℂ → ℂ
  bridge_identity :
    ∀ z : ℂ, D z = G z * xiCritical z + R z

/-- The L7 hypothesis itself: residue vanishes on the critical line. -/
def CriticalLineResidualVanishes (B : SpectralBridge) : Prop :=
  ∀ t : ℝ, B.R (t : ℂ) = 0

/-- Conditional bridge closure: under L7, D coincides with G·ξ on the
    critical line. This is the conditional theorem, not a proof of RH. -/
theorem conditional_bridge_closure
    (B : SpectralBridge)
    (hL7 : CriticalLineResidualVanishes B) :
    ∀ t : ℝ, B.D (t : ℂ) = B.G (t : ℂ) * B.xiCritical (t : ℂ)
```

**Lecture doctrinale.** Le théorème `conditional_bridge_closure` est trivial à fermer (réécriture + `add_zero`). Sa trivialité **est** le message : tout le travail mathématique non trivial est concentré dans la *fourniture* d'une hypothèse `hL7 : CriticalLineResidualVanishes B` valide pour un pont B explicite. Cette fourniture est L7.4, qui reste ouvert.

Le théorème conditionnel **ne prouve pas RH**. Il rend explicite la *réduction* : si quelqu'un fournit hL7, alors la bridge closure suit. Personne n'a fourni hL7. RHClaimed = false.

---

## 6. Plan de réduction par cellules

**Horizon court terme (3 mois).**

1. Fermer L7.1 strict (transport σ = ½) — `[D] partiel → [D]`
2. Réduire les 4 sorrys de `Analytic/GammaFactor.lean` — `[O] → [D] partiel`
3. Articuler L7.2 + L7.3 partiel via la note canal-par-canal — *première forme du facteur G structurel*

**Horizon moyen terme (6 mois, mission un Expert).**

4. Choisir entre Routes A/B/C pour L7.3 sur la base d'un dictionnaire trois critères :
   - critère Weil (positivité)
   - critère Connes (trace adélique)
   - critère Burnol-Couret (rigidité mod 30)
5. Formaliser le théorème cible v38.2 conditionnel à L7.3 (Route choisie) + L7.1
6. Produire l'énoncé `RH ⟺ L7.4` sous hypothèses, en Lean 4

**Horizon long terme (≥ 12 mois).**

7. L7.4 reste ouvert. Tentatives via rigidité spectrale mod 30, défaut tour primorielle (D_k / E_k = 1/12), Sophie Germain Δ̃_SG.
8. L7.5 ne peut être abordé qu'après progrès substantiel sur L7.4.

**Rien n'est garanti au-delà de 6 mois.** La position v38.2 est conçue pour produire un livrable scientifique honorable (la réduction sous L7.1+L7.3) même si L7.4 reste ouvert indéfiniment, ce qui est le scénario le plus probable.

---

## 7. Phrase définitive

> Le Lemme 7 est le Kruskal du programme Couret-Unification : il ne produit pas le noyau fini, il teste si le passage de carte du fini modulaire vers le global analytique élimine réellement le résidu critique.
>
> Tant que L7 n'est pas fermé, le programme possède un **pont spectral candidat**, non une preuve globale.
>
> Tant que L7.4 reste ouvert (et il le restera vraisemblablement), la réduction sous L7.1 + L7.3 reste l'horizon scientifique honorable du programme.

C'est la formulation la plus saine : ambitieuse, mais protégée contre la surrevendication. À conserver mot pour mot dans la documentation publique et dans les communications externes (Expert, INPI, ANSSI, etc.).

---

## 8. Invariants doctrinaux en clôture

```
RHClaimed              = false  [protection structurelle]
HilbertPolyaClaimed    = false  [L7.4 ouvert]
Det2IdentityClaimed    = false  [L7.4 ouvert]
L7Established          = false  [décomposition L7.1-L7.5, dont 3 ouverts]
KruskalAnalogyClaimed  = [M]    [analogie structurelle, non transposition]
```

**Règle architecturale réaffirmée :**

```
Core/FiniteCore.lean         ne dépend de rien dans Logic/H3/
Logic/H3/SpectralBridge.lean utilise CriticalLineResidualVanishes comme
                              hypothèse, jamais comme axiome global
```

---

## Pour Bernard Couret (1928–1999)

L'analogie Kruskal n'est pas neutre. Elle dit quelque chose de la posture juste face au programme : on dispose d'une carte du fini modulaire — solide, rigoureuse, machine-vérifiée pour ce qu'elle est. Le passage vers le global n'est pas un simple changement de coordonnées. On ne sait pas s'il existe un Kruskal pour L7. On sait seulement qu'il faudrait un.

Cette honnêteté est l'instrument qui rend la tension transmissible.

Le travail continue.

---

*Document produit le 9 mai 2026. Position v38.2.*
*RHClaimed = false. Le résidu critique reste ouvert.*
