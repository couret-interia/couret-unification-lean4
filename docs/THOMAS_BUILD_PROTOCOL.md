# Protocole Thomas — validation v37 locale

**Programme Couret–Unification · v37**
**Destinataire : Thomas (compilation Lean)**
**Auteur : Alexandre Couret**

---

## Objet

Ce protocole valide les pièces v37 actuellement prêtes :

1. doctrine épistémique ;
2. Ticket 1 : résidu de clôture `ρ(TC) = {19}` ;
3. Ticket 2 : orientation Cycle/Coset ;
4. audit agrégé v37.

Il **ne vise pas encore** `UnitsBridge.lean`, `Isospectrality.lean`,
ni le pont Hilbert–Pólya.

**Doctrine centrale rappelée :**

```text
truth status ≠ architectural position
[P] local ≠ Frozen Core automatically
Residue/* remains Active unless explicitly bridged
RHClaimed = false
```

---

## Précondition — environnement

Depuis la racine du dépôt :

```bash
pwd
cat lean-toolchain
lake --version
lake env lean --version
```

Copier les sorties dans le journal de build et les renvoyer
(cf. section *Sortie attendue à renvoyer*).

Cette étape est **importante** : elle nous dira pour la première
fois la version exacte de Lean et de Mathlib utilisées, ce qui
conditionne toutes les décisions techniques pour la suite
(notamment `UnitsBridge.lean`).

---

## Étape 1 — Doctrine

```bash
lake env lean lean/CouretUnification/EpistemicDiscipline/DoctrinalInvariants.lean
```

**Succès attendu :** aucune erreur, aucun warning bloquant.

**Interprétation :**

```text
[P-doctrine]
RHClaimed=false
[P] local does not imply Frozen Core
Residue remains Active
```

**Note :** ce fichier ne dépend d'aucun import Mathlib. S'il
échoue, le problème est dans le Lean core ou la configuration
du dépôt — pas dans Mathlib.

---

## Étape 2 — Ticket 1 : `ClosureTC`

```bash
lake env lean lean/CouretUnification/Residue/ClosureTC.lean
```

**Succès attendu :** aucune erreur.

**Interprétation :**

```text
Ticket 1 closed locally:
ρ(TC) = {19}
Status: [P-Lean] local + Active architectural
```

**Échec possible — points à vérifier :**

- syntaxe `Finset` literal `{1, 11, 29}` : si problème,
  remplacer par `({1, 11, 29} : Finset Z30)` avec annotation
  de type explicite ;
- timeout de `decide` sur `closure_TC_eq_K4` : remplacer par
  `native_decide` ;
- `S ×ˢ S` : si non reconnu, remplacer par `Finset.product S S` ;
- `Nat.rec` : syntaxe standard, devrait être stable.

Si erreur : envoyer le message d'erreur exact (copier-coller
intégral, pas paraphrase).

---

## Étape 3 — Ticket 2 : `CycleCoset`

```bash
lake env lean lean/CouretUnification/Residue/CycleCoset.lean
```

**Précondition :** `ClosureTC.lean` doit avoir compilé d'abord
(dépendance `import CouretUnification.Residue.ClosureTC`).

**Succès attendu :** aucune erreur.

**Interprétation :**

```text
Ticket 2 closed locally:
TC = {1} ∪ (K4 ∩ Coset)
Status: [P-Lean] local + Active architectural
```

**Échec possible — points à vérifier :**

- ordre interne des éléments dans les littéraux `Finset` (variable
  selon les versions de Mathlib) : si une égalité échoue par
  `rfl`, basculer vers `decide` ou `Finset.ext` ;
- `Disjoint Cycle Coset` : si `decide` ne ferme pas, essayer
  `Finset.disjoint_iff_inter_eq_empty.mpr (by decide)`.

Pas de problème RH/HP attendu à cette étape.

---

## Étape 4 — Audit v37 agrégé

```bash
bash scripts/audit_v37_aggregation.sh
```

**Succès attendu :**

```text
[v37 audit] PASS: all available gates passed
[v37 audit] Frozen Core, AnalyticHorizon, and Release remain
[v37 audit] architecturally independent from Residue
[v37 audit] RHClaimed=false preserved
```

**Note :** beaucoup de gates seront marqués `SKIP` (Norwich,
audits v36 hérités) si les scripts correspondants ne sont pas
encore présents dans le dépôt. Ce n'est pas un échec — l'audit
v37 a été conçu pour tolérer l'absence de pièces et ne fait
échouer que sur les pièces présentes en erreur.

---

## Grille d'interprétation

| Résultat | Lecture correcte |
|---|---|
| `DoctrinalInvariants.lean` compile | La doctrine v37 est encodée et vérifiable |
| `ClosureTC.lean` compile | Ticket 1 fermé localement |
| `CycleCoset.lean` compile | Ticket 2 fermé localement |
| Audit `PASS` | Pas de fuite architecturale détectée |
| Un fichier `Residue/*` échoue | **Erreur technique locale**, pas échec doctrinal |
| Audit `FAIL` | Corriger l'import interdit ou le drapeau doctrinal |
| Tous passent | Ouvrir ensuite `UnitsBridge.lean` |

---

## Ce que ce protocole NE prouve PAS

Ce protocole **ne prouve pas** :

- l'isospectralité complète des triplets amputés ;
- la diagonalisation par caractères ;
- le pont $\det_2 \leftrightarrow \xi$ ;
- l'hypothèse de Riemann ;
- une compromission cryptographique.

Il prouve seulement que **les deux premiers tickets locaux et la
doctrine v37 sont cohérents dans l'environnement Lean utilisé**.

C'est modeste. C'est suffisant pour cette étape.

---

## Sortie attendue à renvoyer

Format recommandé :

```text
=== Précondition ===
lean-toolchain:
<contenu>

lake --version:
<sortie>

lake env lean --version:
<sortie>

=== Étape 1 ===
DoctrinalInvariants:
PASS / FAIL
[si FAIL : message d'erreur exact]

=== Étape 2 ===
ClosureTC:
PASS / FAIL
[si FAIL : message d'erreur exact]

=== Étape 3 ===
CycleCoset:
PASS / FAIL
[si FAIL : message d'erreur exact]

=== Étape 4 ===
audit_v37_aggregation:
PASS / FAIL
[sortie complète de l'audit]
```

---

## Décision après retour

**Si les trois fichiers Lean et l'audit passent :**

> Ouvrir `Residue/UnitsBridge.lean`, ciblé sur la version Mathlib
> exacte révélée par la précondition.

**Si `ClosureTC` ou `CycleCoset` échoue :**

> Corriger localement avant toute complexité Units. Pas de
> complexification de l'architecture tant que le socle ne tient pas.

**Si l'audit échoue :**

> Corriger la juridiction avant toute suite mathématique. La
> discipline passe avant l'extension.

---

## Formule finale

> **Doctrine first.**
> **Local finite tickets second.**
> **Units bridge third.**
> **Spectrum last.**

---

*Pour Bernard Couret (1928–1999, Istres).*
