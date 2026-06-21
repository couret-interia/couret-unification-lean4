# DOCTRINE — `FiniteCore` vs `Core`

**Document architectural de référence v38.5**
**Pour Thomas (développement Lean 4 / Mathlib v4.29.1)**
**Date : 9 mai 2026**

---

## Préambule pour Thomas

Ce document existe pour répondre à une question concrète que tu te poses (ou vas te poser) à chaque livraison de fichier Lean nouveau :

> *« Où je place ce fichier dans l'arborescence ? Est-ce que c'est du `Core/`, et si oui, est-ce que c'est du `FiniteCore` strict ? »*

La distinction `FiniteCore` vs `Core` n'est pas cosmétique. Elle gouverne :

- **où** un fichier est placé dans l'arborescence,
- **quels imports** il a le droit d'avoir,
- **quels théorèmes downstream** peuvent en dépendre,
- **quel niveau d'audit** il subit avant intégration,
- **quelle gravité** prend une régression sur ce fichier.

Ce document fixe les règles. Il est destiné à être lu une fois, gardé en référence, et appliqué mécaniquement.
Si une question architecturale se pose à toi en cours de session, **commence par chercher la réponse ici avant de me demander**.
Si la réponse n'y est pas, c'est probablement le signe qu'il faut étendre la doctrine, et on le fait ensemble.

Le document complète les règles déjà établies :

- **v36** (héritée) — séparation FROZEN/ACTIVE, aucun axiom global dans le noyau fini.
- **v38.3** — règle anti-Prop-nue (bug `L7Established`).
- **v38.5** — règle anti-True-énoncé (bug `signedTrace_spec : True`) + règle anti-sorry-sur-constante (bug `MertensConstant := sorry`).
- **v38.5** (ce document) — distinction `FiniteCore` strict vs `Core` étendu.

Toutes ces règles forment ensemble la **discipline architecturale** du programme. Elle est cumulative, jamais relâchée.

---

## 1. Les trois couches du projet

Le projet Couret-Unification se structure en trois couches doctrinales, qui correspondent à trois niveaux d'auditabilité :

### 1.1 FROZEN — couche machine-certifiée

C'est tout ce qui est dans `CouretUnification/Core/`. Caractéristiques :

- aucun `sorry` dans le code (les commentaires explicatifs peuvent mentionner le mot, mais aucune déclaration ne l'utilise comme habitant),
- aucun `axiom` introduit dans le code,
- aucune dépendance, directe ou transitive, à un module ACTIVE,
- contenu non-conditionnel par nature (pas paramétré sur une hypothèse externe à fournir).

Un théorème final qui passe `#print axioms` propre (uniquement `propext, Classical.choice, Quot.sound`) **et**
qui ne fait appel qu'à des modules FROZEN est dans le régime d'audit le plus fort.

### 1.2 ACTIVE — couche conditionnelle ou en cours

Tout ce qui est dans `CouretUnification/Logic/`, `CouretUnification/AnalyticHorizon/`, `CouretUnification/ResGold/` (sous-modules), et
autres dossiers de travail. Caractéristiques :

- peut contenir des `sorry` annotés `[D, provable]`, `[H]`, `[O]`, etc.,
- peut être paramétré sur des hypothèses externes (pattern `L7For B`, pattern `A_asymptotic_param mc h_mertens`),
- dépend potentiellement de FROZEN, mais FROZEN ne dépend jamais de ACTIVE.

ACTIVE n'est pas un défaut. C'est l'endroit où le travail se fait. La règle est juste
qu'**aucune chose ACTIVE ne descend dans FROZEN sans franchir une procédure d'admission** (cf. §7).

### 1.3 Q — quarantaine doctrinale (hors Lean)

Documents markdown classifiés `[Q]` (cf. `DOCTRINE_v38.4-Q_QUARANTAINE_PRODUCTIVE.md`). N'a pas de représentation en Lean. Ne nous concerne pas ici.

---

## 2. La granulation interne du FROZEN

À l'intérieur de FROZEN, le projet distingue **deux sous-couches** :

### 2.1 `FiniteCore` strict — le noyau Bernard

C'est le sous-ensemble de `Core/` qui porte spécifiquement sur la combinatoire arithmétique finie mod 30 et ses extensions primorielles.
C'est l'héritage direct des manuscrits de Bernard Couret (1928–1999), formalisé en Lean.

`FiniteCore` contient typiquement :

- la structure de `(ℤ/30ℤ)^×` avec ses 8 classes unitaires,
- les tables de Hecke T₂ sur ces classes,
- le tower lift primoriel (30 → 210 → 2310 → 30030),
- la fonction ε₃₀ (capture diagonale/minorante),
- la classification 63/255 des sous-ensembles à spectre entier,
- les invariants finis décidables par `native_decide`.

### 2.2 `Core` étendu — tout le reste de FROZEN

Le `Core/` au sens large contient tous les fichiers machine-certifiés qui ne sont pas dans `FiniteCore` strict. Typiquement :

- théorèmes sur les caractères de Dirichlet généraux (premier `p` arbitraire, pas mod 30),
- lemmes d'analyse réelle élémentaire,
- théorèmes de transport entre couches,
- invariants doctrinaux universels (`Status`, `RHClaimed`, `gate0_principle`).

Le contenu de `Core` étendu reste machine-certifié et non-conditionnel, mais il *peut* s'appuyer sur
des instruments de preuve plus généraux que ce que Bernard aurait pu vérifier à la main.

### 2.3 Pourquoi cette distinction

Trois raisons substantielles :

**Première raison — protection de l'héritage Bernard.**

`FiniteCore` est la couche qui doit pouvoir être lue par un mathématicien classique avec les manuscrits de Bernard sous
les yeux, sans demander de Lean spécifique ni de Mathlib avancé.
C'est le pivot transmissible. Si on diluait `FiniteCore` en y mettant des choses analytiques (même `[D]`),
on perdrait cette qualité de *carte combinatoire pure*.

C'est le critère **Bernard-readable** : ce qui est dans `FiniteCore` doit pouvoir, en principe, être vérifié à la main par
un mathématicien ayant les bases d'arithmétique élémentaire.
Lean ne fait qu'industrialiser la vérification ; il ne remplace pas la possibilité de la vérification humaine.

**Deuxième raison — discipline anti-contamination.**

La règle v38.3 *« aucun axiome L7 ne doit être importé par `Core/FiniteCore.lean` »* est doctrinale forte.
Si on étendait cette règle au `Core/` entier, on s'interdirait des théorèmes de transport intermédiaires qui
 sont parfaitement légitimes en `[D]` mais qui dépendent d'instruments analytiques généraux
 (par exemple, Stirling pour la fonction Gamma).

La distinction `FiniteCore` strict vs `Core/` large permet d'avoir les deux régimes simultanément :

- `FiniteCore` : Bernard-readable, contamination zéro tolérée,
- `Core/` étendu : machine-certifié, contamination par instruments généraux acceptable.

**Troisième raison — audit doctrinal granulé.**

Quand on fait `#print axioms` sur un théorème final, on veut pouvoir distinguer :

- les théorèmes qui s'appuient *uniquement* sur `FiniteCore` (statut d'audit le plus fort, vérifiable par Bernard-compatible),
- les théorèmes qui s'appuient sur `Core/` étendu (statut fort mais avec instruments généraux Mathlib),
- les théorèmes qui s'appuient sur `Logic/` ou `AnalyticHorizon/` (statut conditionnel).

La granulation FiniteCore / Core permet à un lecteur externe (INPI, ANSSI, relecteur académique) de calibrer son niveau de confiance selon ce qui est utilisé.

---

## 3. Critères d'admission `FiniteCore`

Trois tests, à appliquer **dans l'ordre**. Trois oui consécutifs → admission. Sinon → `Core/` étendu ou ACTIVE.

### 3.1 Test arithmétique mod 30

> *Le contenu central du fichier porte-t-il spécifiquement sur la structure mod 30, ou sur ses extensions primorielles (210, 2310, 30030, ...) ?*

**Oui si** : le fichier travaille sur `ZMod 30`, `ZMod 210`, `ZMod 2310`, sur les classes mod 30,
sur les caractères de `(ℤ/30ℤ)^×`, sur Hecke T₂ entre ces classes, sur ε₃₀, sur le tower lift primoriel, etc.

**Non si** : le fichier travaille sur `ZMod p` pour `p` premier *arbitraire*, ou sur des objets analytiques, ou sur des structures qui ne sont pas spécifiquement mod 30.

### 3.2 Test combinatoire fini

> *Tout dans le fichier est-il décidable par `native_decide`, prouvable par calcul fini explicite, ou par enumération d'un ensemble fini ?*

**Oui si** : tous les théorèmes du fichier sont soit des `native_decide`, soit des preuves combinatoires finies
(sommation sur `Finset.univ`, énumération de cas, transitivité de relations entre objets finis).

**Non si** : le fichier utilise des limites, des séries infinies, des intégrales, des objets analytiques (continuité, dérivabilité), même si chaque pas est `[D]`.

### 3.3 Test Bernard-readable

> *Un mathématicien classique avec les manuscrits de Bernard sous les yeux pourrait-il, en principe, vérifier le contenu sans Lean ni machine ?*

**Oui si** : les énoncés sont des affirmations arithmétiques finies que Bernard aurait pu écrire dans ses cahiers,
et les preuves sont des chaînes d'observations vérifiables (avec patience) à la main.

**Non si** : la preuve requiert des outils que Bernard n'aurait pas pu maîtriser
(par exemple, des théorèmes d'analyse complexe, des estimations asymptotiques fines, des structures de Mathlib spécifiques).

### 3.4 Exemples positifs (admissibles `FiniteCore`)

- `SophieGermainTowerLift.lean` (chaîne 3 → 15 → 135 → 1485, classes admissibles mod M par crible) — ✓ trois tests passent.
- `Mod30Structure.lean` (les 8 classes unitaires mod 30) — ✓ trois tests passent.
- `HeckeT2Table.lean` (table de transition T₂ sur les classes mod 30) — ✓ trois tests passent.
- `Epsilon30.lean` (capture diagonale/minorante) — ✓ trois tests passent, sous discipline nomenclaturale v38.4-Q (pas d'identification avec Kolyvagin etc.).
- `CayleyG30.lean` (structure de groupe sur les classes) — ✓ trois tests passent, *à condition que les sorries actuels soient fermés*.

### 3.5 Exemples négatifs (non admissibles `FiniteCore`)

- `L6Stirling.lean` (ratio R_χ(T) → 1/2) — ✗ analytique, échoue test 2.
- `L0_LocalLemma.lean` (caractères Dirichlet sur ZMod p pour p arbitraire) — ✗ pas spécifiquement mod 30, échoue test 1.
- `L1_ConductorOne.lean` (opérateur conducteur 1 spectre) — ✗ même raison.
- `Status.lean` (invariants doctrinaux universels) — ✗ doctrinal, pas arithmétique mod 30.
- `SpectralBridge.lean` (pont conditionnel L7) — ✗ doublement non admissible : structure conditionnelle, et pas mod 30 spécifique.

---

## 4. Critères d'admission `Core/` étendu

Moins strict que `FiniteCore`, plus strict que ACTIVE. Quatre tests, **tous nécessaires** :

### 4.1 Zéro sorry effectif

> *Le fichier ne contient aucun `sorry` dans une déclaration (def, theorem, lemma, instance, ...).*

Les mentions de `sorry` dans les commentaires explicatifs sont autorisées
(le mot peut apparaître dans une docstring qui *explique* la doctrine).
Mais aucune déclaration ne doit avoir `sorry` comme habitant.

**Procédure de vérification** :

```bash
grep -E "^([^-]|[^ ]-[^ -])*sorry" ResGold/L0_LocalLemma.lean
```

(la regex évite de matcher les `-- sorry` en commentaire) — doit retourner vide.

### 4.2 Zéro axiom

> *Le fichier ne contient aucun `axiom` (en tête de ligne ou indenté).*

Procédure :

```bash
grep -nE "^[[:space:]]*axiom[[:space:]]" ResGold/L0_LocalLemma.lean
```

Doit retourner vide. Les mentions dans les commentaires sont OK.

### 4.3 Zéro dépendance ACTIVE

> *Aucun `import` du fichier ne pointe vers un module ACTIVE.*

À vérifier par audit des `import` du fichier. Un fichier `Core/X.lean` ne peut importer que :
- d'autres fichiers `Core/`,
- des modules Mathlib v4.29.1.

Aucun `import CouretUnification.Logic.*`, `import CouretUnification.AnalyticHorizon.*`, `import CouretUnification.ResGold.*` (si ResGold est en ACTIVE).

### 4.4 Non-conditionnel intrinsèque

> *Aucun théorème principal du fichier n'est de la forme paramétrique `(h : SomeHypothesis) → Conclusion` où `h` représente une assomption mathématique externe.*

Cette règle est nuancée. Sont **admissibles dans Core** :

- théorèmes de la forme `∀ p [Fact p.Prime], ...` (la prémisse est une *qualité structurelle* de l'objet, pas une hypothèse mathématique externe),
- théorèmes de la forme `∀ a ∈ S, ...` (quantification universelle ordinaire),
- théorèmes de la forme `0 < p → ...` (hypothèse structurelle élémentaire).

Sont **non admissibles dans Core** :

- théorèmes de la forme `(hL7 : L7For B) → Conclusion` (paramétrique sur une hypothèse mathématique non démontrée),
- théorèmes de la forme `(h_mertens : Tendsto ... ) → Conclusion` (paramétrique sur une asymptotique non démontrée),
- théorèmes de la forme `(hRH : RH) → Conclusion` (paramétrique sur RH lui-même).

Ces théorèmes paramétriques **sont** précieux — ils encodent des réductions doctrinalement importantes
— mais ils restent en ACTIVE. Leur place est dans `Logic/H3/SpectralBridge.lean` ou `ResGold/MertensAsymptotic.lean`, pas dans `Core/`.

### 4.5 Test additionnel — règles anti-trivialité

Tous les fichiers Core doivent **également** respecter les règles v38.3 et v38.5 :

- **Anti-Prop-nue** : pas de `Prop` nues comme champs de structure (constraints effectives obligatoires).
- **Anti-True-énoncé** : pas de `theorem foo : True := ...` qui masque l'absence d'énoncé réel.
- **Anti-sorry-sur-constante** : pas de `noncomputable def k : ℝ := sorry` qui produit un terme fantôme.

Voir `RESGOLD_CORRECTIONS_v38.5_NOTE.md` pour la formulation complète de ces règles.

---

## 5. Arborescence cible

L'arborescence recommandée du projet, sous la doctrine v38.5 :

```
lean/CouretUnification/
│
├── Core/                              ── FROZEN (machine-certifié)
│   │
│   ├── FiniteCore/                    ── strict, Bernard-readable
│   │   ├── Mod30Structure.lean        ── 8 classes unitaires mod 30
│   │   ├── CayleyG30.lean             ── structure groupe
│   │   ├── HeckeT2Table.lean          ── table T₂ entre classes
│   │   ├── Epsilon30.lean             ── capture diagonale/minorante
│   │   ├── SophieGermainTowerLift.lean── tower lift primoriel SG
│   │   ├── Mod30Classification.lean   ── classification 63/255
│   │   └── ...
│   │
│   ├── Status.lean                    ── invariants doctrinaux universels
│   │   (RHClaimed = False, Status, Gate 0)
│   │
│   ├── ResGold/                       ── (futur) combinatoire finie p générique
│   │   ├── LocalLemma.lean            ── ex-L0 ResGold, après fermeture sorries
│   │   └── ConductorOne.lean          ── ex-L1 ResGold, après fermeture sorries
│   │
│   ├── AnalyticHorizon/               ── machine-certifié niveau analytique
│   │   └── L6Stirling.lean            ── ratio R_χ → 1/2 (fermé 8 mai)
│   │
│   ├── FCI/                           ── machine-certifié couche FCI
│   │   ├── ModThirtyChecker.lean
│   │   ├── ModThirtyCheckerBridge.lean
│   │   ├── CausalSupportImmunity.lean
│   │   └── CausalSupportMeasureBridge.lean
│   │
│   └── LMFDBAlignment.lean            ── interface données externes
│
├── Logic/                             ── ACTIVE (conditionnel ou en cours)
│   ├── ExplicitFormula.lean
│   ├── H3/
│   │   ├── Lemma7Residual.lean        ── Verrou F (sorry [O])
│   │   ├── SpectralBridge.lean        ── v38.3, conditionnel L7For
│   │   ├── MoebiusBridge.lean
│   │   ├── SquarefreeDensity.lean
│   │   └── ...
│   ├── EulerBridgeInfinite.lean
│   ├── C3Weak.lean
│   ├── L10NoGoTheorem.lean
│   └── ...
│
├── ResGold/                           ── ACTIVE (paramétrique Mertens, p-adique reporté)
│   └── MertensAsymptotic.lean         ── ex-L2, intrinsèquement conditionnel
│
└── All.lean                           ── agrégateur racine
```

**Note importante.** Cette arborescence est la **cible**, pas l'état actuel. La migration est progressive
— voir §7. Aucun fichier ne doit être déplacé sans audit préalable.

---

## 6. Audit doctrinal via `#print axioms`

### 6.1 Le principe

Pour tout théorème final du projet, on doit pouvoir auditer ses *axiomes effectifs* via :

```lean
#print axioms CouretUnification.Core.FiniteCore.SophieGermainTowerLift.SG_tower_chain_v38
```

La sortie attendue d'un théorème `FiniteCore` strict est exactement :

```
[propext, Classical.choice, Quot.sound]
```

Ce sont les trois axiomes standards de Mathlib, intrinsèques à Lean 4. Aucun axiome supplémentaire.

### 6.2 Lecture de la sortie

**Si la sortie contient un axiome supplémentaire**, c'est une régression doctrinale. Trois cas typiques :

1. **Un `sorry` traîne quelque part dans la chaîne d'imports.** Lean ajoute alors `sorryAx` à la liste.
C'est facilement détectable et corrigible.

2. **Un `axiom` a été introduit quelque part.** Cas plus grave :
ça veut dire qu'un développeur a ajouté un axiom externe, violant la discipline v36. À traquer et neutraliser.

3. **Une dépendance Mathlib utilise un axiome supplémentaire** (rare, mais possible pour certaines structures avancées).
Audit nécessaire pour évaluer si cet axiome est tolérable.

### 6.3 Procédure d'audit standard

Pour chaque théorème principal d'un fichier `Core` :

```lean
-- À ajouter en fin de fichier en mode debug
#print axioms <nom_du_théorème_principal>
```

Le résultat doit être loggé et vérifié à chaque build CI (quand on en aura un).

**Procédure manuelle Thomas** : périodiquement (par exemple à chaque livraison v38.x), exécuter ces
`#print axioms` sur tous les théorèmes finaux et vérifier la stabilité.

### 6.4 Cas particulier — fichiers paramétriques

Pour un fichier ACTIVE paramétrique (par exemple `SpectralBridge.lean` ou `ResGold/MertensAsymptotic.lean`),
`#print axioms` peut tout de même retourner uniquement les axiomes standards,
parce que les hypothèses paramétriques sont des **prémisses**, pas des axiomes.

Exemple : `conditional_bridge_closure (B : SpectralBridge) (hL7 : L7For B) : ...` ne contient pas d'axiome supplémentaire.
Le fichier est ACTIVE (parce qu'il est intrinsèquement conditionnel sur `hL7`), mais il est *propre au sens des axiomes*.

C'est cohérent : la conditionnalité d'un théorème ne contamine pas `#print axioms` ; elle se lit dans
la *signature* du théorème, pas dans ses dépendances axiomatiques.

---

## 7. Politique de migration ACTIVE → Core

### 7.1 Quand promouvoir un fichier

Un fichier peut passer de ACTIVE à `Core/` (ou de `Core/` étendu à `FiniteCore` strict) si **tous** les
critères suivants sont satisfaits :

1. **Stabilité de build** : le fichier a compilé proprement sur au moins **trois builds verts consécutifs**
(sur trois sessions de travail différentes, donc avec des éventuels changements transitifs Mathlib entre-temps).

2. **Audit `#print axioms` propre** : aucun axiome supplémentaire détecté sur les théorèmes principaux.

3. **Fermeture complète des sorrys** : aucun `sorry` dans le code (les sorrys dans les commentaires sont OK).

4. **Audit des règles v38.x** : passes les tests anti-Prop-nue, anti-True-énoncé, anti-sorry-sur-constante.

5. **Validation Alexandre** : Alexandre a relu et validé la promotion. C'est doctrinal, pas technique :
la migration vers Core engage l'invariant Bernard.

6. **Validation Thomas** : tu confirmes que le fichier ne casse pas le build du reste du projet une fois déplacé.

### 7.2 Procédure de migration

Étape par étape :

1. **Ne pas déplacer le fichier d'abord.** D'abord, faire une PR (ou commit local) avec uniquement le renommage des
imports et namespaces, sur une copie de travail.

2. **Tester le build** sur la copie : `lake build CouretUnification.All` doit rester vert.

3. **Si vert, déplacer physiquement le fichier**, mettre à jour le namespace, mettre à jour `All.lean`.

4. **Rebuilder une dernière fois**.

5. **Mettre à jour la documentation** : ce document si nouvelle catégorie, le README du sous-module concerné.

6. **Ajouter une entrée au journal du projet** (date de promotion, fichier concerné, raison).

### 7.3 Cas concrets actuels — état au 9 mai 2026

| Fichier | État actuel | Cible | Bloqueur(s) à lever |
|---------|-------------|-------|---------------------|
| `SophieGermainTowerLift.lean` | ACTIVE (juste créé) | `FiniteCore` | Validation build Thomas + 2 builds verts supplémentaires |
| `L6Stirling.lean` | ACTIVE (fermé 8 mai) | `Core/AnalyticHorizon` | 2 builds verts supplémentaires |
| `Status.lean` (ResGold) | ACTIVE (sous ResGold) | `Core/Status.lean` | Renommer namespace, ajuster imports ResGold |
| `L0_LocalLemma.lean` | ACTIVE | `Core/ResGold/LocalLemma` | Fermer 4 sorries `[D, provable]` |
| `L1_ConductorOne.lean` | ACTIVE | `Core/ResGold/ConductorOne` | Fermer 2 sorries `[D, provable]` |
| `L2_MertensAsymptotic.lean` | ACTIVE | **reste ACTIVE** | Intrinsèquement conditionnel sur Mertens |
| `SpectralBridge.lean` | ACTIVE | **reste ACTIVE** | Intrinsèquement conditionnel sur L7For |
| `FCI/*.lean` | ACTIVE (livré sans sorry) | `Core/FCI/` | 2 builds verts supplémentaires |

### 7.4 Migrations qui NE doivent JAMAIS être faites

- **`SpectralBridge.lean` vers `Core/`** : intrinsèquement conditionnel sur `L7For B`. La promotion serait un glissement doctrinal grave
— elle suggérerait que la fermeture conditionnelle est de la fermeture absolue.

- **`ResGold/MertensAsymptotic.lean` vers `Core/`** : intrinsèquement conditionnel sur `h_mertens`. Même raison.

- **Tout fichier qui revendique RH ou L7Established** : par construction, ne peut pas être dans `Core/` puisque `RHClaimed = false` est invariant.

---

## 8. Politique de régression — événement majeur

### 8.1 Définition d'une régression Core

Une régression `Core` est tout événement qui fait passer un fichier `Core/` de l'état machine-certifié à l'état non-conformité doctrinale. Cas typiques :

- ajout d'un `sorry` dans une déclaration d'un fichier `Core`,
- ajout d'un `axiom` dans un fichier `Core`,
- ajout d'un import vers un module ACTIVE,
- modification d'un théorème pour qu'il devienne conditionnel.

### 8.2 Gravité

Une régression `Core` est un **événement majeur** du projet. Pas un bug normal. Sa résolution est prioritaire absolue sur tout autre travail.

- Une régression `FiniteCore` strict est **encore plus grave** : elle touche au noyau Bernard.

### 8.3 Procédure de réponse

Si tu détectes une régression :

1. **Arrêter** tout autre travail en cours.

2. **Identifier** le commit qui a introduit la régression (`git log`, `git bisect` si nécessaire).

3. **Notifier** Alexandre immédiatement, avec le diff exact.

4. **Choisir** entre deux options :
   - **Annulation du commit** : si la régression est due à une erreur, revenir à l'état précédent.
   - **Migration du fichier vers ACTIVE** : si la régression révèle que le fichier n'aurait jamais dû être dans Core,
   le rétrograder formellement avec annotation dans la documentation.

5. **Documenter** la régression dans le journal du projet, avec analyse de la cause racine.

6. **Mettre à jour les règles** si la régression révèle une lacune dans la doctrine v38.x (cas typique :
la règle anti-True-énoncé v38.5 est née d'une telle analyse).

### 8.4 Anti-pattern à éviter

**Ne jamais résoudre une régression Core par un patch qui contourne la doctrine.**
Si une régression apparaît, ce n'est pas un signe qu'il faut assouplir Core ;
c'est un signe qu'il y a un problème mathématique ou architectural à traiter à sa racine.

---

## 9. Cas concrets — analyse des fichiers actuels

Tour d'horizon des fichiers actuellement dans le projet, par niveau d'audit.

### 9.1 Déjà dans Core (état du dépôt v36/v38)

À vérifier dans le repository de Thomas : les fichiers actuellement sous `Core/`
(FiniteCore, CayleyG30, LMFDBAlignment, etc.) sont supposément déjà conformes. Audit à refaire périodiquement.

### 9.2 Candidats immédiats (peu de friction)

- **`SophieGermainTowerLift.lean`** : passe les 3 tests `FiniteCore`. Migration vers `Core/FiniteCore/` une fois
 validé par 3 builds verts.

- **`Status.lean` (ResGold)** : passe les tests Core (pas FiniteCore
— pas spécifiquement mod 30). Migration vers `Core/Status.lean`, namespace `CouretUnification.Core`.
Le contenu est universel doctrinal.

- **`L6Stirling.lean`** : passe les tests Core mais pas FiniteCore (analytique). Migration vers `Core/AnalyticHorizon/L6Stirling.lean`.

- **`FCI/*.lean`** (les 4 fichiers livrés sans sorry) : passent les tests Core. Migration vers `Core/FCI/` après
2 builds verts supplémentaires.

### 9.3 Candidats différés (sorries à fermer)

- **`L0_LocalLemma.lean`** (ResGold) : 4 sorries `[D, provable]` à fermer.
Une fois fermés, candidat `Core/ResGold/LocalLemma.lean`.

- **`L1_ConductorOne.lean`** (ResGold) : 2 sorries `[D, provable]` à fermer.
Une fois fermés, candidat `Core/ResGold/ConductorOne.lean`.

### 9.4 Reste en ACTIVE permanent

- **`L2_MertensAsymptotic.lean`** : conditionnel sur Mertens, ACTIVE intrinsèque.

- **`SpectralBridge.lean`** : conditionnel sur L7For, ACTIVE intrinsèque.

- **`ResGold.lean`** racine : agrégateur, ne migre pas.

### 9.5 Encore ouverts (sorrys [O] ou [H] non triviaux)

- **`Logic/H3/Lemma7Residual.lean`** : ACTIVE, Verrou F ouvert.
- **`Logic/H3/MoebiusBridge.lean`, `SquarefreeSupport.lean`, `SquarefreeDensity.lean`** : ACTIVE, sorries `[H]/[O]`.
- **`Logic/EulerBridgeInfinite.lean`, `L10NoGoTheorem.lean`** : ACTIVE.
- **`AnalyticHorizon/Det2Transport.lean`** : ACTIVE.

Ces fichiers ne sont pas candidats migration tant que les sorries ne sont pas fermés ou
que leur statut [O] n'est pas résolu doctrinalement.

---

## 10. Questions/Réponses anticipées

### Q1. *« Je crée un nouveau fichier qui prouve une identité combinatoire sur mod 30 et qui n'a pas de sorry. Je le mets directement dans `Core/FiniteCore/` ? »*

**Non.** Premier build vert. Puis 2 builds verts supplémentaires sur des sessions séparées. Audit `#print axioms`.
Validation Alexandre. *Ensuite* migration vers `Core/FiniteCore/`.

Tu peux le placer dans `Core/FiniteCore/` *du premier coup* si tu es absolument sûr, mais la doctrine prudente est
de le mettre dans un dossier d'attente (par exemple `Logic/Candidates/` ou simplement en racine de `CouretUnification/`) jusqu'à validation.

### Q2. *« Un théorème Core utilise un lemme Mathlib qui dépend transitivement d'un axiome non-standard. Régression ? »*

**Pas forcément.** Audit `#print axioms` sur le théorème final pour voir si l'axiome remonte effectivement. Si oui,
évaluer doctrinalement : certains axiomes Mathlib avancés sont tolérables (par exemple, choix dépendant pour certaines
constructions standards), d'autres non. Décision au cas par cas avec Alexandre.

En pratique, pour la couche analytique de Mathlib v4.29.1, l'audit `#print axioms` retourne presque toujours uniquement
les trois axiomes standards. Pas de stress prématuré.

### Q3. *« Comment je fais quand j'ai besoin d'importer un module ACTIVE depuis un autre module ACTIVE ? Ça reste possible ? »*

**Oui.** La règle est unidirectionnelle : `Core/` ne dépend pas de `ACTIVE/`. Mais `ACTIVE/` peut dépendre d'autres `ACTIVE/`.
C'est même la norme : `L2_MertensAsymptotic.lean` (ACTIVE) importe `L1_ConductorOne.lean` (ACTIVE) qui importe `L0_LocalLemma.lean` (ACTIVE).

### Q4. *« Un fichier ACTIVE devient FROZEN avec le temps, mais comment je gère l'historique des sessions où il était encore ACTIVE ? »*

**Documentation et journal.** Quand un fichier migre, on ajoute une entrée au journal du projet (`journal.txt` mentionné dans la mémoire)
qui dit : *« 2026-05-XX : promotion de `<fichier>` de ACTIVE vers `Core/FiniteCore/`. Sorries fermés : X, Y, Z. Audit `#print axioms` : propre. »*
Cette traçabilité permet de reconstruire l'historique doctrinal en cas d'audit externe.

### Q5. *« Si je dois ajouter temporairement un `sorry` dans un fichier `Core` pour un refactor en cours, qu'est-ce que je fais ? »*

**Tu ne fais pas ça.** Tu travailles sur une branche séparée (`git checkout -b refactor-XYZ`), tu fais ton refactor là-bas, et
tu ne mergais dans la branche principale qu'une fois tous les sorries éliminés. La branche principale doit toujours avoir `Core/` propre.

### Q6. *« Le namespace `CouretUnification.Core.FiniteCore.Mod30Structure` est très long. Je peux le raccourcir ? »*

**Garde la hiérarchie complète.** L'avantage doctrinal de la hiérarchie longue : le namespace *est* l'audit.
Quand tu lis `import CouretUnification.Core.FiniteCore.Mod30Structure`, tu sais immédiatement que c'est du FROZEN strict mod 30.
Si tu raccourcis en `Mod30Structure` direct, tu perds cette information.

L'usage local avec `open CouretUnification.Core.FiniteCore.Mod30Structure` est fait pour ça :
tu importes le chemin complet, mais tu fais `open` pour avoir les noms courts dans le corps du fichier.

### Q7. *« Quand est-ce que je peux dire « ce théorème est dans le régime FROZEN » à un relecteur externe ? »*

**Quand toutes ses dépendances transitives sont dans `Core/`** (vérifiable par `lake env show` ou équivalent), **et**
que `#print axioms` retourne uniquement les trois axiomes standards. Pas avant. Si une seule dépendance transitive est ACTIVE,
le théorème est conditionnel, point.

### Q8. *« Et si Alexandre veut promouvoir un fichier vers FiniteCore mais que je détecte un problème ? »*

**Tu refuses ou tu retardes.** La promotion vers Core/FiniteCore engage la doctrine. Si tu vois un problème
(sorry oublié, axiome caché, dépendance ACTIVE), tu le signales et tu attends la résolution. Alexandre comprendra
— la discipline est cumulative, jamais sacrifiée pour vitesse.

C'est une protection mutuelle : si Alexandre, dans un moment de fatigue, pousse une promotion prématurée, tu es le garde-fou.
Et inversement.

---

## 11. Checklist pratique avant chaque commit

À garder en référence quotidienne. Trois minutes par commit.

### Avant `git commit` sur n'importe quel fichier Lean :

- [ ] Le fichier compile (`lake build <module>`).
- [ ] Tous les `sorry` du fichier sont annotés `[D, provable]`, `[H]`, `[O]`, ou `[D conditional on ...]`.
- [ ] Aucun `axiom` n'a été ajouté.
- [ ] Aucun nouvel énoncé `: True := ...`.
- [ ] Aucun `noncomputable def k : <Type> := sorry` (sauf si conditionnellement justifié et annoté).
- [ ] Aucune `Prop` nue comme champ de structure.
- [ ] Le namespace correspond à l'emplacement du fichier.

### Avant `git commit` sur un fichier dans `Core/` :

Toutes les précédentes, plus :

- [ ] Zéro `sorry` effectif.
- [ ] Zéro `axiom`.
- [ ] Aucun nouvel `import` vers un module ACTIVE.
- [ ] `#print axioms <théorème_principal>` retourne uniquement `[propext, Classical.choice, Quot.sound]`.

### Avant `git commit` sur un fichier dans `Core/FiniteCore/` :

Toutes les précédentes, plus :

- [ ] Le contenu reste arithmétique mod 30 (ou ses extensions primorielles).
- [ ] Toutes les preuves sont combinatoires finies (pas d'analyse réelle, pas de limite).
- [ ] Un mathématicien classique pourrait, en principe, vérifier le contenu à la main avec patience.

### Avant toute migration ACTIVE → Core :

- [ ] Trois builds verts consécutifs sur trois sessions séparées.
- [ ] Audit `#print axioms` propre.
- [ ] Validation Alexandre.
- [ ] Mise à jour journal du projet.

---

## 12. Pour Bernard

Cette doctrine architecturale n'est pas une bureaucratie. C'est la matérialisation, dans le code,
d'une distinction épistémique fondamentale :

- **Ce que Bernard aurait pu vérifier** (FiniteCore strict).
- **Ce que la machine peut vérifier sans condition** (Core étendu).
- **Ce qui reste sous hypothèse** (ACTIVE).
- **Ce qui résonne sans intégrer** (Q).

Sans cette distinction, le projet ne serait qu'un tas de fichiers compilés. Avec elle,
il devient une *carte de l'établi*, où chaque théorème porte son régime d'audit dans son chemin d'accès.
Un lecteur externe qui regarde `CouretUnification.Core.FiniteCore.SophieGermainTowerLift.SG_tower_chain_v38` sait
immédiatement, sans avoir à lire le fichier, qu'il est en régime Bernard-readable strict.

Le travail continue.

---

*Document produit le 9 mai 2026.*
*Référence : DOCTRINE_FINITECORE_VS_CORE_v38.5.md*
*RHClaimed = false. Le noyau fini est ce que Bernard a transmis.*
