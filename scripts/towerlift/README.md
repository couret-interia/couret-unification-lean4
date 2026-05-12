# Scripts TowerLift / Sophie Germain

**Statut : `[M]` — numérique, expérimental, reproductible**
**Dépôt : Couret–Unification v38x**
**Répertoire : `scripts/towerlift/`**

Ce dossier regroupe les scripts Python issus du pack TowerLift / Sophie Germain, adaptés aux chemins du dépôt principal Couret–Unification v38x.

Ils servent à reproduire les calculs numériques, les visualisations et les artefacts JSON/PNG liés aux analyses Sophie Germain modulo 30, 210 et 2310.

Ces scripts ne font pas partie du noyau Lean démonstratif `[D]`. Ils appartiennent à la couche :

```text
[M] numérique / expérimentation / reproductibilité
```

Les résultats Lean démontrés associés vivent séparément dans :

```text
lean/CouretUnification/Core/SophieGermainHecke.lean
lean/CouretUnification/Core/SophieGermainTowerLift.lean
lean/CouretUnification/Residue/SGShiftSqrt2.lean
```

---

## 1. Préparation de l'environnement

Depuis la racine du dépôt :

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

Puis exécuter les scripts depuis la racine du dépôt, par exemple :

```bash
python scripts/towerlift/toymodel_validation.py
```

---

## 2. Scripts disponibles

### 2.1 `toymodel_validation.py`

**Objet :** validation numérique du modèle jouet Euler ↔ spectral Sophie Germain.

Ce script :

- construit les nombres de Sophie Germain jusqu'à la borne fixée ;
- calcule la distribution dans les classes actives `S.11`, `S.23`, `S.29` ;
- construit la matrice de transition empirique `M₃` ;
- construit les opérateurs `T₂`, `D_ε₃₀`, `Δ_SG` et `Δ̃_SG` ;
- calcule les valeurs propres de l'opérateur symétrisé ;
- vérifie le couplage faible sous forme existentielle ;
- produit une synthèse opérationnelle du bridge Euler ↔ spectral SG.

Commande :

```bash
python scripts/towerlift/toymodel_validation.py
```

Statut :

```text
[M] validation numérique / modèle jouet
```

Remarque doctrinale :

Le script observe des proximités numériques avec `1/√7`, mais ne les promeut pas au statut `[D]`.
Le résultat exact Lean actuellement démontré pour le bloc SG-shift fini est l'identité rationnelle :

```text
M³ = (1/2)M
```

dans :

```text
lean/CouretUnification/Residue/SGShiftSqrt2.lean
```

---

### 2.2 `sophie_germain_analysis.py`

**Objet :** analyse des chaînes de Sophie Germain et des transitions modulo 30.

Ce script :

- identifie les nombres de Sophie Germain ;
- construit des chaînes de Cunningham ;
- calcule les transitions directes `p → 2p + 1` ;
- confirme la structure déterministe modulo 30 :

```text
11 → 23
23 → 17
29 → 29
```

- calcule des matrices de transition directes et consécutives ;
- produit des visualisations et un export JSON.

Commande :

```bash
python scripts/towerlift/sophie_germain_analysis.py
```

Sorties attendues :

```text
docs/towerlift/sophie_germain_results.json
docs/towerlift/sophie_germain_graph.png
docs/towerlift/sophie_germain_spectral.png
```

Statut :

```text
[M] analyse numérique / visualisation / reproductibilité
```

Lien Lean associé :

```text
lean/CouretUnification/Core/SophieGermainHecke.lean
lean/CouretUnification/Core/SophieGermainTowerLift.lean
```

---

### 2.3 `information_analysis.py`

**Objet :** analyse informationnelle du canal Sophie Germain sous relèvements primoriels.

Ce script :

- compare les niveaux modulo 30, 210 et 2310 ;
- calcule entropie marginale, information mutuelle, entropie conditionnelle ;
- évalue la capacité du canal ;
- mesure une vitesse informationnelle basée sur le gap spectral ;
- compare plusieurs métriques à `1/7` et `1/√7`.

Commande :

```bash
python scripts/towerlift/information_analysis.py
```

Sortie attendue :

```text
docs/towerlift/information_analysis.json
```

Statut :

```text
[M] analyse informationnelle / exploration numérique
```

Remarque doctrinale :

Ce script teste des hypothèses de stabilité sous lift.
Il ne démontre pas une identité analytique globale.
Les comparaisons à `1/√7` doivent rester au statut expérimental tant qu'aucun pont Lean ou analytique séparé ne les établit.

---

### 2.4 `dimensional_test.py`

**Objet :** test dimensionnel comparant les constantes candidates aux niveaux modulo 30, 210 et 2310.

Ce script :

- vérifie les signes du caractère `ε₃₀` utilisés par le code ;
- détecte et documente l'incohérence typographique éventuelle de l'article concernant `ε₃₀(23)` ;
- construit les données Sophie Germain ;
- compare les spectres de `Δ̃` aux constantes candidates :

```text
1/√2
1/√7
1/√14
1/√134
```

- exporte un verdict dimensionnel.

Commande :

```bash
python scripts/towerlift/dimensional_test.py
```

Sortie attendue :

```text
docs/towerlift/dimensional_test_results.json
```

Statut :

```text
[M] test numérique / discrimination dimensionnelle
```

Remarque doctrinale :

Le verdict numérique du script ne doit pas être lu comme une preuve Lean.
La distinction canonique à préserver est :

```text
1/√2 : invariant algébrique exact du bloc SG-shift, démontré en Lean.
1/√7 : invariant géométrique global ou hypothèse/observation selon la couche.
```

---

### 2.5 `delta7_sophie_germain.py`

**Objet :** analyse spectrale de type `Δ⁷` appliquée aux nombres de Sophie Germain modulo 30.

Ce script :

- construit les données SG jusqu'à la borne choisie ;
- calcule la matrice de transition `M₃` ;
- analyse le spectre de `M₃`, de la fluctuation `Q₃`, de `T₂` et de `Δ_SG` ;
- compare les constantes de simplexe `1/√2` et `1/√7` ;
- génère des visualisations et des exports JSON.

Commande :

```bash
python scripts/towerlift/delta7_sophie_germain.py
```

Sorties attendues :

```text
docs/towerlift/delta7_sg_results.json
docs/towerlift/delta7_sophie_germain.png
```

Statut :

```text
[M] analyse spectrale numérique / visualisation
```

Remarque doctrinale :

Les comparaisons numériques à `1/√7` sont conservées comme résultats expérimentaux.
Le résultat formel Lean démontré reste séparé :

```text
Residue/SGShiftSqrt2.lean : M³ = (1/2)M
```

---

## 3. Répertoire de sortie

Les scripts écrivent leurs artefacts dans :

```text
docs/towerlift/
```

Ce répertoire peut contenir :

```text
*.json   résultats numériques structurés
*.png    visualisations
*.docx   synthèses générées ou documents de travail
*.md     notes d'intégration et notes doctrinales
```

Les fichiers JSON/PNG/DOCX sont des artefacts expérimentaux.
Ils ne remplacent pas les preuves Lean.

---

## 4. Doctrine de statut

### Couche `[D]`

Les résultats Lean suivants sont démontrés et intégrés à `CouretUnification.All` :

```text
Core/SophieGermainHecke.lean
Core/SophieGermainTowerLift.lean
Residue/SGShiftSqrt2.lean
```

Ils établissent :

```text
- le SG-shift modulo 30 ;
- le tower lift primoriel avec règle ℓ - 2 ;
- l'identité cubique rationnelle M³ = (1/2)M.
```

### Couche `[M]`

Les scripts de ce dossier relèvent de :

```text
- calcul numérique ;
- exploration ;
- visualisation ;
- reproductibilité expérimentale ;
- génération d'artefacts.
```

Ils peuvent soutenir les hypothèses, mais ne les clôturent pas.

### Couche `[H]` ou legacy

Les anciennes affirmations de type :

```text
Δ̃_SG ≈ 1/√7
```

doivent rester classées comme :

```text
[M] observation numérique
```

ou :

```text
[H] hypothèse
```

tant qu'elles ne sont pas reliées à une preuve Lean ou à un argument analytique fermé.

---

## 5. Commandes de vérification recommandées

Exécuter les cinq scripts :

```bash
python scripts/towerlift/toymodel_validation.py
python scripts/towerlift/sophie_germain_analysis.py
python scripts/towerlift/information_analysis.py
python scripts/towerlift/dimensional_test.py
python scripts/towerlift/delta7_sophie_germain.py
```

Puis vérifier que le dépôt Lean compile toujours :

```bash
lake build CouretUnification.All
```

---

## 6. Points d'attention

### 6.1 Sorties `#eval` côté Lean

Les modules expérimentaux Lean :

```text
lean/CouretUnification/Experimental/TowerLift/ToyModel.lean
lean/CouretUnification/Experimental/TowerLift/ToyModelFloat.lean
```

produisent volontairement des sorties `info` au build, car ils contiennent des `#eval`.

C'est acceptable dans la couche expérimentale.

### 6.2 Incohérence `ε₃₀(23)`

Le script `dimensional_test.py` documente une incohérence possible entre une ancienne section d'article et le code.

Le code stabilisé utilise :

```text
ε₃₀(11) = -1
ε₃₀(23) = -1
ε₃₀(29) = +1
```

Cette table est cohérente avec les fichiers Lean récemment intégrés.

### 6.3 Ne pas surclasser les observations numériques

Même lorsque les résultats numériques sont frappants, ils doivent rester séparés des résultats Lean `[D]`.

La ligne doctrinale à préserver est :

```text
[D] noyau fini vérifié
[M] numérique reproductible
[H] hypothèse interprétative
[O] ouvert ou non reproduit
```

---

## 7. Résumé court

Ce dossier fournit la couche expérimentale TowerLift / Sophie Germain du dépôt Couret–Unification v38x.

Il complète les preuves Lean `[D]` par des scripts reproductibles `[M]`.

Les scripts sont utiles pour :

```text
- reproduire les matrices ;
- générer les figures ;
- vérifier les constantes empiriques ;
- produire les JSON de suivi ;
- documenter les hypothèses ouvertes.
```

Ils ne revendiquent aucune preuve globale de type RH, Hilbert–Pólya ou L7.

Invariants préservés :

```text
RHClaimed = false
HilbertPolyaClaimed = false
L7Established = false
TopologicalUniversalityClaimed = false
```
