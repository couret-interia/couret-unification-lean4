# Couret-Unification — génération de documentation avec doc-gen4

Ce répertoire contient un mini-projet Lake dédié à la génération de la documentation HTML du dépôt `CouretUnification` avec [`doc-gen4`](https://github.com/leanprover/doc-gen4).

L’objectif est de produire une documentation consultable localement, sans modifier le `lakefile` principal du dépôt.

---

## 1. Pré-requis

Depuis la racine du dépôt, entrer dans le répertoire dédié :

```bash
cd docbuild
```

Vérifier la version de Lean utilisée :

```bash
lake env lean --version
```

Version attendue pour cette branche :

```text
Lean 4.29.1
```

---

## 2. Initialisation / mise à jour

Lors de la première installation, ou après modification du `lakefile.toml`, exécuter :

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
```

Le fichier `lake-manifest.json` est commité afin de rendre la génération reproductible.

---

## 3. Génération recommandée : documentation locale exhaustive

Commande recommandée pour générer toute la documentation locale du paquet :

```bash
DOCGEN_SRC="file" lake build CouretUnification.All:docs
```

Cette commande utilise des liens locaux vers les fichiers sources Lean.

Elle évite l’erreur liée à l’absence de remote Git :

```text
Failed to find a git remote in your project
```

Cette erreur peut apparaître avec le mode GitHub par défaut lorsque la copie locale du dépôt ne possède pas de remote Git configuré.

---

## 4. Variantes de génération

### Documentation du module principal uniquement

```bash
DOCGEN_SRC="file" lake build CouretUnification:docs
```

### Documentation complète avec liens GitHub

À utiliser seulement si le dépôt possède un remote Git valide :

```bash
DOCGEN_SRC="github" lake build CouretUnification:docs
```

ou, pour la documentation exhaustive :

```bash
DOCGEN_SRC="github" lake build CouretUnification.All:docs
```

### Documentation complète avec liens VSCode / VSCodium

```bash
DOCGEN_SRC="vscode" lake build CouretUnification.All:docs
```

---

## 5. Visualisation locale

Après génération, la documentation HTML se trouve dans :

```bash
docbuild/.lake/build/doc
```

Depuis la racine du dépôt :

```bash
cd docbuild/.lake/build/doc
python3 -m http.server
```

Puis ouvrir dans un navigateur :

```text
http://localhost:8000
```

---

## 6. Durée et taille attendues

Le premier build peut être long, en particulier parce que `doc-gen4` génère aussi la documentation des dépendances, dont `mathlib`.

Ordres de grandeur observés :

```text
Premier build : plusieurs heures possibles
Taille générée : environ 750 Mo ou plus
```

Les builds suivants sont généralement plus rapides grâce au cache Lake.

---

## 7. Avertissements connus

Pendant la génération, `doc-gen4` peut afficher de nombreux avertissements de ce type :

```text
WARNING: Failed to calculate equational lemmata ...
```

Ces avertissements concernent souvent Lean, Mathlib ou les dépendances, et ne bloquent pas nécessairement la génération.

Le dépôt peut aussi afficher les avertissements attendus sur les fichiers contenant encore des `sorry`, notamment dans les couches analytiques ou conditionnelles du programme.

Le critère de succès est la ligne finale :

```text
Build completed successfully
```

Exemple validé :

```text
info: Generating documentation for CouretUnification.All and dependencies
Build completed successfully
```

---

## 8. Fichiers à ne pas committer

Ne pas committer les artefacts générés :

```text
docbuild/.lake/build/doc
docbuild/.lake/build
```

Le répertoire `docbuild/` contient seulement l’infrastructure de génération :

```text
docbuild/
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
└── README.md
```

---

## 9. Commande canonique courte

Pour usage courant :

```bash
cd docbuild
DOCGEN_SRC="file" lake build CouretUnification.All:docs
cd .lake/build/doc
python3 -m http.server
```
