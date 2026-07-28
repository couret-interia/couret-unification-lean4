# Cibles Makefile — lecture InterIA

Ce dépôt possède un `Makefile` riche. Les agents doivent utiliser ses cibles au lieu d'inventer des commandes parallèles.

## Build

```bash
make build
```

Équivalent attendu : `lake build`.

```bash
make build-all
```

Équivalent attendu : `lake build CouretUnification.All`.

```bash
make build-log-all
```

Construit `CouretUnification.All` et écrit les journaux dans `build_reports/` :

- `build_reports/build.log`
- `build_reports/errors_unique.txt`
- `build_reports/warnings_unique.txt`

## Audits internes

```bash
make audit-imports
make audit-sorries
make audit-warnings
make audit-axiom-declarations
make audit-true-statements
make audit-invariants
```

Ces cibles détectent respectivement :

- imports `CouretUnification.*` cassés ;
- déclarations utilisant `sorry` dans le log Lean ;
- warnings non liés aux `sorry` ;
- déclarations textuelles `axiom` ;
- théorèmes triviaux `: True := ...` ;
- invariants doctrinaux comme `RHClaimed`, `HilbertPolyaClaimed`, `Det2IdentityClaimed`.

## Audits externes / scripts

```bash
make audit-proved
make audit-collisions
make audit-collisions-basic
make check-frozen
make gate-frozen
make audit-orphans
make audit-reachability
make audit-doctrine
make audit-scripts
```

Ces cibles dépendent de scripts présents dans `scripts/`. En cas d'échec, ne pas masquer l'erreur : rapporter la cible, le script appelé et la sortie exacte.

## Méta-cibles

```bash
make audit-all
make doctrine-check
make report
make snapshot
```

- `audit-all` lance le build loggé et la suite complète d'audits.
- `doctrine-check` est un contrôle rapide des invariants critiques.
- `report` agrège architecture, build et audits.
- `snapshot` copie les logs et rapports dans un dossier daté.

## Discipline agents IA

Lorsqu'un agent modifie un fichier Lean, il doit proposer au minimum :

```bash
make audit-imports audit-sorries audit-warnings \
  audit-axiom-declarations audit-true-statements audit-invariants
make doctrine-check
```

Si le changement touche la couche fermée ou les invariants doctrinaux, ajouter :

```bash
make audit-all
```
