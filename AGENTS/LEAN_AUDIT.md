# Audit Lean — Couret-Unification

Ce document est aligné sur le `Makefile` du dépôt. Les agents IA doivent citer les cibles `make` réellement disponibles au lieu de proposer des commandes génériques non reliées au dépôt.

## Niveau 0 — vérification minimale

À lancer après une petite modification documentaire ou un changement local non critique :

```bash
lake build
```

ou, via le `Makefile` :

```bash
make build
```

## Niveau 1 — build complet loggé

À lancer après une modification Lean ordinaire :

```bash
make build-log-all
```

Cette cible construit `CouretUnification.All` et produit :

```text
build_reports/build.log
build_reports/errors_unique.txt
build_reports/warnings_unique.txt
```

## Niveau 2 — audit de sorries et warnings

À lancer avant une PR touchant `lean/` :

```bash
make audit-sorries
make audit-warnings
make audit-axiom-declarations
make audit-true-statements
make audit-invariants
```

Rapports attendus :

```text
build_reports/sorries_declarations.txt
build_reports/warnings_non_sorry.txt
build_reports/axiom_declarations.txt
build_reports/true_statements.txt
build_reports/invariants.txt
```

## Niveau 3 — audit structurel

À lancer avant merge ou tag :

```bash
make audit-imports
make audit-reachability
make audit-orphans
make check-frozen
make gate-frozen
make audit-doctrine
make audit-proved
```

## Niveau 4 — audit complet opposable

À lancer avant une release candidate ou un tag public :

```bash
make audit-all
make report
make snapshot
```

## CI GitHub Actions recommandée

La CI doit rester fidèle au `Makefile`. Elle ne doit pas inventer une autre grammaire d'audit.

Pipeline recommandé :

1. installer Lean via `leanprover/lean-action` ;
2. lancer `make build-log-all` ;
3. lancer les audits internes rapides ;
4. lancer `make doctrine-check` ;
5. publier `build_reports/` comme artefact, même en cas d'échec.

Les audits plus lourds (`make audit-all`, `make report`) peuvent être gardés pour `workflow_dispatch`, tags ou branches de release.

## Règles de statut

- Ne pas écrire `[L-verified]` sans build réussi.
- Ne pas écrire `[T-theorem]` si le résultat dépend d'un `sorry`, d'un `axiom`, ou d'une hypothèse non nommée.
- Ne pas transformer un `[D-computational, finite]` en revendication globale.
- Un échec CI est `[X-blocked]` jusqu'à correction.

## Rapport minimal attendu

Tout audit doit indiquer :

- version Lean / Mathlib ;
- commande exacte ;
- module ou cible buildée ;
- résultat : succès / échec ;
- nombre de `sorry` trouvés ;
- nombre de warnings non-sorry ;
- présence ou non d'`axiom` ;
- statut final proposé.

## Commande courte pour Thomas

```bash
make audit-imports audit-sorries audit-warnings \
  audit-axiom-declarations audit-true-statements audit-invariants
make doctrine-check
```
