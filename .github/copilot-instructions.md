# GitHub Copilot instructions — Couret-Unification Lean 4

Répondre en français par défaut dans les commentaires, explications et suggestions textuelles. Garder les chemins, commandes, noms Lean, noms de théorèmes et messages d'erreur inchangés.

Lire `AGENTS/INTERIA.md` pour le protocole complet.

## Règles de code

- Préserver le namespace `CouretUnification`.
- Ne pas introduire `sorry`, `axiom` ou `admit` dans les fichiers Lean de production.
- Utiliser les cibles `make` du dépôt quand elles existent.
- Pour les calculs finis, préférer des définitions finies explicites et `native_decide` quand c'est approprié.
- Ne pas ajouter de commentaire revendiquant une conséquence globale en théorie des nombres à partir d'un calcul fini modulo 30.

## Commandes de validation

```bash
make build-log-all
make audit-sorries
make audit-warnings
make doctrine-check
```

Pour un audit complet avant tag :

```bash
make audit-all
make report
make snapshot
```
