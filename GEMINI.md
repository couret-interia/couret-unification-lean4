# GEMINI.md — Couret-Unification Lean 4

> Répondre en français par défaut. Garder les noms Lean, chemins, commandes, identifiants et messages d'erreur inchangés. Ajouter un court résumé anglais seulement si utile.

Ce fichier est l'adaptateur court pour Gemini CLI / NotebookLM. Le protocole complet est dans `AGENTS/INTERIA.md`.

## Identité

- Organisation : `couret-interia`.
- Dépôt : `couret-unification-lean4`.
- Namespace : `CouretUnification`.
- Toolchain : Lean `v4.29.1`.
- Mathlib : `v4.29.1`.

## Travail attendu

Séparer nettement :

- preuve Lean ;
- computation finie ;
- expérience numérique ;
- hypothèse ;
- interprétation philosophique.

## Audit

Utiliser `AGENTS/LEAN_AUDIT.md` et les cibles du `Makefile`.

Commande courte :

```bash
make build-log-all && make audit-sorries && make audit-warnings && make doctrine-check
```

## Garde-fou

Un résultat fini modulo 30 n'est pas une preuve globale sur les nombres premiers.
