# AGENTS.md — Couret-Unification Lean 4

> Répondre en français par défaut. Garder les noms Lean, chemins, commandes, identifiants et messages d'erreur inchangés.

Ce fichier est l'adaptateur court pour ChatGPT / Codex et agents compatibles. Le protocole complet est dans `AGENTS/INTERIA.md`.

## Lire d'abord

1. `AGENTS/INTERIA.md`
2. `AGENTS/LEAN_AUDIT.md`
3. `AGENTS/MAKE_TARGETS.md`
4. `AGENTS/STATUS_TAGS.md`
5. `AGENTS/LANGUAGE_POLICY.md`

## Règles obligatoires

- Ne pas affirmer qu'un résultat est vérifié sans build ou CI correspondant.
- Ne pas ajouter `sorry`, `axiom` ou `admit` dans les fichiers Lean de production.
- Préserver le namespace `CouretUnification`.
- Ne pas transformer un certificat fini modulo 30 en preuve globale sur les nombres premiers.
- En cas de blocage, utiliser `[X-blocked]`, pas `[T-theorem]`.

## Commandes de référence

```bash
make build-log-all
make audit-sorries
make audit-warnings
make doctrine-check
```

Avant tag ou livraison majeure :

```bash
make audit-all
make report
make snapshot
```

## Rapport final attendu

Indiquer : fichiers modifiés, commandes lancées, résultat du build, rapports `build_reports/` consultés, statut final, risques restants.
