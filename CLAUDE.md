# CLAUDE.md — Couret-Unification Lean 4

> Répondre en français par défaut. Garder les noms Lean, chemins, commandes, identifiants et messages d'erreur inchangés.

Lire `AGENTS/INTERIA.md` avant tout refactor ou audit Lean.

## Sources utiles

- `AGENTS/LEAN_AUDIT.md` — audit aligné sur le `Makefile`.
- `AGENTS/MAKE_TARGETS.md` — cibles `make` disponibles.
- `AGENTS/STATUS_TAGS.md` — grammaire des statuts.
- `AGENTS/LANGUAGE_POLICY.md` — politique FR-first / EN-supported.

## Règles Claude Code

1. Thomas / compilateur décide le statut Lean final.
2. Ne pas promouvoir une conjecture, une analogie ou un calcul fini en théorème global.
3. Ne pas ajouter `sorry`, `axiom`, `admit` dans les fichiers de production.
4. Utiliser les cibles `make` du dépôt quand elles existent.
5. Rapporter toute commande lancée et tout échec exact.

## Commande courte

```bash
make build-log-all && make audit-sorries && make audit-warnings && make doctrine-check
```
