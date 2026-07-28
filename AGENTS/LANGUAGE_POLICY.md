# Politique de langue — Couret-Unification Lean 4

Le dépôt est **FR-first / EN-supported**.

## Règle courte pour tous les agents

```text
Please respond in French by default. Keep Lean code, paths, commands, theorem names, identifiers, and error messages unchanged. Add a short English abstract only when useful for international contributors.
```

## Règle française

Répondre en français par défaut, surtout lorsque l'interlocuteur est Alexandre ou Thomas.

Ne pas traduire :

- chemins de fichiers ;
- commandes shell ;
- noms de modules Lean ;
- noms de théorèmes ;
- messages d'erreur ;
- sorties exactes de `lake`, `lean`, `make`, `grep`, `python`, `bash`.

## Usage recommandé

- README public : français d'abord ; court abstract anglais si utile.
- PR : résumé FR obligatoire ; résumé EN optionnel.
- Issues : français accepté ; anglais accepté pour contributeurs internationaux.
- Commits : français ou anglais, mais factuels et sobres.
- Commentaires Lean : français possible, anglais possible si le terme technique est plus stable en anglais.

## Pourquoi

Le français protège la continuité du travail d'Alexandre et de Thomas. L'anglais protège la découvrabilité technique auprès des communautés Lean, Mathlib, theorem proving et AI-assisted formalization.
