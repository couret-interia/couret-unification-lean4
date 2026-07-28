# Où placer ces fichiers

Copier le contenu de ce kit à la racine du nouveau dépôt GitHub.

Arborescence finale recommandée :

```text
<repo>/
  AGENTS.md
  CLAUDE.md
  GEMINI.md
  INTERIA.md
  INTERIA.yml
  .chatgpt.yml        # manifeste optionnel ; AGENTS.md est le fichier important
  .claude.yml         # manifeste optionnel ; CLAUDE.md est le fichier important
  .gemini.yml         # manifeste optionnel ; GEMINI.md est le fichier important
  .claude/
    CLAUDE.md
    commands/
      lean-audit.md
  .github/
    copilot-instructions.md
    pull_request_template.md
    workflows/
      lean.yml
  .cursor/
    rules/
      couret-unification.mdc
  docs/
    INTERIA_PROTOCOL.md
    LANGUAGE_POLICY.md
    LEAN_AUDIT.md
    STATUS_TAGS.md
```

Les adaptateurs reconnus/officiels sont :

- `AGENTS.md` pour Codex / agents OpenAI de codage.
- `CLAUDE.md` ou `.claude/CLAUDE.md` pour Claude Code.
- `GEMINI.md` pour Gemini CLI.
- `.github/copilot-instructions.md` pour GitHub Copilot.

Les fichiers `.chatgpt.yml`, `.claude.yml` et `.gemini.yml` sont des manifestes neutres optionnels. Ils peuvent aider au routage machine, mais ne doivent pas être considérés comme le mécanisme officiel d'instruction des outils.

## Politique de langue

Cette version est **FR-first / EN-supported** :

- les instructions humaines sont en français ;
- les mots-clés techniques restent en anglais lorsque c'est utile ;
- chaque agent reçoit l'instruction : répondre en français par défaut.
