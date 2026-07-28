# /lean-audit

Lancer ou proposer l'audit Lean standard du dépôt :

```bash
make build-log-all
make audit-sorries
make audit-warnings
make doctrine-check
```

Puis résumer en français :

- erreurs uniques ;
- warnings non-sorry ;
- sorries détectés ;
- invariants doctrinaux ;
- statut final proposé.
