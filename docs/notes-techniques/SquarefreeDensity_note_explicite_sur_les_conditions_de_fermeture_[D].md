## Peut-on réunir les conditions pour passer C-04a/C-04b en `[D]` ?

Oui. Il faut expliciter un petit **dossier de fermeture [D]** dans le code ou dans un document associé. Aujourd’hui, les deux bridges disent :

```lean
SquarefreeCountGeHalfBridge
SquarefreeAsymptoticDensityBridge
```

Pour les remplacer par de vraies preuves `[D]`, il faut fermer deux chaînes distinctes.

### Pour C-04a : `squarefreeCount_ge_half`

Il faut prouver effectivement :

```lean
∀ {N : ℕ}, 176 ≤ N → (N : ℚ) / 2 ≤ squarefreeCount N
```

Conditions nécessaires :

1. Une formule exacte du comptage squarefree, du type :

```lean
squarefreeCount N =
  ∑ d ∈ Icc 1 (Nat.sqrt N), μ(d) * ⌊N / d^2⌋
```

ou une variante équivalente.

2. Une borne inférieure effective de cette somme.

3. Une gestion explicite du seuil `176`.

La difficulté n’est pas conceptuelle mais **effective** : il faut une borne suffisamment forte pour tous les `N ≥ 176`, ou bien une combinaison :

```text
preuve analytique pour N ≥ N₀
+
vérification finie pour 176 ≤ N < N₀
```

Donc C-04a est probablement prouvable, mais il faut un vrai module de borne effective. Ce n’est pas seulement un branchement à C-03.

## Addendum v38.5.11 — statut de C-04b

La section C-04b de cette note a été retirée car le verrou correspondant est désormais fermé dans le dépôt.

Le statut canonique est documenté dans :

```text
docs/notes-techniques/SquarefreeDensity_C04b_v38.5.11.md
```

Résumé :

```text
C-04b densité 6 / π² : [D] prouvé via SquarefreeDensityC04bClosed
C-04a minoration N/2 : conditional bridge / ouvert
RHClaimed            : false
```

Cette note reste donc pertinente uniquement pour la dette restante C-04a.
