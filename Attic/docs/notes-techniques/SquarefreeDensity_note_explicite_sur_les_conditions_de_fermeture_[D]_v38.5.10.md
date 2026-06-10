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

### Pour C-04b : densité `6 / π²`

Il faut prouver :

```lean
Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
  (nhds (6 / Real.pi^2))
```

Conditions nécessaires :

1. Formule de Möbius :

```text
1_squarefree(n) = ∑_{d² | n} μ(d)
```

2. Réindexation Fubini déjà largement préparée par C-01.

3. Contrôle d’erreur : C-03 donne `O(√N)`, donc après division par `N`, il faut montrer :

```lean
O(√N) / N → 0
```

4. Passage à la limite :

```text
∑_{d ≤ √N} μ(d) / d² → ∑_{d ≥ 1} μ(d) / d²
```

5. Identification eulérienne :

```text
∑ μ(d) / d² = 1 / ζ(2)
```

6. Évaluation classique :

```text
ζ(2) = π² / 6
```

donc :

```text
1 / ζ(2) = 6 / π²
```

La fermeture `[D]` de C-04b dépend donc de deux zones : ton `MoebiusBridge` et une évaluation formelle de `ζ(2)` côté Mathlib/projet.
