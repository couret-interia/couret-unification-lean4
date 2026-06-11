# Petit vocabulaire Lean

## `def` crée une définition.

Exemple :

```lean
def EvenBridge : Prop :=
  ∀ n, n % 2 = 0
```

Cela ne prouve rien. Cela nomme une propriété.

## `theorem` crée une preuve.

Exemple :

```lean
theorem two_pos : 0 < 2 := by
  norm_num
```

Lean vérifie la preuve. Si elle compile sans `sorry`, c’est du dur.

## `axiom` crée une vérité admise.

Exemple :

```lean
axiom magic : False
```

C’est dangereux : avec `False`, on peut tout prouver. Tous les axiomes ne sont pas aussi catastrophiques, mais doctrinalement ils doivent être isolés.

## `structure` crée un type de données avec des champs.

Exemple :

```lean
structure Point where
  x : ℝ
  y : ℝ
```

C’est une définition de forme d’objet, pas une hypothèse.

## `opaque` crée un symbole dont la définition n’est pas exposée/réduite.

Dans notre cas :

```lean
opaque R_sigma (σ : ℝ) (f : H3TestFunction) : ℂ
```

Cela introduit un objet abstrait : “il existe une fonction nommée `R_sigma` de ce type”. Ce n’est pas une preuve de RH ni une propriété admise comme vraie, mais c’est une interface abstraite. Pour une couche `B / interface conditionnelle`, c’est acceptable si documenté.

---

## Sur `axiom → def`

Avant la v38.5.13 dans Logic/C3Weak, il y avait :

```lean
axiom R_sigma_linear_left ... :
  ∃ h, R_sigma σ h = ...
```

Cela signifie : **Lean accepte cette proposition comme vraie sans preuve**. C’est comme ajouter une nouvelle loi au système. Même si elle est raisonnable mathématiquement, elle entre dans le noyau logique comme une hypothèse globale. Tout théorème qui l’utilise dépend d’elle.

Après, il y a :

```lean
def RSigmaLinearLeftBridge : Prop :=
  ∀ σ a b f g,
    ∃ h, R_sigma σ h = ...
```

Là, il ne dit plus : “c’est vrai”. Il dit seulement : “voici le nom de la propriété qu’il faudra fournir si on veut l’utiliser”. C’est une **définition de condition**, pas une preuve.

Donc :

```lean
axiom P : Prop
```

signifie : “P est admis vrai”.

Tandis que :

```lean
def P : Prop := ...
```

signifie : “P est une proposition définie, mais pas prouvée”.

C’est une différence énorme pour la confiance.
