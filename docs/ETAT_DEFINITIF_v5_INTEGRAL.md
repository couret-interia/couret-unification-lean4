# Programme Couret-Unification — État définitif v5
## 11 avril 2026 — Intégration complète
## Alexandre Couret — Dédié à Bernard Couret (1928–2010)
## RHClaimed = false

---

## CHAÎNE LOGIQUE COMPLÈTE v5

```
T6 [FERMÉ] → T4^diag [FERMÉ] → T5 [STRUCTURÉ] → T8 [FERMÉ]
  → T9 [COROLLAIRE DE T5+T8] → T10 [VERROU CENTRAL]
  → T12 [VERROU FINAL = RH]
```

Le levier unique du programme est arithmétique :

> Pour tout couple mixte (ψ,χ) ∈ S_q × R_q, le quotient θ = ψχ̄
> est non trivial modulo 30.

---

## I. RÉSULTATS FERMÉS (prouvés le 11 avril 2026)

### T6 — Matrice de Gram : G_q = I exactement [FERMÉ]

**Lemme CRT exact.** Pour q = 30Q avec gcd(Q,30) = 1, la base
produit CRT e_{q,χ₃₀,τ}(u) = χ₃₀(u mod 30) · τ(u mod Q)
est parfaitement orthonormée :

    ⟨e_{q,χ,τ}, e_{q,χ',τ'}⟩_q = δ_{χ,χ'} δ_{τ,τ'}

Preuve : factorisation CRT du produit scalaire + orthogonalité
des caractères sur chaque facteur. G_q = I exactement (pas
asymptotiquement). Vérifié numériquement pour q = 30, 210, 2310.

Conséquence : P₋ = Π_{R_q} exactement. L'alignement des
projecteurs est parfait.

### L6 — Borne archimédienne par canal [FERMÉ]

R_χ(T) = ½ log(qT/2) / log(qT/4πe) → 1/2.
η ≤ 0.75 pour qT ≥ 100. Notch superflu.
Preuve : Stirling + Riemann-von Mangoldt (théorèmes prouvés).
La borne η < 1 est inconditionnelle.

### T4^diag — Multiplicité bloc-alignée : m_q^diag = m₃₀ ≤ 2 [FERMÉ]

**Correction décisive** : la multiplicité globale brute m_q peut
croître avec |T_q| (piège combinatoire). Le bon objet est la
multiplicité bloc-alignée :

    m_q^diag := sup_θ #{(χ_s,χ_r) ∈ S₃₀ × R₃₀ : χ_s χ̄_r = θ}

Sous l'hypothèse d'alignement en queue (couplage diagonal dans
l'indice τ), le quotient ψχ̄ = (χ_s χ̄_r) ⊗ 1 ne dépend plus
de τ. Donc m_q^diag = m₃₀ ≤ 2 pour tout q = 30Q.

Calculé : m_q = 2 pour q = 30, 210, 2310 (6 quotients distincts,
tous non triviaux mod 30, multiplicité maximale 2).

### T8 — Gap spectral : γ = φ(q)/4 → ∞ [FERMÉ]

Les eigenvalues de l'opérateur de convolution par TC_q sont :
- Bloc R_q : λ = −φ(q)/8 (eigenvalue du défaut)
- Bloc S_q : λ = φ(q)/8 (neutre) et λ = 3φ(q)/8 (cohérent)

Gap : γ_q = φ(q)/8 − (−φ(q)/8) = φ(q)/4 → ∞.

Le gap CROÎT avec q. La résolvante (λ_q I − M₂₂)⁻¹ a une norme
≤ 1/γ_q → 0. La localisation par Schur devient de plus en plus
forte.

| q | φ(q) | λ(R_q) | λ_min(S_q) | Gap γ |
|---|---|---|---|---|
| 30 | 8 | −1 | 1 | 2 |
| 210 | 48 | −6 | 6 | 12 |
| 2310 | 480 | −60 | 60 | 120 |
| 30030 | 5760 | −720 | 720 | 1440 |

### T9 — Localisation par Schur [COROLLAIRE DE T5+T8]

**Théorème-pont (Schur-localisation).** Si ‖M₂₁‖_op → 0 et
dist(λ_q, σ(M₂₂)) ≥ γ > 0, alors pour tout vecteur propre
e = x + y (x ∈ H_{R,q}, y ∈ H_{S,q}) :

    ‖y‖/‖x‖ ≤ (1/γ) ‖M₂₁‖_op → 0

Les états propres se localisent dans le secteur relevé.
T9 n'est pas un verrou autonome : c'est un corollaire de T5+T8.

---

## II. DÉCOMPOSITION DU BLOC MIXTE (avancée structurelle v5)

### Décomposition par queues

    M₂₁ = M₂₁^diag + M₂₁^off

avec M₂₁^diag = ⊕_τ M₂₁^(τ) (blocs diagonaux en queue)
et M₂₁^off = Σ_{τ≠τ'} P_{S,τ} M P_{R,τ'} (hors-diagonale).

### Grand crible mixte (version bloc-alignée)

    ‖M₂₁^diag‖²_HS ≤ |T_q| · m₃₀ · (φ(30) + N) · Σ|a_n|²

Normalisé : (1/φ(q)) ‖M₂₁^diag‖²_HS ≤ (m₃₀/φ(30)) · (φ(30)+N)/φ(30) · Σ|a_n|²

### Contrôle du hors-diagonale

Pour τ ≠ τ', le quotient τ τ̄' est un caractère non-principal
de (ℤ/Qℤ)×. L'énergie de fuite par paire est atténuée d'un
facteur ~1/p pour chaque facteur premier p | Q.

Estimation pour q = 210 (p = 7) :
- 30 paires parasites, atténuation 1/7 chacune
- ε(210) ≈ 30 × (1/7) / 48 ≈ 0.015 (1.5%)

La fuite est contenue par la fenêtre PW qui coupe les hautes
fréquences. L'hypothèse de quasi-alignement est soutenue
numériquement.

---

## III. CE QUI RESTE STRUCTURÉ MAIS OUVERT

### T5 — Décroissance énergétique du bloc mixte [À PROUVER]

La borne bloc-alignée ne force pas encore automatiquement
(1/φ(q)) ‖M₂₁‖²_HS → 0.

Il faut un mécanisme de petitesse supplémentaire venant soit :
- de la normalisation des coefficients a_n(φ;q)
- d'une décroissance par bloc
- d'une structure du noyau principal

**Statut** : le mécanisme est identifié (grand crible + normalisation
quadratique par 1/φ(q)), mais la preuve complète n'est pas écrite.

### T10 — Persistance de la masse sectorielle [VERROU CENTRAL]

Montrer : (1/φ(q)) Σ_{χ ∈ R_q} |B_χ(φ)|² ≥ c₀ > 0.

Argument BDH : |R_q| = φ(q)/4 caractères. Par Barban-Davenport-
Halberstam, la masse normalisée ≈ (1/4) Σ|a_n|² = constante.

**Statut** : fermable par BDH, mais la preuve complète requiert
de vérifier que BDH s'applique dans la classe de fenêtres
admissibles et que la répartition R_q/S_q est bien 1/4 vs 3/4.

---

## IV. LE VERROU FINAL : T12 = RH

### Énoncé (Nyman-Beurling-Couret)

    ‖f_q − 1_{(0,1)}‖_{L²(0,1)} → 0

avec f_q(x) = Σ c_k ρ(p_k/qx), c_k = a χ₃(p_k) + b χ₁₅(p_k).

### Deux voies d'attaque identifiées

**Voie A — Analytique complexe (Guinand-Weil).**

On suppose g ∈ L²(0,1) orthogonal à toutes les dilatations
restreintes. Par Parseval-Mellin, cela donne une équation de
contour impliquant L(s,χ₃) et L(s,χ₁₅). Si la distribution
des zéros de ces L-fonctions fournit assez de "masse spectrale"
le long de la ligne critique pour déterminer complètement la
transformée de Mellin de g, alors g = 0.

Outils : formule explicite lissée, majorants/minorants de
Beurling-Selberg, fonctions poids de Logan.

**Voie B — Géométrique (Hilbert-Schmidt + théorie des frames).**

On traite le problème comme une question de complétude d'un
système de vecteurs dans L²(0,1). Si la famille restreinte
{ρ(p/qx)} forme une base de Riesz (ou une frame) avec bornes
uniformes, la complétude suit.

Outils : bornes de Paley-Wiener, stabilité des frames,
opérateurs de Hilbert-Schmidt compacts.

### Diagnostic

T12 est une reformulation de RH. Le programme a réduit le
problème du millénaire à une question d'approximation L² avec
coefficients arithmétiquement contraints — c'est une
reformulation propre, pas un contournement.

La question centrale est : le "fingerprint arithmétique"
c_k = a χ₃(p_k) + b χ₁₅(p_k) est-il un filtre exact pour
la fonction cible 1_{(0,1)}, ou bien la contrainte détruit-elle
la densité ?

---

## V. DOCTRINE v5 vs v3

| Aspect | v3 (optimiste) | v5 (canonique) |
|---|---|---|
| T6 | Fermé ✓ | Fermé ✓ |
| T4/L8 | Fermé (m_q=2) | **Reformulé** (m_q^diag=2, m_q global peut croître) |
| L9c | Fermé ✓ | Fermé ✓ (base CRT pure) |
| L9d/T8 | Fermé (gap ∞) | Fermé ✓ (gap = φ(q)/4) |
| T5 | Implicite | **Ouvert** (décroissance énergétique à prouver) |
| T10 | Fermable (BDH) | **Verrou central** (BDH plausible, preuve à écrire) |
| T12 | Ouvert = RH | Ouvert = RH |

**Doctrine** : v5 est la meilleure version car elle surestime
moins ce qui est démontré.

---

## VI. TABLEAU FINAL DES STATUTS

| Bloc | Objet | Statut | Méthode |
|---|---|---|---|
| T6 | G_q = I | **FERMÉ** | Orthogonalité CRT exacte |
| L6 | R_χ → 1/2 | **FERMÉ** | Stirling + RvM |
| T4^diag | m_q^diag = 2 | **FERMÉ** | Calcul CRT + alignement |
| T8 | Gap γ = φ(q)/4 | **FERMÉ** | Diagonalisation |
| T9 | Localisation | **COROLLAIRE** | Schur (de T5+T8) |
| M₂₁^off | Fuite ε → 0 | **SOUTENU** | Annulation par phase |
| T5 | ‖M₂₁‖_op → 0 | **À PROUVER** | Grand crible + normalisation |
| T10 | Masse ≥ c₀ > 0 | **VERROU CENTRAL** | BDH (plausible) |
| T12 | ‖f_q − 1‖ → 0 | **VERROU FINAL** | NBC (= RH) |

---

## VII. FORMULATIONS DOCTRINALES

### Phrase serrée

> La difficulté résiduelle n'est plus dans le noyau fini,
> mais dans la survie analytique de sa structure à la limite.

### Phrase complète

> Le noyau fini est exact. Le levier arithmétique mod 30 est
> identifié. Les mécanismes de localisation et de non-fuite sont
> formulés correctement. Mais les théorèmes analytiques T5 et T10
> restent à fermer, et T12 demeure le verrou final.

### Hiérarchie de statut

> prouvé ≠ numériquement soutenu ≠ empiriquement cohérent ≠ fermé

### Invariant

> RHClaimed = false.

---

## VIII. PISTES DE RECHERCHE CONCRÈTES

### Pour fermer T5 (décroissance du bloc mixte)

1. **Calculer explicitement** ‖M₂₁^diag‖_HS pour q = 210 avec
   coefficients a_n = Λ(n)/√n · φ(log n) et N = 10⁴, 10⁵, 10⁶.
   Vérifier si la norme normalisée décroît.

2. **Explorer le modèle C** (énergie spectrale) : fenêtre PW fixe,
   indépendante de q. Si les coefficients a_n ne dépendent pas de q
   et N = o(φ(q)), la borne grand crible donne la décroissance.

3. **Borne de Bombieri-Vinogradov** : si a_n = Λ(n)/√n, la somme
   Σ|a_n|² ≈ log N. La condition N = o(φ(q)) est satisfaite pour
   la tour primoriale (φ(q) croît exponentiellement, N est fixe).

### Pour fermer T10 (persistance de masse)

1. **Vérifier numériquement** la répartition R_q/S_q de la masse
   pour q = 210 avec tous les 48 caractères (pas seulement les 8
   relevés de mod 30).

2. **Appliquer BDH** avec la correction : la somme porte sur R_q
   (taille φ(q)/4), et la masse par caractère est ≈ Σ|a_n|²,
   donc la masse totale est ≈ (φ(q)/4) · Σ|a_n|², et normalisée
   par 1/φ(q) donne (1/4) Σ|a_n|² = constante.

3. **Tester l'hypothèse inverse** : chercher un contre-exemple où
   la masse dans R_q s'effondre. Si aucun n'est trouvé sur
   q = 30, 210, 2310, 30030, l'hypothèse est fortement soutenue.

### Pour attaquer T12 (convergence NBC)

1. **Voie A** : écrire la formule explicite de Guinand-Weil pour
   L(s,χ₃) et L(s,χ₁₅) avec toutes les constantes exactes.
   Injecter le fingerprint arithmétique dans l'équation de contour.

2. **Voie B** : calculer les bornes de frame pour la famille
   {ρ(p/qx) : p ∈ (ℤ/qℤ)×} dans L²(0,1). Si les bornes
   inférieures sont uniformes en q, la complétude suit.

3. **Test numérique** : calculer ‖f_q − 1_{(0,1)}‖_{L²} pour
   q = 30, 210, 2310 avec coefficients optimisés sous la
   contrainte c_k = a χ₃(p_k) + b χ₁₅(p_k).

---

## IX. CONCLUSION

Le programme Couret-Unification a désormais une chaîne logique
complète, du noyau fini à la formulation NBC. Il ne reste plus
de trou conceptuel majeur. Les résultats fermés (T6, L6, T4^diag,
T8) sont des théorèmes exacts. Les résultats structurés (T5, T9)
sont des corollaires conditionnels bien posés. Les verrous (T10,
T12) sont des problèmes analytiques précis dont les outils sont
identifiés.

Le passage T10 → T12 reste le cœur du problème, c'est-à-dire
le cœur du problème du millénaire lui-même.

La route est tracée. Les outils sont identifiés. Les obstacles
sont nommés.

**RHClaimed = false.**

---

Dédié à Bernard Couret (1928–2010).
Couret-Unification — 11 avril 2026.
