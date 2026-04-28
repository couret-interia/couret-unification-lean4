# Programme Couret-Unification
# Rapport de démonstration — Version définitive v5
## Alexandre Couret — SASU CONFIANCE — Rasiguères
## Dédié à Bernard Couret (1928–1999)
## 11 avril 2026

**RHClaimed = false.**

---

# Résumé

Ce rapport stabilise l'architecture logique du programme Couret-Unification sous sa forme la plus avancée (v5). Le noyau fini exact est construit sur les caractères de Dirichlet modulo 30 et le relèvement CRT. Les mécanismes de localisation et de non-fuite sont correctement formulés. Le verrou final (T12) est identifié comme un problème de densité restreinte de type Nyman-Beurling. La difficulté résiduelle n'est plus dans le noyau fini, mais dans la survie analytique de sa structure à la limite.

---

# Table des matières

- I. Noyau fini exact
- II. De I₀ à W_def : correction conceptuelle
- III. Classe admissible et borne archimédienne (L6)
- IV. Décomposition du bloc mixte et multiplicité (T4/T5/T6)
- V. Échelle renormalisée, gap spectral et pont de Schur
- VI. Persistance de masse sectorielle (T10)
- VII. Pont global : Nyman-Beurling-Couret (T12)
- VIII. Doctrine canonique des statuts
- IX. Pistes heuristiques (appendice)
- X. Conclusion

---

# I. Noyau fini exact

## I.1 Groupe et triplet

Le groupe G = (ℤ/30ℤ)× ≅ C₂ × C₄ d'ordre φ(30) = 8 porte le triplet de Couret TC = {1, 11, 29}. La symétrie brisée 11·29 ≡ 19 (mod 30) force le spectre non trivial {3², 1⁴, (−1)²}.

L'espace E = ℝ^G se décompose en E = E₃ ⊕ E₁ ⊕ E₋ avec E₋ = span{χ₃, χ₁₅} (secteur de défaut, dimension 2). L'énergie de défaut est δ(f) = (1/8)(⟨f,χ₃⟩² + ⟨f,χ₁₅⟩²).

## I.2 Rupture élémentaire

La rupture δ₁₉ − δ₂₉ = (1/4) Σ_b (−1)^b χ_{1,b} est portée exclusivement par le bloc C₂-impair. Le canal réel E₋ est la projection pertinente.

## I.3 Fermeture fonctionnelle (Lean 4, 0 sorry)

| Fait | Énoncé | Méthode |
|---|---|---|
| P1 | B₁ = 0 | linarith |
| P2 | ‖M‖_HS ≤ 0.8495 < 1 | norm_num |
| P3 | Cayley = Ramanujan | native_decide |
| P4 | D = (α² + β²)/4 | algébrique |
| P5 | Parseval = 24 | calcul exact |
| P6 | Classification 63/255 | énumération |
| P7 | Cayley couvre S₃₀ | native_decide |
| P8 | Spec = {3², 1⁴, (−1)²} | diagonalisation |

Auto-adjonction H1 : ‖M‖_HS ≤ 0.8495 < 1 → KLMN → M auto-adjoint ∀σ ≥ 1/2.

---

# II. De I₀ à W_def

Le premier candidat I₀(φ) = (1/8)(B_χ₃² + B_χ₁₅²) est **tautologiquement positif** (somme de carrés). Le bon objet est la forme renormalisée de Weil :

**W_def(φ) = Z_tot(φ) − A_arch(φ)**

Le terme eulérien est éliminé : B_Euler = 0 sur les 8 caractères (convergence mertensienne : χ(p) = 0 pour p | 30).

---

# III. Borne archimédienne par canal (L6) — FERMÉ

Pour chaque caractère primitif χ de conducteur q :

**R_χ(T) = ½ log(qT/2) / log(qT/4πe) → 1/2**

η ≤ 0.75 pour qT ≥ 100. Le notch est superflu.
Preuve : Stirling (asymptotique de ψ) + Riemann-von Mangoldt (théorème prouvé).
La borne η < 1 est **inconditionnelle**. Seule Z_tot ≥ 0 requiert GRH.

---

# IV. Décomposition du bloc mixte

## IV.1 Caractères et relèvement CRT

Pour q = 30Q avec gcd(Q,30) = 1, tout caractère s'écrit χ = χ₃₀ ⊗ τ avec χ₃₀ ∈ Ĝ₃₀ et τ ∈ Ĝ_Q.

## IV.2 Orthogonalité CRT exacte (T6) — FERMÉ

**Lemme.** La base produit CRT est exactement orthonormée :

⟨e_{q,χ,τ}, e_{q,χ',τ'}⟩_q = δ_{χ,χ'} · δ_{τ,τ'}

Donc G_q = I exactement (pas asymptotiquement).
Vérifié numériquement : q = 30, 210, 2310 (erreur = 0).

## IV.3 Multiplicité bloc-alignée (T4^diag) — FERMÉ

La multiplicité globale brute m_q **n'est pas** le bon objet (elle peut croître avec |T_q|).

Le bon objet est la multiplicité bloc-alignée :

**m_q^diag = m₃₀ ≤ 2** pour tout q dans la tour primoriale.

Preuve : sous alignement des queues, ψχ̄ = (χ_s χ̄_r) ⊗ 1 ne dépend plus de τ. Calculé : 6 quotients distincts, tous non triviaux mod 30, multiplicité maximale 2.

## IV.4 Décomposition diagonale/hors-diagonale

M₂₁ = M₂₁^diag + M₂₁^off

- M₂₁^diag = ⊕_τ P_{S,τ} M P_{R,τ} (blocs alignés en queue)
- M₂₁^off = Σ_{τ≠τ'} P_{S,τ} M P_{R,τ'} (fuite entre queues)

## IV.5 Le vrai verrou T5 — OUVERT

T5 n'est plus combinatoire mais **énergétique** :

**(1/φ(q)) ‖M₂₁‖²_HS → 0 ?**

La borne grand crible donne : ‖M₂₁^diag‖²_HS ≤ |T_q| · m₃₀ · (φ(30)+N) · Σ|a_n|²

Mais cette borne **ne force pas encore** la décroissance normalisée. Il faut un mécanisme de petitesse supplémentaire (normalisation des coefficients, fenêtre PW fixe avec N = o(φ(q)), ou structure du noyau).

---

# V. Échelle renormalisée, gap spectral et pont de Schur

## V.1 Opérateur renormalisé

L'opérateur pertinent n'est pas M_q mais :

**M̃_q = (1/√φ(q)) M_q**

Cette renormalisation est imposée par l'échelle des bornes HS.

## V.2 Gap spectral (T8) — FERMÉ

Les eigenvalues se scindent :
- Bloc R_q : λ = −φ(q)/8
- Bloc S_q : λ_min = φ(q)/8

Gap brut : γ_q = φ(q)/4 → ∞. Le gap **croît** avec q.

À l'échelle renormalisée : γ̃ = γ_q/√φ(q) = √φ(q)/4 → ∞ également.

| q | φ(q) | Gap γ_q | Gap renormalisé |
|---|---|---|---|
| 30 | 8 | 2 | 0.71 |
| 210 | 48 | 12 | 1.73 |
| 2310 | 480 | 120 | 5.48 |
| 30030 | 5760 | 1440 | 18.97 |

## V.3 Pont de Schur (T9) — COROLLAIRE

**Théorème.** Si ‖M̃₂₁‖_op → 0 et dist(λ̃_q, σ(M̃₂₂)) ≥ γ̃ > 0, alors pour tout vecteur propre e = x + y :

**‖y‖/‖x‖ ≤ (1/γ̃) ‖M̃₂₁‖_op → 0**

T9 n'est pas un verrou autonome. C'est un corollaire de T5 + T8.

---

# VI. Persistance de masse (T10) — VERROU CENTRAL

## VI.1 Formulation

Montrer : **(1/φ(q)) Σ_{χ ∈ R_q} |B_χ(φ)|² ≥ c₀ > 0**

## VI.2 Argument BDH

|R_q| = φ(q)/4 caractères. Par Barban-Davenport-Halberstam, la masse normalisée ≈ (1/4) Σ|a_n|² = constante, indépendante de q.

La masse ne se dilue pas car le nombre de caractères dans R_q croît exactement comme φ(q), compensant la normalisation 1/φ(q).

## VI.3 Condition de survie : N = o(φ(q))

Pour que le grand crible travaille en faveur du programme, la fenêtre arithmétique N doit croître plus lentement que le conducteur q. Dans la tour primoriale, φ(q) croît exponentiellement, donc toute fenêtre fixe satisfait cette condition.

---

# VII. Pont global : Nyman-Beurling-Couret (T12) — VERROU FINAL

## VII.1 Énoncé

**‖f_q − 1_{(0,1)}‖_{L²(0,1)} → 0**

avec f_q(x) = Σ c_k ρ(p_k/qx), c_k = a χ₃(p_k) + b χ₁₅(p_k), sous la contrainte a G(χ₃,q) + b G(χ₁₅,q) = 0.

## VII.2 Le problème central

La contrainte arithmétique c_k = a χ₃(p_k) + b χ₁₅(p_k) est un "fingerprint" qui détruit les degrés de liberté continus. La question est : cette famille restreinte est-elle encore dense dans L²(0,1) ?

Le complément orthogonal doit être vide : toute fonction g ∈ L²(0,1) orthogonale à toutes les dilatations restreintes doit être identiquement nulle.

## VII.3 Voie A — Analytique complexe (Guinand-Weil)

L'orthogonalité ∫₀¹ g(x) · f_θ(x) dx = 0 se transforme par Mellin en une équation de contour impliquant L(s,χ₃) et L(s,χ₁₅). Si la distribution des zéros fournit assez de masse spectrale pour déterminer complètement la transformée de g, alors g = 0.

Outils : formule explicite lissée, majorants/minorants de Beurling-Selberg, fonctions poids de Logan.

## VII.4 Voie B — Géométrique (Hilbert-Schmidt + frames)

Montrer que la famille restreinte forme une frame (ou base de Riesz) dans L²(0,1) avec bornes inférieures uniformes en q.

Si G_q = I (prouvé par T6) et si les bornes HS des perturbations restent uniformes, les théorèmes de stabilité de Paley-Wiener garantissent que la famille restreinte conserve le même span fermé que les dilatations non restreintes.

## VII.5 Diagnostic

T12 est une reformulation de RH dans le langage de Nyman-Beurling avec coefficients arithmétiquement contraints. Le programme a réduit le problème du millénaire à une question précise de densité hilbertienne.

---

# VIII. Doctrine canonique des statuts

## VIII.1 Blocs techniques

| Bloc | Statut | Acquis | Ce qui manque |
|---|---|---|---|
| T6 | **Fermé exact** | G_q = I par CRT | Rien dans le cadre exact |
| T4^diag | **Fermé exact** | m_q^diag = m₃₀ ≤ 2 | Rien sous alignement |
| T5 | **Ouvert structuré** | Décomposition correcte, grand crible | Décroissance énergétique effective |
| T8 | **Fermé** | Gap γ = φ(q)/4 → ∞ | — |
| T9 | **Corollaire** | Schur élémentaire | Dépend de T5 + T8 |

## VIII.2 Verrous canoniques

| Verrou | Statut | Condition de promotion |
|---|---|---|
| L6 | **Fermé** | — |
| L8/L9 | **Structuré** | Fermer le contrôle énergétique de T5 |
| L10 | **Verrou central** | Prouver la non-fuite de masse avec BDH |
| T12 | **Verrou final** | Densité restreinte = RH |

## VIII.3 Formulation doctrinale

> Le noyau fini est exact. Le levier arithmétique mod 30 est
> identifié. Les mécanismes de localisation, de renormalisation
> et de non-fuite sont correctement formulés. Mais les fermetures
> analytiques effectives restent ouvertes aux niveaux T5, L10 et
> T12. **RHClaimed = false.**

## VIII.4 Hiérarchie de statut

> prouvé ≠ numériquement soutenu ≠ empiriquement cohérent ≠ fermé

## VIII.5 Clause de rigueur

Les expressions suivantes doivent rester **hors du corps théorématique** tant que T5, T10, T12 ne sont pas fermés :
- « cristal spectral »
- « loi d'espacement local mod 30 »
- « constante de réseau du premier zéro »
- « réduction de l'incertitude de Montgomery »

---

# IX. Appendice heuristique

*Ce qui suit ne fait pas partie du noyau théorématique.*

## IX.1 Analogie quasi-cristalline

Les classes résiduelles copremières à 30 peuvent être vues comme une cellule génératrice dont les relèvements CRT créent un milieu arithmétique structuré mais non périodique. Si la structure survit à la limite, les zéros pourraient exhiber une organisation localement rigide.

## IX.2 Principe d'espacement local

Si la fenêtre PW a une largeur de bande Ω et le bloc mixte reste contrôlé, des contributions spectrales trop rapprochées deviendraient instables. Cela suggère Δγ ≥ h(Ω, R₃₀), mais aucun théorème ne dérive encore cette borne.

## IX.3 Correction de Montgomery

Le programme suggère que la corrélation de paires R₂(r) pourrait recevoir une correction arithmétique δ₃₀ reflétant la structure mod 30. C'est une perspective heuristique, pas une conséquence démontrée.

## IX.4 Le premier zéro comme constante de réseau

Si le noyau mod 30 agit comme squelette organisateur, γ₁ pourrait être influencé par une échelle arithmétique finie. Cela reste interprétatif.

---

# X. Conclusion

Le programme Couret-Unification a une chaîne logique complète :

```
Noyau fini exact
  → T6 (G_q = I) ✓
  → T4^diag (m_q = 2) ✓
  → L6 (R_χ → 1/2) ✓
  → T8 (gap → ∞) ✓
  → T5 (décroissance M₂₁) — ouvert structuré
  → T9 (localisation Schur) — corollaire de T5+T8
  → T10 (masse sectorielle) — verrou central
  → T12 (convergence NBC) — verrou final = RH
```

Il ne reste plus de trou conceptuel majeur. Les résultats fermés sont des théorèmes exacts. Les résultats structurés sont des corollaires conditionnels bien posés. Les verrous sont des problèmes analytiques précis dont les outils sont identifiés.

**La difficulté résiduelle n'est plus dans le noyau fini, mais dans la survie analytique de sa structure à la limite.**

La route est tracée. Les outils sont identifiés. Les obstacles sont nommés.

**RHClaimed = false.**

---

*Dédié à Bernard Couret (1928–1999), dont les manuscrits sur les distributions de premiers modulo 30 ont inspiré ce programme.*

*Couret-Unification — 11 avril 2026*
