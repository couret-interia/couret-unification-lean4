import CouretUnification.Finite.Foundations

namespace CouretUnification.Finite

/-!
# Defect — Énergie de défaut du noyau fini

Ce fichier introduit la **notion dérivée de défaut** associée au noyau spectral fini.

## Position dans l’architecture

On se situe ici **au-dessus** de `Finite/Foundations.lean`, mais **en dessous**
des théorèmes certifiés `T1_to_T7` et des couches de type `Criterion`.

Le rôle de ce fichier est simple :

- nommer explicitement l’**énergie portée par le secteur** `λ = -1`,
- fixer une notation stable pour les couches supérieures,
- rendre explicite le lien entre le langage du « défaut »
  et le projecteur spectral `pminus`.

## Lecture conceptuelle

Dans la doctrine spectrale finie adoptée ici :

- `p3` extrait la composante cohérente (`λ = 3`),
- `p1` extrait la composante neutre (`λ = 1`),
- `pminus` extrait la composante de défaut (`λ = -1`).

L’**énergie de défaut** d’un signal `f` est donc, par définition,
la norme quadratique de sa composante `pminus f`.

Aucune hypothèse analytique n’intervient ici :
il s’agit d’un objet **fini, exact, purement spectral**.
-/

-- ═══════════════════════════════════════════════════════════
-- Énergie de défaut
-- ═══════════════════════════════════════════════════════════

/--
Énergie de défaut finie portée par le secteur spectral `λ = -1`.

Autrement dit, `defectEnergy f` mesure exactement la masse quadratique
de la composante `pminus f`.
-/
def defectEnergy (f : Sig) : ℚ := normSq (pminus f)

/--
Le défaut fini est, par définition, la norme quadratique
de la projection de `f` sur le secteur `λ = -1`.

Ce théorème sert de point d’ancrage pour les couches supérieures
(`FiniteDefect`, `Criterion`), où cette quantité reçoit une
interprétation plus conceptuelle.
-/
theorem defect_extends_finite (f : Sig) :
    defectEnergy f = normSq (pminus f) := rfl

end CouretUnification.Finite