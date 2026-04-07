import CouretUnification.Core.TripletLocalExceptionalCandidate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Prédicat minimal de candidature exceptionnelle locale pour un triplet arbitraire :

un triplet est dit localement exceptionnel s’il admet
un `TripletLocalExceptionalCandidate`.

On n’ouvre encore :
- aucun filtrage global,
- aucune classification des 21 triplets,
- aucun `ExceptionalFilter`.
-/
def isLocalExceptionalCandidate (T : Triplet) : Prop :=
  Nonempty (TripletLocalExceptionalCandidate T)

/--
Introduction canonique du prédicat à partir d’un candidat local déjà empaqueté.
-/
theorem TripletLocalExceptionalCandidate.isExceptionalPredicate
    {T : Triplet} (E : TripletLocalExceptionalCandidate T) :
    isLocalExceptionalCandidate T := by
  exact ⟨E⟩

/--
Élimination minimale : le prédicat local fournit bien
un candidat local empaqueté.
-/
theorem isLocalExceptionalCandidate_hasWitness
    {T : Triplet} (h : isLocalExceptionalCandidate T) :
    ∃ _ : TripletLocalExceptionalCandidate T, True := by
  rcases h with ⟨E⟩
  exact ⟨E, trivial⟩

/--
Dépliage structuré du prédicat :
à partir de la candidature exceptionnelle locale,
on récupère :
- un certificat harmonique,
- un spectre documentaire candidat,
- le recollement harmonique/documentaire historique,
- le recollement quadratique harmonique/documentaire,
- l’intégralité harmonique minimale,
- l’intégralité finie documentaire,
- le critère brut d’intégralité harmonique.
-/
theorem isLocalExceptionalCandidate_unpacked
    {T : Triplet} (h : isLocalExceptionalCandidate T) :
    ∃ H : HarmonicCertificate T,
      ∃ S : FiniteSpectrum,
        tripletFourier T = H.coeffs
          ∧ matchesHistoricalSpectrum T S
          ∧ tripletPowerSpectrum T =
              S.powerHistorical.map (fun n => (n : ℝ))
          ∧ certificateHasIntegralEntries H
          ∧ hasIntegralSpectrum S
          ∧ hasRawIntegralCriterion T := by
  rcases h with ⟨E⟩
  refine ⟨E.quadraticIntegral.quadratic.candidate.documentary.harmonic,
          E.quadraticIntegral.quadratic.candidate.documentary.candidate,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.quadraticIntegral.quadratic.candidate.documentary.harmonic.realizes
  · exact E.matchesHistorical
  · exact E.realizesPower.symm.trans E.matchesHistoricalPower
  · exact E.harmonicIntegral
  · exact E.documentaryIntegral
  · exact E.rawIntegral

/--
Cas Couret : le triplet distingué vérifie bien le prédicat
de candidature exceptionnelle locale.
-/
theorem couretTriplet_isLocalExceptionalCandidate :
    isLocalExceptionalCandidate couretTriplet := by
  exact ⟨couretTripletLocalExceptionalCandidate⟩

/--
Version spécialisée : le cas Couret fournit bien tous les témoins locaux attendus.
-/
theorem couretTriplet_isLocalExceptionalCandidate_unpacked :
    ∃ H : HarmonicCertificate couretTriplet,
      ∃ S : FiniteSpectrum,
        tripletFourier couretTriplet = H.coeffs
          ∧ matchesHistoricalSpectrum couretTriplet S
          ∧ tripletPowerSpectrum couretTriplet =
              S.powerHistorical.map (fun n => (n : ℝ))
          ∧ certificateHasIntegralEntries H
          ∧ hasIntegralSpectrum S
          ∧ hasRawIntegralCriterion couretTriplet := by
  exact isLocalExceptionalCandidate_unpacked
    couretTriplet_isLocalExceptionalCandidate

/--
Validation groupée minimale du cas Couret au niveau du prédicat :
- existence d’une candidature exceptionnelle locale,
- extraction de tous les témoins minimaux associés.
-/
theorem couretTripletExceptionalPredicate_valid :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTriplet_isLocalExceptionalCandidate

end

end CouretUnification.Core