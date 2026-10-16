module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalRepresentation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_lifted_cocycle {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth),
      Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
        (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val) ∧
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ finite : level, ∀ matrix monomial,
          cusp.π (atFinite finite.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val) ∧
      (∀ first second, cocycle (first * second) = cocycle first +
        binaryCohomologicalRepresentation cusp degree first (cocycle second)) ∧
      ¬ ∃ vector : BinaryDegreeMonomial (degree + 1) → cusp.smooth,
        ∀ matrix, cocycle matrix = binaryCohomologicalRepresentation cusp degree matrix vector - vector := by
  obtain ⟨original, cuspidal, smooth, level, identity, nontrivial⟩ := cohomological
  have lifts : ∀ matrix, ∃ vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth,
      binaryCuspRealize cusp degree vectors = original matrix := fun matrix =>
    (binaryValues_iff_cuspRealize cusp degree (original matrix)).mp (cuspidal matrix)
  choose cocycle realizes using lifts
  have coefficient (matrix : BinaryRealGL) (argument : BinaryAdelicGL)
      (monomial : BinaryDegreeMonomial (degree + 1)) :
      cusp.realize (cocycle matrix monomial) argument =
        (original matrix argument).val.coeff monomial.val := by
    rw [← realizes matrix]
    exact (binaryCuspRealize_coefficient cusp degree (cocycle matrix) argument monomial).symm
  refine ⟨cocycle, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro monomial
    change Smooth (fun input : Fin 2 → BinaryRealGL =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val)
    obtain ⟨family, family_smooth, family_realizes⟩ := smooth monomial.val
    have equality : (fun input : Fin 2 → BinaryRealGL =>
        (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val) =
          (fun input => (family input).val) := by
      funext input
      apply congrArg Subtype.val
      apply cusp.injective
      funext argument
      rw [show cusp.realize (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)) argument =
          cusp.realize (cocycle (input 0) monomial) (argument * atInfinity (input 1)) from
        cusp.equivariant _ _ _, coefficient, family_realizes]
    rw [equality]
    exact family_smooth
  · obtain ⟨level, open_level, compact_level, fixed⟩ := level
    refine ⟨level, open_level, compact_level, ?_⟩
    intro finite matrix monomial
    have equality : cuspSmoothAction cusp (atFinite finite.val) (cocycle matrix monomial) =
        cocycle matrix monomial := by
      apply cusp.injective
      funext argument
      rw [show cusp.realize (cuspSmoothAction cusp (atFinite finite.val) (cocycle matrix monomial)) argument =
          cusp.realize (cocycle matrix monomial) (argument * atFinite finite.val) from cusp.equivariant _ _ _,
        coefficient, coefficient, fixed]
    exact congrArg Subtype.val equality
  · intro first second
    apply binaryCuspRealize_injective cusp degree
    change binaryCuspRealize cusp degree (cocycle (first * second)) =
      binaryCuspRealize cusp degree (cocycle first + binaryCuspTwistedAction cusp degree first (cocycle second))
    rw [map_add]
    funext argument
    simp only [Pi.add_apply, binaryCuspTwistedAction_realize]
    rw [realizes, realizes, realizes]
    exact identity first second argument
  · rintro ⟨vector, boundary⟩
    apply nontrivial
    refine ⟨binaryCuspRealize cusp degree vector, binaryCuspRealize_values cusp degree vector, ?_⟩
    intro matrix argument
    have equality := congrArg (fun vectors => binaryCuspRealize cusp degree vectors argument) (boundary matrix)
    change binaryCuspRealize cusp degree (cocycle matrix) argument =
      binaryCuspRealize cusp degree (binaryCuspTwistedAction cusp degree matrix vector - vector) argument at equality
    rw [map_sub, Pi.sub_apply, binaryCuspTwistedAction_realize, realizes] at equality
    exact equality

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
