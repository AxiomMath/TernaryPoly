module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.HilbertFixedSpace

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_smooth_ne_bot {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) : cusp.smooth ≠ ⊥ := by
  intro zero_space
  have vector_zero (vector : cusp.smooth) : vector = 0 := by
    apply Subtype.ext
    exact (show cusp.smooth ≤ ⊥ from le_of_eq zero_space) vector.property
  obtain ⟨cocycle, values, _, _, _, not_coboundary⟩ := cohomological
  have cocycle_zero (matrix : BinaryRealGL) (argument : BinaryAdelicGL) : cocycle matrix argument = 0 := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    obtain ⟨vector, represents⟩ := values matrix monomial
    have coefficient := congrFun represents argument
    rw [vector_zero vector, map_zero, Pi.zero_apply] at coefficient
    simpa only [Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using coefficient.symm
  apply not_coboundary
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro monomial
    refine ⟨0, ?_⟩
    funext argument
    simp
  · intro matrix argument
    simp [cocycle_zero, binaryCohomologicalAction]

theorem cusp_smooth_dense_of_ne_bot (cusp : CuspidalRepresentation) (nonzero : cusp.smooth ≠ ⊥) :
    Dense (cusp.smooth : Set cusp.H) := by
  have stable (matrix : BinaryAdelicGL) :
      cusp.smooth.topologicalClosure ≤ (cusp.smooth.topologicalClosure).comap (cusp.π matrix) := by
    have original_stable : cusp.smooth.map (cusp.π matrix) ≤ cusp.smooth := by
      rintro vector ⟨preimage, member, rfl⟩
      exact cusp.smooth_stable matrix preimage member
    have mapped := (cusp.smooth.topologicalClosure_map
      (cuspUnitaryAction cusp matrix).toContinuousLinearMap).trans
        (Submodule.topologicalClosure_mono original_stable)
    exact Submodule.map_le_iff_le_comap.mp mapped
  have alternative := cusp.irreducible cusp.smooth.topologicalClosure
    cusp.smooth.isClosed_topologicalClosure (fun matrix vector member => stable matrix member)
  have all : cusp.smooth.topologicalClosure = ⊤ := by
    rcases alternative with zero | all
    · exact False.elim (nonzero (eq_bot_iff.mpr (by simpa [zero] using cusp.smooth.le_topologicalClosure)))
    · exact all
  apply dense_iff_closure_eq.mpr
  change (cusp.smooth.topologicalClosure : Set cusp.H) = Set.univ
  rw [all, Submodule.top_coe]

theorem cohomological_smooth_dense {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) : Dense (cusp.smooth : Set cusp.H) :=
  cusp_smooth_dense_of_ne_bot cusp (cohomological_smooth_ne_bot cohomological)

theorem cohomological_inner_ext {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) {vector : cusp.H}
    (orthogonal : ∀ smoothVector : cusp.smooth, inner ℂ vector smoothVector.val = 0) : vector = 0 := by
  have all : ∀ other : cusp.H, inner ℂ vector other = 0 := by
    intro other
    have closed : IsClosed {other : cusp.H | inner ℂ vector other = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have closure_subset := closure_minimal (fun other member => orthogonal ⟨other, member⟩) closed
    exact closure_subset ((cohomological_smooth_dense cohomological) other)
  exact inner_self_eq_zero.mp (all vector)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
