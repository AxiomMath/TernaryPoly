module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Orbit

@[expose] public section


open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers

theorem representative_nonzero_identity {degree : ℕ} (data : InducingData degree)
    (boundaryClass : boundarySummand data .plane) (nonzero : boundaryClass ≠ 0)
    (representative : BadPlaneRepresentative data boundaryClass) :
    ∃ (source : SourceCochain degree), IsSourceCocycle data .plane source ∧
      ∃ vertices : Fin 3 → RealGL3, source vertices 1 ≠ 0 := by
  obtain ⟨source, cycle, cocycle, evaluates, equal, supported⟩ := representative
  refine ⟨source, cocycle, ?_⟩
  by_contra no_value
  push Not at no_value
  have cycle_zero : cycle = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices flag
    obtain ⟨rational, rfl⟩ := QuotientGroup.mk_surjective flag
    by_cases good : GoodFlag .plane (QuotientGroup.mk rational)
    · rw [evaluates]
      have zero := supported
        (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
        rational good 1
      simpa [atInfinity_one] using zero
    · obtain ⟨integral, same_flag⟩ := bad_plane_arithmetic_representative rational good
      let element : rationalLevel := ⟨rationalInclusion integral,
        ⟨integral, rfl⟩⟩
      let translated : Fin 3 → RationalGL3 := fun index => element.val⁻¹ * vertices index
      have moved_flag : element.val⁻¹ • (QuotientGroup.mk rational : Flags .plane) =
          QuotientGroup.mk (1 : RationalGL3) := by
        change (QuotientGroup.mk (element.val⁻¹ * rational) : Flags .plane) =
          QuotientGroup.mk (1 : RationalGL3)
        apply QuotientGroup.eq.mpr
        simpa [element, parabolic] using same_flag
      have equivariant := congrFun (cycle.val.property element translated)
        (QuotientGroup.mk rational)
      change cycle.val.val (fun index => element.val * translated index)
          (QuotientGroup.mk rational) =
        rationalCoefficientComponent degree data.chi element.val
          (cycle.val.val translated (element.val⁻¹ • QuotientGroup.mk rational)) at equivariant
      have vertices_equal : (fun index => element.val * translated index) = vertices := by
        funext index
        simp [translated]
      have identity_zero : cycle.val.val translated
          (QuotientGroup.mk (1 : RationalGL3)) = 0 := by
        rw [evaluates]
        simpa using no_value
          (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (translated index))
      rw [vertices_equal, moved_flag, identity_zero, map_zero] at equivariant
      exact equivariant
  apply nonzero
  apply Subtype.ext
  simpa [cycle_zero] using equal.symm

theorem spherical_of_supported_representative {degree : ℕ} (data : InducingData degree)
    (boundaryClass : boundarySummand data .plane) (nonzero : boundaryClass ≠ 0)
    (representative : BadPlaneRepresentative data boundaryClass) :
    SphericalCusp data.cusp := by
  obtain ⟨source, cocycle, vertices, nonzero_value⟩ :=
    representative_nonzero_identity data boundaryClass nonzero representative
  have nonzero_polynomial : (source vertices 1).val ≠ 0 := by
    intro zero
    apply nonzero_value
    exact Subtype.ext zero
  obtain ⟨monomial, nonzero_coefficient⟩ :
      ∃ monomial, (source vertices 1).val.coeff monomial ≠ 0 := by
    by_contra all_zero
    push Not at all_zero
    apply nonzero_polynomial
    exact MvPolynomial.ext _ _ (by simpa using all_zero)
  exact spherical_of_nonzero_at_identity data
    (fun argument => (source vertices argument).val.coeff monomial)
    (cocycle.1 vertices monomial) nonzero_coefficient

end TernaryPeriodPolynomials.BadPlaneSupportSphericity.Helpers
