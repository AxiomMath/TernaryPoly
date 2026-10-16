module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightWeakKernels
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineDerivativeLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCauchyRiemannRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cohomological_holomorphic_or_regularity_obstruction (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree) :
    (∃ (halfWeight : ℤ) (vector : cusp.smooth), 2 * halfWeight = -((degree : ℤ) + 3) ∧
      vector ≠ 0 ∧ vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val) UpperHalfPlane.upperHalfPlaneSet) ∨
    ∃ (level : Subgroup BinaryFiniteGL) (vector : cusp.H),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      vector ∈ cuspHilbertWeightValues cusp level (degree + 1 : ℕ) ∧
      DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
      vector ∉ cuspAffineSmoothValues cusp ∧
      cuspRaisingVector cusp (degree + 1 : ℕ) vector ∈ cuspAffineSmoothValues cusp := by
  obtain ⟨level, level_open, level_compact, alternatives⟩ :=
    cohomological_extremal_or_analytic_obstruction cusp spherical cohomological
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  obtain ⟨index, degree_eq⟩ := odd
  let halfWeight : ℤ := (index : ℤ) + 2
  have weight_eq : ((degree + 1 : ℕ) : ℤ) + 2 = 2 * halfWeight := by
    dsimp [halfWeight]
    omega
  have negative_eq : -2 - ((degree + 1 : ℕ) : ℤ) = 2 * (-halfWeight) := by omega
  have target_eq : 2 * (-halfWeight) = -((degree : ℤ) + 3) := by omega
  rcases alternatives with ⟨vector, nonzero, member, killed⟩ | ⟨vector, nonzero, member, annihilates⟩ |
    ⟨vector, member, differentiable, not_smooth, raised_smooth⟩
  · left
    have value_nonzero : vector.val ≠ 0 := fun equality => nonzero (Subtype.ext equality)
    have rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • vector.val := by
      simpa only [negative_eq] using member.2
    have raising_zero : cuspRaisingVector cusp (2 * (-halfWeight)) vector.val = 0 := by
      have equality := congrArg Subtype.val killed
      change cuspRaisingVector cusp (-2 - (degree + 1 : ℕ)) vector.val = 0 at equality
      simpa only [negative_eq] using equality
    obtain ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩ :=
      cusp_exists_spherical_smooth_raising_zero cusp spherical central_positive vector.val (-halfWeight)
        value_nonzero rotation vector.property raising_zero
    exact ⟨-halfWeight, result, target_eq, result_nonzero, fixed, rotation, killed, holomorphic⟩
  · left
    obtain ⟨result, result_nonzero, fixed, rotation, killed, holomorphic⟩ :=
      cuspWeightWeakLoweringKernel_exists_spherical cusp spherical central_positive level level_open level_compact
        (degree + 1 : ℕ) halfWeight weight_eq vector nonzero member annihilates
    exact ⟨-halfWeight, result, target_eq, result_nonzero, fixed, rotation, killed, holomorphic⟩
  · exact Or.inr ⟨level, vector, level_open, level_compact, member, differentiable, not_smooth, raised_smooth⟩

/-- The actual nonzero cohomology class supplies an exact spherical holomorphic vector. -/
theorem cohomological_exists_spherical_holomorphic (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree) :
    ∃ (halfWeight : ℤ) (vector : cusp.smooth), 2 * halfWeight = -((degree : ℤ) + 3) ∧
      vector ≠ 0 ∧ vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val) UpperHalfPlane.upperHalfPlaneSet := by
  rcases cohomological_holomorphic_or_regularity_obstruction cusp spherical odd cohomological with result | obstruction
  · exact result
  · obtain ⟨_, vector, _, _, _, differentiable, not_smooth, raised_smooth⟩ := obstruction
    obtain ⟨index, degree_eq⟩ := odd
    have weight_eq : ((degree + 1 : ℕ) : ℤ) = 2 * ((index : ℤ) + 1) := by omega
    rw [weight_eq] at raised_smooth
    exact False.elim (not_smooth (cuspAffineOrbitVector_contDiffOn_of_raising_smooth cusp ((index : ℤ) + 1)
      vector differentiable raised_smooth))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
