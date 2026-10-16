module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FiniteAveragedForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.PeriodClassCocycle

@[expose] public section


/-!
# The finite average of the scalar weighted realization

Let `F = F_v` be the scalar weighted realization of a spherical smooth vector `v`. At a real point
`g` the averaged integrand `w(f) F(b(f) g, z)` is `(Im z)^k` times the `p`-adic good-line
integrand of the spherical vector `π(g σ(z)) v`, where `σ(z)` is the affine section of `z`. Hence
it is continuous in the finite pair, the averaged form at the real component inherits the Eichler
data of `F`, and, for a classical vector `v`, the averaged form at real points is the scalar
weighted realization of the classical finite average `w` of `v` at `s = n/2 + 3 + s₀`. Since `F`
is left `GL₂(ℚ)`-invariant and right `GL₂(Ẑ)`-invariant, its average is invariant under left
translation by real integral matrices at real points.

The scalar weighted realization of a classical vector has the Eichler data as soon as it is
holomorphic at every adelic base point.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

section Spherical

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)

include spherical in
/-- **The averaged integrand at a real point** is a `p`-adic good-line integrand. -/
theorem cuspScalar_averagedIntegrand_eq (g : BinaryRealGL) (z : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        cuspScalarWeightedRealization cusp halfWeight vector
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) z =
      ((z.im ^ halfWeight : ℝ) : ℂ) * goodLineFinitePadicIntegrand cusp
        (cuspSmoothAction cusp (atInfinity (g * invertibleMatrix (binaryUpperSectionMatrix z)))
          vector) ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite := by
  rw [← goodLineFinitePadicIntegrand_eq n cusp cohomologicalPoint _
    (cuspSmoothAction_real_spherical cusp vector spherical _) finite, cuspSmoothAction_realize,
    atInfinity_mul]
  simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization, Complex.real_smul,
    mul_assoc]
  ring

include spherical in
/-- The averaged integrand at a real point is continuous in the finite pair. -/
theorem cuspScalar_averagedIntegrand_continuous (g : BinaryRealGL) (z : ℂ) :
    Continuous fun finite : FiniteAwayThree × FiniteAwayThree =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        cuspScalarWeightedRealization cusp halfWeight vector
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) z := by
  simp only [cuspScalar_averagedIntegrand_eq cusp halfWeight vector spherical]
  exact continuous_const.mul (goodLineFinitePadicIntegrand_continuous cusp _
    (cuspSmoothAction_real_spherical cusp vector spherical _) _)

include spherical in
/-- **The averaged scalar weighted realization at the real component has the Eichler data** if
the scalar weighted realization has. -/
theorem EichlerData.averagedReal_cuspScalar (large : 3 < n)
    (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector)) :
    EichlerData n (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)) :=
  hF.averagedReal large fun g z _ =>
    (cuspScalar_averagedIntegrand_continuous cusp halfWeight vector spherical g
      z).aestronglyMeasurable

include spherical in
/-- **Invariance of the averaged scalar weighted realization under real integral Levi
translations** at real points. -/
theorem averagedForm_cuspScalar_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (z : ℂ) :
    averagedForm n (cuspScalarWeightedRealization cusp halfWeight vector)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g) z =
      averagedForm n (cuspScalarWeightedRealization cusp halfWeight vector) (atInfinity g) z := by
  refine finiteAverageLeft_realLevi _ (fun γ h => ?_) (fun h compact => ?_) γ g
  · simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization, mul_assoc,
      cusp.leftRational]
  · have fixed : (⟨cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding compact)) vector.val,
        cusp.smooth_stable _ _ vector.property⟩ : cusp.smooth) = vector :=
      Subtype.ext (spherical compact)
    simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization]
    rw [mul_assoc, ← (atInfinity_commute_atFinite _ _).eq, ← mul_assoc, ← cusp.equivariant, fixed]

include spherical in
/-- The real-component version of the Levi invariance. -/
theorem averagedRealForm_cuspScalar_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ)
    (g : BinaryRealGL) (z : ℂ) :
    averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g) z =
      averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)
        (atInfinity g) z := by
  rw [← atInfinity_mul, averagedRealForm_atInfinity, averagedRealForm_atInfinity, atInfinity_mul,
    averagedForm_cuspScalar_realLevi cusp halfWeight vector spherical]

end Spherical

/-! ### Identification with the classical finite average -/

/-- **The averaged scalar weighted realization of a classical vector at real points is the scalar
weighted realization of its classical finite average** at `s = n/2 + 3 + s₀`. -/
theorem averagedForm_cuspScalar_atInfinity (large : 3 < n) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cuspClassicalVectors cusp halfWeight)
    (g : BinaryRealGL) (z : ℂ) :
    averagedForm n (cuspScalarWeightedRealization cusp halfWeight vector.val) (atInfinity g) z =
      cuspScalarWeightedRealization cusp halfWeight
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
          ((n : ℂ) / 2 + 3 + cohomologicalPoint) vector).val (atInfinity g) z := by
  have convergent := cohomologicalExponent_re large
  rw [averagedForm_def]
  simp only [cuspScalar_averagedIntegrand_eq cusp halfWeight vector.val vector.property.1]
  rw [integral_const_mul]
  change _ * cuspClassicalFiniteAverage cusp halfWeight _ convergent vector
    (g * invertibleMatrix (binaryUpperSectionMatrix z)) = _
  rw [← realize_cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative _
    convergent vector]
  simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization, Complex.real_smul,
    atInfinity_mul]

/-- The real-component version of the identification. -/
theorem averagedRealForm_cuspScalar_atInfinity (large : 3 < n) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cuspClassicalVectors cusp halfWeight)
    (g : BinaryRealGL) (z : ℂ) :
    averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector.val)
        (atInfinity g) z =
      cuspScalarWeightedRealization cusp halfWeight
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
          ((n : ℂ) / 2 + 3 + cohomologicalPoint) vector).val (atInfinity g) z := by
  rw [averagedRealForm_atInfinity,
    averagedForm_cuspScalar_atInfinity large cusp central_positive halfWeight negative]

/-! ### The Eichler data of the scalar weighted realization -/

/-- **The scalar weighted realization of a vector of rotation weight `-(n + 3)` has the Eichler
data** if it is holomorphic at every adelic base point and the central character is trivial on
positive reals. -/
theorem eichlerData_cuspScalarWeightedRealization (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (weight : 2 * halfWeight = -((n : ℤ) + 3))
    (holomorphic : ∀ h, DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector h)
      {z : ℂ | 0 < z.im}) :
    EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector) where
  holomorphic := holomorphic
  modular := cuspScalarWeightedRealization_modular_weight cusp halfWeight vector rotation weight
  central c positive h z := by
    have commute : ∀ x : BinaryAdelicGL, x * GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit c) =
        GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit c) * x := fun x => by
      apply Units.ext
      exact ((Matrix.scalar_commute ((realAdeleUnit c : Adelesˣ) : Adeles)
        (fun _ => Commute.all _ _) x.val).eq).symm
    simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization]
    rw [atInfinity_scalar, commute, mul_assoc, cusp.central, central_positive c positive, one_mul]
  bounded K subset compact := by
    obtain ⟨bound, nonnegative, bounded⟩ :=
      cuspScalarWeightedRealization_bound cusp halfWeight vector
    obtain ⟨M, hM⟩ := compact.exists_bound_of_continuousOn
      (Complex.continuous_im.continuousOn.zpow₀ halfWeight fun w member =>
        Or.inl (ne_of_gt (subset member)))
    refine ⟨M * bound, fun h w member => ?_⟩
    have value := bounded h ⟨w, subset member⟩
    have power : (w.im ^ halfWeight : ℝ) ≤ M := (le_abs_self _).trans (hM w member)
    exact value.trans (mul_le_mul_of_nonneg_right power nonnegative)

end TernaryPeriodPolynomials.AnalyticClasses
