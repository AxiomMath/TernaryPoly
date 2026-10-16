module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstantTermComparison
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LineFactorization

@[expose] public section


/-!
# The real torus average of the defect translation family vanishes

Let `g` be an integral flag representative and `q` its rational image. For either stratum, the
real translation family `r ↦ (E c - c_side)(y)(u(3 r) q⁻¹)` of `Basic.lean` has zero average over
the unit square, after applying any linear functional on the coefficient space. The proof
reduces to coefficients of the polynomial coordinates: the Eisenstein coefficient is a
continuous, left rationally invariant and right `finiteLevel`-invariant function, whose real
average over the square equals its adelic average over the radical domain (scaling by three
removes the finite part), and the adelic average is the constant term of the Eisenstein series,
which is `c` on the plane stratum and `J c` on the line stratum.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (realPlaneUnitMeasure planeDomainMeasure planeDomainMeasure_eq
    planeDomain_integral_real_projection radical_periodic_integral_rational_scaling
    scalar_plane_constant_term atInfinity_planeUnipotent planeUnipotent_continuous
    lineUnipotent_continuous map_planeUnipotent map_lineUnipotent atInfinity_atFinite_commute
    atFinite_left_conjugate finiteGroup_atInfinity integral_principal_finite_conjugate
    planeUnipotent_three_reduction planeUnipotent_adelic_factor)

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

namespace DefectAverage

/-! ### Measures on the unit square -/

/-- The unit-square measure `[0,1)²` equals Lebesgue measure restricted to the closed square. -/
theorem realPlaneUnitMeasure_eq_Icc :
    realPlaneUnitMeasure =
      (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hae : Set.Ico (0 : ℝ) 1 =ᵐ[(volume : Measure ℝ)] Set.Icc (0 : ℝ) 1 := Ico_ae_eq_Icc
  have prodVolume : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
  rw [realPlaneUnitMeasure, Measure.restrict_congr_set hae, Measure.prod_restrict, prodVolume]

/-- A continuous function on the plane is integrable for the unit-square measure. -/
theorem integrable_realPlaneUnit_of_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    Integrable f realPlaneUnitMeasure := by
  rw [realPlaneUnitMeasure_eq_Icc]
  have compact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  exact hf.continuousOn.integrableOn_compact compact

/-- The real average over the unit square equals the adelic average over the radical domain
when scaling by three removes the finite part on the domain. -/
theorem real_unit_average_eq_adelic_average
    (G : Adeles × Adeles → ℂ) (R : ℝ × ℝ → ℂ) (hR : Measurable R)
    (periodic : ∀ (rational : ℚ × ℚ) (point : Adeles × Adeles),
      G (rationalAdele rational.1 + point.1, rationalAdele rational.2 + point.2) = G point)
    (removal : ∀ point : Adeles × Adeles, point ∈ additiveDomain ×ˢ additiveDomain →
      G (3 * point.1, 3 * point.2) = R (point.1.1, point.2.1)) :
    (∫ r, R r ∂realPlaneUnitMeasure) = ∫ point, G point ∂planeDomainMeasure := by
  rw [← planeDomain_integral_real_projection hR]
  have scaled := radical_periodic_integral_rational_scaling G periodic
    (Units.mk0 (3 : ℚ) (by norm_num))
  simp only [Units.val_mk0, map_ofNat] at scaled
  rw [← scaled]
  apply integral_congr_ae
  rw [planeDomainMeasure_eq]
  have measurable_domain : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  filter_upwards [ae_restrict_mem (measurable_domain.prod measurable_domain)] with point member
  exact (removal point member).symm

/-- Subtracting the average from an integrable function leaves integral zero. -/
theorem integral_sub_const_eq_zero {E : ℝ × ℝ → ℂ} {S : ℂ}
    (hE : Integrable E realPlaneUnitMeasure) (havg : (∫ r, E r ∂realPlaneUnitMeasure) = S) :
    (∫ r, (E r - S) ∂realPlaneUnitMeasure) = 0 := by
  have hc : (∫ _r : ℝ × ℝ, S ∂realPlaneUnitMeasure) = S :=
    integral_eq_const (ae_of_all _ fun _ => rfl)
  rw [integral_sub hE (integrable_const S), havg, hc, sub_self]

/-- A linear functional of a polynomial-valued family has zero average as soon as every
coefficient is an integrable function minus its average. -/
theorem average_zero_of_coefficients (μ : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (f : ℝ × ℝ → HomogeneousPoly n) (Ecf : (Fin 3 →₀ ℕ) → ℝ × ℝ → ℂ)
    (Sc : (Fin 3 →₀ ℕ) → ℂ)
    (hf : ∀ (r : ℝ × ℝ) (m : Fin 3 →₀ ℕ), (f r).val.coeff m = Ecf m r - Sc m)
    (hint : ∀ m, Integrable (Ecf m) realPlaneUnitMeasure)
    (havg : ∀ m, (∫ r, Ecf m r ∂realPlaneUnitMeasure) = Sc m) :
    (∫ r, μ (f r) ∂realPlaneUnitMeasure) = 0 := by
  have hlin : ∀ r, μ (f r) = ∑ m ∈ FlatExtensions.degreeMonomials n,
      (Ecf m r - Sc m) * μ (PolynomialNaturality.basisVector n m) := by
    intro r
    have expansion := congrArg μ (PolynomialNaturality.sum_basis n (f r))
    rw [map_sum] at expansion
    rw [← expansion]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul, smul_eq_mul, hf]
  have hint' : ∀ m, Integrable (fun r => Ecf m r - Sc m) realPlaneUnitMeasure :=
    fun m => (hint m).sub (integrable_const (Sc m))
  have hsum : (∫ r, μ (f r) ∂realPlaneUnitMeasure) =
      ∑ m ∈ FlatExtensions.degreeMonomials n,
        ∫ r, (Ecf m r - Sc m) * μ (PolynomialNaturality.basisVector n m) ∂realPlaneUnitMeasure := by
    simp only [hlin]
    exact integral_finsetSum _ (fun m _ => (hint' m).mul_const _)
  rw [hsum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [integral_mul_const, integral_sub_const_eq_zero (hint m) (havg m), zero_mul]

/-! ### Radical coordinates at infinity and at the finite places -/

theorem atInfinity_lineUnipotent_eq (first second : ℝ) :
    atInfinity (lineUnipotent first second) = lineUnipotent (first, 0) (second, 0) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, lineUnipotent, upperUnipotent]

theorem atFinite_lineUnipotent_eq (first second : FiniteAdeles) :
    atFinite (lineUnipotent first second) = lineUnipotent ((0 : ℝ), first) ((0 : ℝ), second) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    fin_cases i <;> fin_cases j <;>
    simp [atFinite, combineGL, pairMatrix, lineUnipotent, upperUnipotent]

theorem lineUnipotent_adelic_factor (first second : Adeles) :
    lineUnipotent first second = atInfinity (lineUnipotent first.1 second.1) *
      atFinite (lineUnipotent first.2 second.2) := by
  rw [atInfinity_lineUnipotent_eq, atFinite_lineUnipotent_eq, ← lineUnipotent_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

theorem lineUnipotent_three_reduction (first second : IntegralAdeles) :
    Matrix.GeneralLinearGroup.map integralReduction (lineUnipotent (3 * first) (3 * second)) =
      1 := by
  rw [map_lineUnipotent]
  have first_zero : integralReduction (3 * first) = 0 := by
    rw [map_mul, map_ofNat, show (3 : ZMod 3) = 0 from by decide, zero_mul]
  have second_zero : integralReduction (3 * second) = 0 := by
    rw [map_mul, map_ofNat, show (3 : ZMod 3) = 0 from by decide, zero_mul]
  rw [first_zero, second_zero]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> norm_num [lineUnipotent, upperUnipotent]

/-! ### Removal of the finite part -/

/-- A function that is right invariant under the finite level does not see a finite principal
element placed on the left of a matrix with integral finite part. -/
theorem finite_principal_removal {F : AdelicGL → ℂ}
    (hfin : ∀ (level : finiteLevel) (x : AdelicGL), F (x * atFinite level.val) = F x)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (real : RealGL3) (principal : GL3 IntegralAdeles)
    (reduction : Matrix.GeneralLinearGroup.map integralReduction principal = 1) :
    F (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding principal) *
      (atInfinity real * matrix)) = F (atInfinity real * matrix) := by
  have finite_eq' : finiteGroup (atInfinity real * matrix) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral := by
    simpa only [map_mul, finiteGroup_atInfinity, one_mul] using finite_eq
  have level : (finiteGroup (atInfinity real * matrix))⁻¹ *
      Matrix.GeneralLinearGroup.map integralEmbedding principal *
      finiteGroup (atInfinity real * matrix) ∈ finiteLevel := by
    rw [finite_eq']
    exact integral_principal_finite_conjugate principal integral reduction
  rw [atFinite_left_conjugate]
  exact hfin ⟨_, level⟩ _

theorem planeUnipotent_three_finite_removal {F : AdelicGL → ℂ}
    (hfin : ∀ (level : finiteLevel) (x : AdelicGL), F (x * atFinite level.val) = F x)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (first second : Adeles) (first_integral : first.2 ∈ Set.range integralEmbedding)
    (second_integral : second.2 ∈ Set.range integralEmbedding) :
    F (planeUnipotent (3 * first) (3 * second) * matrix) =
      F (atInfinity (planeUnipotent (3 * first.1) (3 * second.1)) * matrix) := by
  obtain ⟨firstValue, first_eq⟩ := first_integral
  obtain ⟨secondValue, second_eq⟩ := second_integral
  have finite_unipotent : planeUnipotent (3 * first.2) (3 * second.2) =
      Matrix.GeneralLinearGroup.map integralEmbedding
        (planeUnipotent (3 * firstValue) (3 * secondValue)) := by
    simp only [map_planeUnipotent, map_mul, map_ofNat, first_eq, second_eq]
  rw [planeUnipotent_adelic_factor]
  change F ((atInfinity (planeUnipotent (3 * first.1) (3 * second.1)) *
    atFinite (planeUnipotent (3 * first.2) (3 * second.2))) * matrix) = _
  rw [atInfinity_atFinite_commute, mul_assoc, finite_unipotent]
  exact finite_principal_removal hfin integral matrix finite_eq _ _
    (planeUnipotent_three_reduction firstValue secondValue)

theorem lineUnipotent_three_finite_removal {F : AdelicGL → ℂ}
    (hfin : ∀ (level : finiteLevel) (x : AdelicGL), F (x * atFinite level.val) = F x)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (first second : Adeles) (first_integral : first.2 ∈ Set.range integralEmbedding)
    (second_integral : second.2 ∈ Set.range integralEmbedding) :
    F (lineUnipotent (3 * first) (3 * second) * matrix) =
      F (atInfinity (lineUnipotent (3 * first.1) (3 * second.1)) * matrix) := by
  obtain ⟨firstValue, first_eq⟩ := first_integral
  obtain ⟨secondValue, second_eq⟩ := second_integral
  have finite_unipotent : lineUnipotent (3 * first.2) (3 * second.2) =
      Matrix.GeneralLinearGroup.map integralEmbedding
        (lineUnipotent (3 * firstValue) (3 * secondValue)) := by
    simp only [map_lineUnipotent, map_mul, map_ofNat, first_eq, second_eq]
  rw [lineUnipotent_adelic_factor]
  change F ((atInfinity (lineUnipotent (3 * first.1) (3 * second.1)) *
    atFinite (lineUnipotent (3 * first.2) (3 * second.2))) * matrix) = _
  rw [atInfinity_atFinite_commute, mul_assoc, finite_unipotent]
  exact finite_principal_removal hfin integral matrix finite_eq _ _
    (lineUnipotent_three_reduction firstValue secondValue)

/-! ### Real paths along the radical -/

theorem continuous_planePath (matrix : AdelicGL) :
    Continuous (fun r : ℝ × ℝ =>
      atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * matrix) := by
  simp only [atInfinity_planeUnipotent]
  exact (planeUnipotent_continuous.comp
    (((continuous_const.mul continuous_fst).prodMk continuous_const).prodMk
      ((continuous_const.mul continuous_snd).prodMk continuous_const))).mul continuous_const

theorem continuous_linePath (matrix : AdelicGL) :
    Continuous (fun r : ℝ × ℝ =>
      atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * matrix) := by
  simp only [atInfinity_lineUnipotent_eq]
  exact (lineUnipotent_continuous.comp
    (((continuous_const.mul continuous_fst).prodMk continuous_const).prodMk
      ((continuous_const.mul continuous_snd).prodMk continuous_const))).mul continuous_const

/-! ### Real average equals adelic average -/

/-- Plane radical: the real average over the unit square of a left rationally invariant,
right `finiteLevel`-invariant continuous function equals its adelic radical-domain average. -/
theorem plane_real_average_eq_adelic {F : AdelicGL → ℂ} (hcont : Continuous F)
    (hrat : ∀ (element : RationalGL3) (x : AdelicGL), F (rationalGroup element * x) = F x)
    (hfin : ∀ (level : finiteLevel) (x : AdelicGL), F (x * atFinite level.val) = F x)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, F (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * matrix)
        ∂realPlaneUnitMeasure) =
      ∫ point : Adeles × Adeles, F (planeUnipotent point.1 point.2 * matrix)
        ∂planeDomainMeasure := by
  refine real_unit_average_eq_adelic_average
    (fun point : Adeles × Adeles => F (planeUnipotent point.1 point.2 * matrix))
    (fun r : ℝ × ℝ => F (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * matrix))
    (hcont.comp (continuous_planePath matrix)).measurable ?_ ?_
  · intro rational point
    show F (planeUnipotent (rationalAdele rational.1 + point.1)
        (rationalAdele rational.2 + point.2) * matrix) =
      F (planeUnipotent point.1 point.2 * matrix)
    rw [planeUnipotent_add, mul_assoc, ← map_planeUnipotent]
    exact hrat (planeUnipotent rational.1 rational.2) _
  · intro point member
    exact planeUnipotent_three_finite_removal hfin integral matrix finite_eq point.1 point.2
      member.1.2 member.2.2

/-- Line radical analogue of `plane_real_average_eq_adelic`. -/
theorem line_real_average_eq_adelic {F : AdelicGL → ℂ} (hcont : Continuous F)
    (hrat : ∀ (element : RationalGL3) (x : AdelicGL), F (rationalGroup element * x) = F x)
    (hfin : ∀ (level : finiteLevel) (x : AdelicGL), F (x * atFinite level.val) = F x)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, F (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * matrix)
        ∂realPlaneUnitMeasure) =
      ∫ point : Adeles × Adeles, F (lineUnipotent point.1 point.2 * matrix)
        ∂planeDomainMeasure := by
  refine real_unit_average_eq_adelic_average
    (fun point : Adeles × Adeles => F (lineUnipotent point.1 point.2 * matrix))
    (fun r : ℝ × ℝ => F (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * matrix))
    (hcont.comp (continuous_linePath matrix)).measurable ?_ ?_
  · intro rational point
    show F (lineUnipotent (rationalAdele rational.1 + point.1)
        (rationalAdele rational.2 + point.2) * matrix) =
      F (lineUnipotent point.1 point.2 * matrix)
    rw [lineUnipotent_add, mul_assoc, ← map_lineUnipotent]
    exact hrat (lineUnipotent rational.1 rational.2) _
  · intro point member
    exact lineUnipotent_three_finite_removal hfin integral matrix finite_eq point.1 point.2
      member.1.2 member.2.2

/-! ### The Eisenstein coefficients -/

/-- The scalar Eisenstein series attached to the `m`-th coefficient of the section of `c`
at the vertex tuple `y`. -/
def eisensteinCoefficient (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    AdelicGL → ℂ :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y))).val

theorem eisensteinValue_coeff (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (g : AdelicGL) :
    (eisensteinValue D hol c y g).val.coeff m = eisensteinCoefficient D hol c y m g :=
  PolynomialNaturality.polynomialValue_coeff D hol (PolynomialEisenstein.sourceSection D c y) m g

theorem eisensteinCoefficient_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    Continuous (eisensteinCoefficient D hol c y m) :=
  sectionEisensteinValue_continuous D hol large _

theorem eisensteinCoefficient_rational (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (element : RationalGL3) (x : AdelicGL) :
    eisensteinCoefficient D hol c y m (rationalGroup element * x) =
      eisensteinCoefficient D hol c y m x :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m
      (PolynomialEisenstein.sourceSection D c y))).property.1 element x

theorem eisensteinCoefficient_finite (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (level : finiteLevel) (x : AdelicGL) :
    eisensteinCoefficient D hol c y m (x * atFinite level.val) =
      eisensteinCoefficient D hol c y m x :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m
      (PolynomialEisenstein.sourceSection D c y))).property.2 level x

/-- The constant term of the plane Eisenstein series of a section along the plane radical is
the section itself. -/
theorem sectionEisenstein_plane_constant_term (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (s : SectionSpace.inducedSections D .plane cohomologicalPoint) (g : AdelicGL) :
    (∫ point : Adeles × Adeles, (SectionSpace.sectionEisensteinValue D hol s).val
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure) = s.val g := by
  have halfPlane : -(n : ℝ) / 2 < cohomologicalPoint.re := by
    have fourReal : (4 : ℝ) ≤ n := by exact_mod_cast large
    norm_num [cohomologicalPoint]
    linarith
  have flat := (SectionSpace.linearFlatExtension D hol s).property
  have hsum : ∀ x, (SectionSpace.sectionEisensteinValue D hol s).val x =
      ∑' flag : Flags .plane, eisensteinSummand
        (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint x flag := by
    intro x
    rw [EndpointEisensteinCocycle.sectionEisensteinValue_eq_sum D hol large s x]
    simp only [eisensteinSummand, SectionSpace.linearFlatExtension_endpoint]
  have constantTerm := (scalar_plane_constant_term (inducingData := D)
    (family := (SectionSpace.linearFlatExtension D hol s).val) flat cohomologicalPoint
    halfPlane g).2
  calc (∫ point : Adeles × Adeles, (SectionSpace.sectionEisensteinValue D hol s).val
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure)
      = ∫ point : Adeles × Adeles, ∑' flag : Flags .plane, eisensteinSummand
          (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint
          (planeUnipotent point.1 point.2 * g) flag ∂planeDomainMeasure :=
        integral_congr_ae (ae_of_all _ fun point => hsum _)
    _ = (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint g := constantTerm
    _ = s.val g := by rw [SectionSpace.linearFlatExtension_endpoint]

theorem eisensteinCoefficient_plane_constant_term (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (∫ point : Adeles × Adeles, eisensteinCoefficient D hol c y m
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure) =
      (c.val y g).val.coeff m :=
  sectionEisenstein_plane_constant_term large D hol
    (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y)) g

/-- The constant term of the Eisenstein coefficient along the line radical is the corresponding
coefficient of the standard continuation `J c`. -/
theorem sourceStandard_coeff_eq_integral (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m =
      ∫ point : Adeles × Adeles, eisensteinCoefficient D hol c y m
        (lineUnipotent point.1 point.2 * g) ∂planeDomainMeasure := by
  rw [StandardConstantTermComparison.sourceStandard_coeff_constantTerm large D hol c y g m,
    planeDomainMeasure_eq]
  refine integral_congr_ae (ae_of_all _ fun point => ?_)
  exact PolynomialNaturality.polynomialValue_coeff D hol
    (PolynomialEisenstein.sourceSection D c y) m _

/-- Real average of the Eisenstein coefficient along the plane radical: it is the coefficient
of `c`. -/
theorem eisensteinCoefficient_plane_real_average (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, eisensteinCoefficient D hol c y m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      (c.val y g).val.coeff m :=
  (plane_real_average_eq_adelic (F := eisensteinCoefficient D hol c y m)
    (eisensteinCoefficient_continuous large D hol c y m)
    (eisensteinCoefficient_rational D hol c y m) (eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans (eisensteinCoefficient_plane_constant_term large D hol c y m g)

/-- Real average of the Eisenstein coefficient along the line radical: it is the coefficient of
`J c`. -/
theorem eisensteinCoefficient_line_real_average (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, eisensteinCoefficient D hol c y m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m :=
  (line_real_average_eq_adelic (F := eisensteinCoefficient D hol c y m)
    (eisensteinCoefficient_continuous large D hol c y m)
    (eisensteinCoefficient_rational D hol c y m) (eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans (sourceStandard_coeff_eq_integral large D hol c y m g).symm

/-! ### Invariance of the source along the radical -/

theorem isInduced_plane_unipotent {D : InducingData n} {s : ℂ} {f : AdelicGL → ℂ}
    (h : IsInduced D .plane s f) (a b : Adeles) (g : AdelicGL) :
    f (planeUnipotent a b * g) = f g := by
  obtain ⟨_, _, _, h5, _⟩ := h
  exact h5 a b g

theorem isInduced_line_unipotent {D : InducingData n} {s : ℂ} {f : AdelicGL → ℂ}
    (h : IsInduced D .line s f) (a b : Adeles) (g : AdelicGL) :
    f (lineUnipotent a b * g) = f g := by
  obtain ⟨_, _, _, h5, _⟩ := h
  exact h5 a b g

theorem source_plane_path_invariant (D : InducingData n)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (a b : ℝ) (g : AdelicGL) :
    (c.val y (atInfinity (planeUnipotent a b) * g)).val.coeff m =
      (c.val y g).val.coeff m := by
  rw [atInfinity_planeUnipotent]
  exact isInduced_plane_unipotent (c.property.1 y m) (a, 0) (b, 0) g

theorem source_line_path_invariant (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (a b : ℝ) (g : AdelicGL) :
    ((EndpointSourceStandard.sourceStandard D large hol c).val y
          (atInfinity (lineUnipotent a b) * g)).val.coeff m =
      ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m := by
  rw [atInfinity_lineUnipotent_eq]
  exact isInduced_line_unipotent
    ((EndpointSourceStandard.sourceStandard D large hol c).property.1 y m) (a, 0) (b, 0) g

/-! ### Unfolding the defect family -/

theorem sideUnipotent_plane {R : Type*} [CommRing R] (s t : R) :
    sideUnipotent .plane s t = planeUnipotent s t := rfl

theorem sideUnipotent_line {R : Type*} [CommRing R] (s t : R) :
    sideUnipotent .line s t = lineUnipotent s t := rfl

theorem sideSource_plane (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) :
    sideSource large D hol c .plane = c := rfl

theorem sideSource_line (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) :
    sideSource large D hol c .line = EndpointSourceStandard.sourceStandard D large hol c := rfl

theorem defectFamily_three (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (q : RationalGL3) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q 3 r y =
      defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
        (atInfinity (sideUnipotent side (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) :=
  rfl

theorem defectValue_coeff (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (defectValue large D hol c side y g).val.coeff m =
      (eisensteinValue D hol c y g).val.coeff m -
        ((sideSource large D hol c side).val y g).val.coeff m := by
  unfold defectValue
  rw [Submodule.coe_sub, MvPolynomial.coeff_sub]

/-- The finite adelic part of the inverse of the rational image of an integral matrix is
integral. -/
theorem finiteGroup_rationalGroup_integral_inv (g : IntegralGL3) :
    finiteGroup (rationalGroup (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding
        (Matrix.GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) g⁻¹) := by
  have inverse : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)⁻¹ =
      integralRational g⁻¹ := (map_inv integralRational g).symm
  rw [inverse]
  exact Comparison.integralFinite_integralMap g⁻¹

end DefectAverage

open DefectAverage

/-! ### The real average of the defect family vanishes -/

/-- Plane stratum: for a rational flag whose inverse has integral finite part, the real torus
average of the defect translation family vanishes under every linear functional. -/
theorem defectFamily_plane_average_zero (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (q : RationalGL3) (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily large D hol c .plane q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine average_zero_of_coefficients μ
    (fun r => defectFamily large D hol c .plane q 3 r y)
    (fun m r => eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily large D hol c .plane q 3 r y).val.coeff m =
      eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [defectFamily_three, defectValue_coeff, sideUnipotent_plane, eisensteinValue_coeff,
      sideSource_plane, source_plane_path_invariant]
  · intro m
    exact integrable_realPlaneUnit_of_continuous
      ((eisensteinCoefficient_continuous large D hol c _ m).comp
        (continuous_planePath (rationalGroup q⁻¹)))
  · intro m
    exact eisensteinCoefficient_plane_real_average large D hol c _ m integral _ hq

/-- Line stratum: the same vanishing, with `J c` in place of `c`. -/
theorem defectFamily_line_average_zero (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (q : RationalGL3) (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily large D hol c .line q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine average_zero_of_coefficients μ
    (fun r => defectFamily large D hol c .line q 3 r y)
    (fun m r => eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => ((EndpointSourceStandard.sourceStandard D large hol c).val
        (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily large D hol c .line q 3 r y).val.coeff m =
      eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      ((EndpointSourceStandard.sourceStandard D large hol c).val
          (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [defectFamily_three, defectValue_coeff, sideUnipotent_line, eisensteinValue_coeff,
      sideSource_line, source_line_path_invariant]
  · intro m
    exact integrable_realPlaneUnit_of_continuous
      ((eisensteinCoefficient_continuous large D hol c _ m).comp
        (continuous_linePath (rationalGroup q⁻¹)))
  · intro m
    exact eisensteinCoefficient_line_real_average large D hol c _ m integral _ hq

/-- Plane stratum at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_plane_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (g : IntegralGL3) (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c .plane
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  rw [← realPlaneUnitMeasure_eq_Icc]
  exact defectFamily_plane_average_zero large D hol c _ _
    (finiteGroup_rationalGroup_integral_inv g) y μ

/-- Line stratum at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_line_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (g : IntegralGL3) (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c .line
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  rw [← realPlaneUnitMeasure_eq_Icc]
  exact defectFamily_line_average_zero large D hol c _ _
    (finiteGroup_rationalGroup_integral_inv g) y μ

/-- Both strata at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (g : IntegralGL3) (y : Fin 3 → RationalGL3)
    (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c side
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  cases side
  · exact defectFamily_plane_average_zero_Icc large D hol c g y μ
  · exact defectFamily_line_average_zero_Icc large D hol c g y μ

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
