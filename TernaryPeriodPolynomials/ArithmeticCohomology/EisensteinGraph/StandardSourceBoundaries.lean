module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardExistence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SourceComparison.RationalInvariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardSourceBoundaries

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction

structure InducedOneCochain {degree : ℕ} (data : InducingData degree) where
  value : (Fin 2 → RealGL3) → AdelicGL → HomogeneousPoly degree
  induced : ∀ vertices monomial, IsInduced data .plane cohomologicalPoint
    (fun matrix => (value vertices matrix).val.coeff monomial)
  equivariant : ∀ real vertices matrix, value (fun index => real * vertices index) matrix =
    realCoefficientComponent degree data.chi real (value vertices (matrix * atInfinity real))

def oneSection {degree : ℕ} {data : InducingData degree} (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) : PolynomialEisenstein.polynomialSections data :=
  ⟨incoming.value vertices, incoming.induced vertices⟩

def standardOneValue {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) : AdelicGL → HomogeneousPoly degree :=
  EndpointPolynomialStandard.polynomialValue data large holomorphic (oneSection incoming vertices)

theorem standardOneValue_induced {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) (monomial : Fin 3 →₀ ℕ) :
    IsInduced data .line cohomologicalPoint
      (fun matrix => (standardOneValue large data holomorphic incoming vertices matrix).val.coeff monomial) :=
  EndpointPolynomialStandard.polynomialValue_induced data large holomorphic _ monomial

theorem standardOneValue_equivariant {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (real : RealGL3) (vertices : Fin 2 → RealGL3) (matrix : AdelicGL) :
    standardOneValue large data holomorphic incoming (fun index => real * vertices index) matrix =
      realCoefficientComponent degree data.chi real
        (standardOneValue large data holomorphic incoming vertices (matrix * atInfinity real)) := by
  have transformed : oneSection incoming (fun index => real * vertices index) =
      PolynomialNaturality.coefficientMap data (realCoefficientComponent degree data.chi real)
        (PolynomialNaturality.rightReal data real (oneSection incoming vertices)) := by
    apply Subtype.ext
    funext argument
    rw [PolynomialNaturality.coefficientMap_apply]
    exact incoming.equivariant real vertices argument
  unfold standardOneValue
  rw [transformed, EndpointPolynomialStandard.polynomialValue_coefficientMap,
    EndpointPolynomialStandard.polynomialValue_right_real]

theorem standardOneValue_finite {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) (matrix : AdelicGL) (level : finiteLevel) :
    standardOneValue large data holomorphic incoming vertices (matrix * atFinite level.val) =
      standardOneValue large data holomorphic incoming vertices matrix := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (standardOneValue_induced large data holomorphic incoming vertices monomial).2.1 level matrix

theorem standardOneValue_parabolic {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) (matrix : AdelicGL) (rational : RationalGL3)
    (parabolic : rational ∈ GeneralEisenstein.parabolic .line) :
    standardOneValue large data holomorphic incoming vertices (rationalGroup rational * matrix) =
      standardOneValue large data holomorphic incoming vertices matrix := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact SourceComparison.induced_parabolic_invariant
    (standardOneValue_induced large data holomorphic incoming vertices monomial) rational parabolic matrix

def rationalOneValue {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RationalGL3) (rational : RationalGL3) : HomogeneousPoly degree :=
  standardOneValue large data holomorphic incoming
    (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
    (rationalGroup rational⁻¹)

theorem rationalOneValue_flag_independent {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RationalGL3) (first second : RationalGL3)
    (related : first⁻¹ * second ∈ GeneralEisenstein.parabolic .line) :
    rationalOneValue large data holomorphic incoming vertices first =
      rationalOneValue large data holomorphic incoming vertices second := by
  have inverse_related : second⁻¹ * first ∈ GeneralEisenstein.parabolic .line := by
    simpa only [_root_.mul_inv_rev, inv_inv] using
      (GeneralEisenstein.parabolic .line).inv_mem related
  have argument : rationalGroup second⁻¹ = rationalGroup (second⁻¹ * first) * rationalGroup first⁻¹ := by
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one]
  unfold rationalOneValue
  rw [argument, standardOneValue_parabolic large data holomorphic incoming _ _ _ inverse_related]

theorem rationalOneValue_equivariant {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (element : rationalLevel) (vertices : Fin 2 → RationalGL3) (rational : RationalGL3) :
    rationalOneValue large data holomorphic incoming (fun index => element.val * vertices index) rational =
      rationalCoefficientComponent degree data.chi element.val
        (rationalOneValue large data holomorphic incoming vertices (element.val⁻¹ * rational)) := by
  have vertices_eq :
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (element.val * vertices index)) =
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) := by
    funext index
    exact map_mul _ _ _
  unfold rationalOneValue
  rw [vertices_eq, standardOneValue_equivariant]
  change realCoefficientComponent degree data.chi
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _ =
    realCoefficientComponent degree data.chi
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _
  congr 1
  rw [_root_.mul_inv_rev, inv_inv, map_mul, Comparison.rationalGroup_split element.val, ← mul_assoc]
  exact (standardOneValue_finite large data holomorphic incoming _ _
    ⟨rationalFinite element.val, Comparison.rationalLevel_finiteLevel element⟩).symm

def standardOneCochain {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data) :
    MaximalCochains degree data.chi .line 1 :=
  ⟨fun vertices flag => Quotient.liftOn' flag (rationalOneValue large data holomorphic incoming vertices)
    (fun first second related => rationalOneValue_flag_independent large data holomorphic incoming
      vertices first second (QuotientGroup.leftRel_apply.mp related)), by
    intro element vertices
    funext flag
    induction flag using Quotient.inductionOn with
    | h rational => exact rationalOneValue_equivariant large data holomorphic incoming element vertices rational⟩

theorem polynomialStandard_sub {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (first second : PolynomialEisenstein.polynomialSections data) :
    EndpointPolynomialStandard.polynomialValue data large holomorphic (first - second) =
      EndpointPolynomialStandard.polynomialValue data large holomorphic first -
        EndpointPolynomialStandard.polynomialValue data large holomorphic second := by
  have difference : first - second = first + (-1 : ℂ) • second := by
    apply Subtype.ext
    funext matrix
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  rw [difference, map_add, map_smul]
  funext matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Submodule.coe_add,
    Submodule.coe_smul, Submodule.coe_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_sub, smul_eq_mul]
  ring

theorem sourceStandard_boundary_of_induced_primitive {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (incoming : InducedOneCochain data) (source : SourceSpace.sourceCocycles data .plane)
    (boundary : ∀ vertices matrix, source.val vertices matrix =
      incoming.value ![vertices 1, vertices 2] matrix - incoming.value ![vertices 0, vertices 2] matrix +
        incoming.value ![vertices 0, vertices 1] matrix) :
    SourceQuotient.sourceToSummand data .line
      (EndpointSourceStandard.sourceStandard data large holomorphic source) = 0 := by
  apply Subtype.ext
  change SourceSpace.sourceClass data .line
    (EndpointSourceStandard.sourceStandard data large holomorphic source) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨standardOneCochain large data holomorphic incoming, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  induction flag using Quotient.inductionOn with
  | h rational =>
    change (boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
      (standardOneCochain large data holomorphic incoming)).val.val vertices (QuotientGroup.mk rational) =
      (SourceSpace.evaluatedSource data .line
        (EndpointSourceStandard.sourceStandard data large holomorphic source)).val.val
          vertices (QuotientGroup.mk rational)
    rw [SourceSpace.evaluatedSource_realizes]
    have sections : PolynomialEisenstein.sourceSection data source
        (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) =
        oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 1),
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)] -
        oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 0),
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)] +
        oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 0),
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 1)] := by
      apply Subtype.ext
      funext matrix
      exact boundary _ matrix
    change rationalOneValue large data holomorphic incoming ![vertices 1, vertices 2] rational -
      rationalOneValue large data holomorphic incoming ![vertices 0, vertices 2] rational +
      rationalOneValue large data holomorphic incoming ![vertices 0, vertices 1] rational =
      EndpointPolynomialStandard.polynomialValue data large holomorphic
        (PolynomialEisenstein.sourceSection data source
          (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)))
          (rationalGroup rational⁻¹)
    rw [sections]
    rw [LinearMap.map_add (EndpointPolynomialStandard.polynomialValue data large holomorphic),
      polynomialStandard_sub]
    have real_pair (first second : RationalGL3) :
        (fun index : Fin 2 => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (![first, second] index)) =
          ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) first,
            Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) second] := by
      funext index
      fin_cases index <;> rfl
    simp only [rationalOneValue, standardOneValue, real_pair, Pi.add_apply, Pi.sub_apply]

theorem realizesStandard_zero_of_induced_primitive {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (actual : RealizesStandard data standard) (incoming : InducedOneCochain data)
    (source : SourceSpace.sourceCocycles data .plane)
    (boundary : ∀ vertices matrix, source.val vertices matrix =
      incoming.value ![vertices 1, vertices 2] matrix - incoming.value ![vertices 0, vertices 2] matrix +
        incoming.value ![vertices 0, vertices 1] matrix) :
    standard (SourceQuotient.sourceToSummand data .plane source) = 0 := by
  rw [StandardExistence.realizesStandard_sourceStandard_value large data holomorphic standard actual source]
  exact sourceStandard_boundary_of_induced_primitive large data holomorphic incoming source boundary

end TernaryPeriodPolynomials.EisensteinGraph.StandardSourceBoundaries
