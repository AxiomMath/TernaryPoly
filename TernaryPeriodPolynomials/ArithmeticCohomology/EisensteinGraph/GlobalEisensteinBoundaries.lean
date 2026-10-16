module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GlobalEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardSourceBoundaries

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.GlobalEisensteinBoundaries

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction StandardSourceBoundaries

def eisensteinOneValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RealGL3) : AdelicGL → HomogeneousPoly degree :=
  PolynomialEisenstein.polynomialValue data holomorphic (oneSection incoming vertices)

theorem eisensteinOneValue_equivariant {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (incoming : InducedOneCochain data) (real : RealGL3) (vertices : Fin 2 → RealGL3)
    (matrix : AdelicGL) :
    eisensteinOneValue data holomorphic incoming (fun index => real * vertices index) matrix =
      realCoefficientComponent degree data.chi real
        (eisensteinOneValue data holomorphic incoming vertices (matrix * atInfinity real)) := by
  have transformed : oneSection incoming (fun index => real * vertices index) =
      PolynomialNaturality.coefficientMap data (realCoefficientComponent degree data.chi real)
        (PolynomialNaturality.rightReal data real (oneSection incoming vertices)) := by
    apply Subtype.ext
    funext argument
    rw [PolynomialNaturality.coefficientMap_apply]
    exact incoming.equivariant real vertices argument
  unfold eisensteinOneValue
  rw [transformed, PolynomialNaturality.polynomialValue_coefficientMap,
    EndpointEisensteinCocycle.polynomialValue_right_real data holomorphic large]

def rationalEisensteinOneValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data)
    (vertices : Fin 2 → RationalGL3) : HomogeneousPoly degree :=
  eisensteinOneValue data holomorphic incoming
    (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) 1

theorem rationalEisensteinOneValue_equivariant {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (incoming : InducedOneCochain data) (element : rationalLevel)
    (vertices : Fin 2 → RationalGL3) :
    rationalEisensteinOneValue data holomorphic incoming (fun index => element.val * vertices index) =
      rationalCoefficientComponent degree data.chi element.val
        (rationalEisensteinOneValue data holomorphic incoming vertices) := by
  have vertices_eq :
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (element.val * vertices index)) =
      (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) := by
    funext index
    exact map_mul _ _ _
  unfold rationalEisensteinOneValue
  rw [vertices_eq, eisensteinOneValue_equivariant large data holomorphic]
  change realCoefficientComponent degree data.chi
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _ =
    realCoefficientComponent degree data.chi
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) _
  congr 1
  have argument : atInfinity (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) element.val) =
      rationalGroup element.val * atFinite (rationalFinite element.val⁻¹) := by
    rw [Comparison.rationalGroup_split]
    apply InducedContinuity.adelic_ext
    · simp only [map_mul, InducedContinuity.realGroup_atInfinity,
        InducedContinuity.realGroup_atFinite, mul_one]
    · simp only [map_mul, InducedContinuity.finiteGroup_atInfinity,
        InducedContinuity.finiteGroup_atFinite, one_mul, map_inv, mul_inv_cancel]
  unfold eisensteinOneValue
  rw [one_mul, argument, PolynomialEisenstein.polynomialValue_rational]
  have finite_membership : rationalFinite element.val⁻¹ ∈ finiteLevel := by
    simpa only [map_inv] using finiteLevel.inv_mem (Comparison.rationalLevel_finiteLevel element)
  simpa only [one_mul] using PolynomialEisenstein.polynomialValue_finite data holomorphic
    (oneSection incoming _) ⟨rationalFinite element.val⁻¹, finite_membership⟩ 1

def eisensteinOneCochain {degree : ℕ} (large : 4 ≤ degree) (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (incoming : InducedOneCochain data) :
    cochains rationalLevel (rationalCoefficientComponent degree data.chi) 1 :=
  ⟨rationalEisensteinOneValue data holomorphic incoming,
    rationalEisensteinOneValue_equivariant large data holomorphic incoming⟩

theorem globalCocycle_boundary_of_induced_primitive {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (incoming : InducedOneCochain data) (source : SourceSpace.sourceCocycles data .plane)
    (boundary : ∀ vertices matrix, source.val vertices matrix =
      incoming.value ![vertices 1, vertices 2] matrix - incoming.value ![vertices 0, vertices 2] matrix +
        incoming.value ![vertices 0, vertices 1] matrix) :
    EndpointEisensteinCocycle.globalCocycle data holomorphic large source =
      boundaryMap rationalLevel (rationalCoefficientComponent degree data.chi)
        (eisensteinOneCochain large data holomorphic incoming) := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  rw [EndpointEisensteinCocycle.globalCocycle_realizes,
    GlobalEisensteinCocycle.evaluatedSourceValue_eq_anchor data holomorphic source vertices 1,
    inv_one, map_one]
  have sections : PolynomialEisenstein.sourceSection data source
      (GlobalEisensteinCocycle.realVertices vertices) =
      oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 1),
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)] -
      oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 0),
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)] +
      oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 0),
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 1)] := by
    apply Subtype.ext
    funext matrix
    exact boundary _ matrix
  have real_pair (first second : RationalGL3) :
      (fun index : Fin 2 => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (![first, second] index)) =
        ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) first,
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) second] := by
    funext index
    fin_cases index <;> rfl
  change PolynomialEisenstein.polynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data source (GlobalEisensteinCocycle.realVertices vertices)) 1 =
    rationalEisensteinOneValue data holomorphic incoming ![vertices 1, vertices 2] -
      rationalEisensteinOneValue data holomorphic incoming ![vertices 0, vertices 2] +
      rationalEisensteinOneValue data holomorphic incoming ![vertices 0, vertices 1]
  rw [sections, LinearMap.map_add (PolynomialEisenstein.polynomialValue data holomorphic),
    LinearMap.map_sub (PolynomialEisenstein.polynomialValue data holomorphic)
      (oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 1),
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)])
      (oneSection incoming ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 0),
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices 2)])]
  simp only [rationalEisensteinOneValue, eisensteinOneValue, real_pair, Pi.add_apply, Pi.sub_apply]

theorem globalClass_zero_of_induced_primitive {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (incoming : InducedOneCochain data) (source : SourceSpace.sourceCocycles data .plane)
    (boundary : ∀ vertices matrix, source.val vertices matrix =
      incoming.value ![vertices 1, vertices 2] matrix - incoming.value ![vertices 0, vertices 2] matrix +
        incoming.value ![vertices 0, vertices 1] matrix) :
    EndpointEisensteinCocycle.globalClass data holomorphic large source = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨eisensteinOneCochain large data holomorphic incoming,
    (globalCocycle_boundary_of_induced_primitive large data holomorphic incoming source boundary).symm⟩

end TernaryPeriodPolynomials.EisensteinGraph.GlobalEisensteinBoundaries
