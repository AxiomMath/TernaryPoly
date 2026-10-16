module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalExponential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.LatticeH1

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {index : Type} [Fintype index]

abbrev realUpperHilbertRep (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) : Rep ℂ RealPlaneRadical :=
  Rep.of ((basisHilbertCoefficientHom cusp basis).toMonoidHom.comp (realUpperRadicalRep degree).ρ)

def realUpperHilbertGenerator (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (coordinate : Fin 2) : Module.End ℂ (index → cusp.H) :=
  basisHilbertCoefficientHom cusp basis (upperRadicalGenerator degree coordinate)

theorem realUpperHilbertRep_continuous (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (element : RealPlaneRadical) :
    Continuous ((realUpperHilbertRep degree cusp basis).ρ element) :=
  (basisHilbertCoefficient cusp basis ((realUpperRadicalRep degree).ρ element)).continuous

theorem realUpperHilbertGenerator_nilpotent (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (coordinate : Fin 2) :
    realUpperHilbertGenerator degree cusp basis coordinate ^ (degree + 1) = 0 := by
  rw [realUpperHilbertGenerator, ← map_pow, upperRadicalGenerator_power_zero, map_zero]

theorem realUpperHilbertRep_axis (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (coordinate : Fin 2) (parameter : ℝ) :
    (realUpperHilbertRep degree cusp basis).ρ (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • realUpperHilbertGenerator degree cusp basis coordinate) := by
  change basisHilbertCoefficientHom cusp basis ((realUpperRadicalRep degree).ρ (realRadicalAxis coordinate parameter)) = _
  rw [realUpperRadicalRep_axis]
  have nilpotent : IsNilpotent ((parameter : ℂ) • upperRadicalGenerator degree coordinate) :=
    ⟨degree + 1, by rw [smul_pow, upperRadicalGenerator_power_zero, smul_zero]⟩
  rw [nilpotent.map_exp, map_smul]
  rfl

abbrev realUpperCuspidalRep (degree : ℕ) (cusp : CuspidalRepresentation) : Rep ℂ RealPlaneRadical :=
  cuspidalTensorPointwiseRep cusp (realUpperRadicalRep degree)

theorem realUpperCuspidalHilbert_intertwines (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (element : RealPlaneRadical)
    (values : realUpperCuspidalRep degree cusp) :
    cuspidalTensorHilbertEmbedding cusp basis ((realUpperCuspidalRep degree cusp).ρ element values) =
      (realUpperHilbertRep degree cusp basis).ρ element (cuspidalTensorHilbertEmbedding cusp basis values) :=
  cuspidalTensorHilbertEmbedding_map cusp basis ((realUpperRadicalRep degree).ρ element) values

def realUpperCuspidalCocycleHilbert (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) :
    groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) →ₗ[ℂ]
      groupCohomology.cocycles₁ (realUpperHilbertRep degree cusp basis) :=
  oneCocyclePullback _ _ (MonoidHom.id RealPlaneRadical) (cuspidalTensorHilbertEmbedding cusp basis) (by
    intro element
    apply LinearMap.ext
    intro values
    exact (realUpperCuspidalHilbert_intertwines degree cusp basis element values).symm)

theorem realUpperCuspidalCocycle_eq_of_generators (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (first second : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (first_regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (first (realRadicalAxis coordinate parameter))) 0)
    (second_regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (second (realRadicalAxis coordinate parameter))) 0)
    (agree : ∀ coordinate, first (realRadicalAxis coordinate 1) = second (realRadicalAxis coordinate 1)) : first = second := by
  have hilbert := realRadicalCocycle_eq_of_generators (realUpperHilbertRep degree cusp basis).ρ
    (realUpperHilbertRep_continuous degree cusp basis) (realUpperHilbertGenerator degree cusp basis) degree
    (realUpperHilbertGenerator_nilpotent degree cusp basis) (realUpperHilbertRep_axis degree cusp basis)
    (realUpperCuspidalCocycleHilbert degree cusp basis first) (realUpperCuspidalCocycleHilbert degree cusp basis second)
    first_regular second_regular (fun coordinate => congrArg (cuspidalTensorHilbertEmbedding cusp basis) (agree coordinate))
  apply groupCohomology.cocycles₁_ext
  intro element
  apply cuspidalTensorHilbertEmbedding_injective cusp basis
  exact congrArg (fun cycle : groupCohomology.cocycles₁ (realUpperHilbertRep degree cusp basis) => cycle element) hilbert

theorem realUpperCuspidalRep_lattice (degree : ℕ) (cusp : CuspidalRepresentation) (element : RadicalLattice)
    (values : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    (realUpperCuspidalRep degree cusp).ρ (radicalLatticeReal element) values =
      (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)).ρ element values := by
  apply Subtype.ext
  funext argument
  exact LinearMap.congr_fun (realUpperRadicalRep_lattice degree element) (values.val argument)

def realUpperCuspidalCocycleLattice (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) →ₗ[ℂ]
      groupCohomology.cocycles₁ (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree)) :=
  oneCocyclePullback _ _ radicalLatticeReal LinearMap.id (by
    intro element
    apply LinearMap.ext
    intro values
    exact (realUpperCuspidalRep_lattice degree cusp element values).symm)

theorem realUpperCuspidalBoundary_differentiable (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree)) (potential : realUpperCuspidalRep degree cusp) (coordinate : Fin 2) :
    Differentiable ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
      ((realUpperCuspidalRep degree cusp).ρ (realRadicalAxis coordinate parameter) potential - potential)) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  change cuspidalTensorValues cusp (HomogeneousPoly degree) at potential
  change Differentiable ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
    (cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
      ((realUpperRadicalRep degree).ρ (realRadicalAxis coordinate parameter)) potential - potential))
  simp only [map_sub, cuspidalTensorHilbertEmbedding_map]
  exact realRadicalBoundary_differentiable (realUpperHilbertRep degree cusp basis).ρ
    (realUpperHilbertGenerator degree cusp basis) degree (realUpperHilbertGenerator_nilpotent degree cusp basis)
    (realUpperHilbertRep_axis degree cusp basis) (cuspidalTensorHilbertEmbedding cusp basis potential) coordinate

theorem realUpperCuspidalH1_zero_iff_lattice (degree : ℕ) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0) :
    groupCohomology.H1π (realUpperCuspidalRep degree cusp) cycle = 0 ↔
      groupCohomology.H1π (cuspidalTensorPointwiseRep cusp (upperRadicalLatticeRep degree))
        (realUpperCuspidalCocycleLattice degree cusp cycle) = 0 := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  constructor
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero ⊢
    obtain ⟨potential, boundary⟩ := zero
    change cuspidalTensorValues cusp (HomogeneousPoly degree) at potential
    refine ⟨potential, ?_⟩
    funext element
    have equality := congrFun boundary (radicalLatticeReal element)
    change cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
      ((realUpperRadicalRep degree).ρ (radicalLatticeReal element)) potential - potential = _ at equality
    rw [realUpperRadicalRep_lattice] at equality
    exact equality
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero
    obtain ⟨potential, boundary⟩ := zero
    change cuspidalTensorValues cusp (HomogeneousPoly degree) at potential
    let realBoundary : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) :=
      ⟨groupCohomology.d₀₁ (realUpperCuspidalRep degree cusp) potential,
        groupCohomology.d₀₁_apply_mem_cocycles₁ (A := realUpperCuspidalRep degree cusp) potential⟩
    have equality : cycle = realBoundary := by
      apply realUpperCuspidalCocycle_eq_of_generators degree cusp basis cycle realBoundary regular
      · intro coordinate
        exact (realUpperCuspidalBoundary_differentiable degree cusp basis potential coordinate) 0
      · intro coordinate
        rw [realRadicalAxis_one]
        have equality := congrFun boundary (radicalLatticeGenerator coordinate)
        change cuspidalTensorMap cusp (rationalCoefficientComponent degree trivialCharacter
          (upperRadicalLattice (radicalLatticeGenerator coordinate))) potential - potential =
          cycle (radicalLatticeReal (radicalLatticeGenerator coordinate)) at equality
        have action : (realUpperRadicalRep degree).ρ (radicalLatticeReal (radicalLatticeGenerator coordinate)) =
            rationalCoefficientComponent degree trivialCharacter (upperRadicalLattice (radicalLatticeGenerator coordinate)) :=
          realUpperRadicalRep_lattice degree (radicalLatticeGenerator coordinate)
        rw [← action] at equality
        exact equality.symm
    rw [equality, groupCohomology.H1π_eq_zero_iff]
    exact ⟨potential, rfl⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
