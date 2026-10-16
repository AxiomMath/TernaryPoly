module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.RealPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realRadicalAxis (coordinate : Fin 2) (parameter : ℝ) : RealPlaneRadical :=
  Multiplicative.ofAdd (Pi.single coordinate parameter)

theorem realRadicalAxis_add (coordinate : Fin 2) (first second : ℝ) :
    realRadicalAxis coordinate (first + second) = realRadicalAxis coordinate first * realRadicalAxis coordinate second := by
  apply Multiplicative.toAdd.injective
  funext index
  fin_cases coordinate <;> fin_cases index <;> simp [realRadicalAxis]

theorem realRadicalAxis_zero (coordinate : Fin 2) : realRadicalAxis coordinate 0 = 1 := by
  apply Multiplicative.toAdd.injective
  simp [realRadicalAxis]

theorem realRadicalAxis_one (coordinate : Fin 2) :
    realRadicalAxis coordinate 1 = radicalLatticeReal (radicalLatticeGenerator coordinate) := by
  apply Multiplicative.toAdd.injective
  funext index
  fin_cases coordinate <;> fin_cases index <;>
    simp [realRadicalAxis, radicalLatticeReal, radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

theorem realRadicalAxis_product (element : RealPlaneRadical) :
    realRadicalAxis 0 (element.toAdd 0) * realRadicalAxis 1 (element.toAdd 1) = element := by
  apply Multiplicative.toAdd.injective
  funext index
  fin_cases index <;> simp [realRadicalAxis]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

attribute [local instance] complexEndRationalAlgebra

theorem realRadicalCocycle_eq_of_generators (representation : Representation ℂ RealPlaneRadical E)
    (continuous : ∀ element, Continuous (representation element))
    (generators : Fin 2 → Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : ∀ coordinate, generators coordinate ^ (cutoff + 1) = 0)
    (exponential : ∀ coordinate parameter, representation (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • generators coordinate))
    (first second : groupCohomology.cocycles₁ (Rep.of representation))
    (first_regular : ∀ coordinate, DifferentiableAt ℝ (fun parameter => first (realRadicalAxis coordinate parameter)) 0)
    (second_regular : ∀ coordinate, DifferentiableAt ℝ (fun parameter => second (realRadicalAxis coordinate parameter)) 0)
    (agree : ∀ coordinate, first (realRadicalAxis coordinate 1) = second (realRadicalAxis coordinate 1)) : first = second := by
  have axes (coordinate : Fin 2) :
      (fun parameter => first (realRadicalAxis coordinate parameter)) =
        (fun parameter => second (realRadicalAxis coordinate parameter)) := by
    let action (parameter : ℝ) : E →L[ℝ] E :=
      (⟨representation (realRadicalAxis coordinate parameter), continuous _⟩ : E →L[ℂ] E).restrictScalars ℝ
    apply additiveNilpotentCocycle_eq_of_one (generators coordinate) cutoff (nilpotent coordinate) action
      (fun parameter vector => LinearMap.congr_fun (exponential coordinate parameter) vector)
    · intro x y
      rw [realRadicalAxis_add, oneCocycle_mul]
      rfl
    · intro x y
      rw [realRadicalAxis_add, oneCocycle_mul]
      rfl
    · rw [realRadicalAxis_zero, groupCohomology.cocycles₁_map_one]
    · rw [realRadicalAxis_zero, groupCohomology.cocycles₁_map_one]
    · exact first_regular coordinate
    · exact second_regular coordinate
    · exact agree coordinate
  apply groupCohomology.cocycles₁_ext
  intro element
  rw [← realRadicalAxis_product element, oneCocycle_mul, oneCocycle_mul,
    congrFun (axes 0) (element.toAdd 0), congrFun (axes 1) (element.toAdd 1)]

def realRadicalCocycleLattice (representation : Representation ℂ RealPlaneRadical E) :
    groupCohomology.cocycles₁ (Rep.of representation) →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.of (representation.comp radicalLatticeReal)) :=
  oneCocyclePullback (Rep.of representation) (Rep.of (representation.comp radicalLatticeReal))
    radicalLatticeReal LinearMap.id (fun _ => rfl)

theorem realRadicalBoundary_differentiable (representation : Representation ℂ RealPlaneRadical E)
    (generators : Fin 2 → Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : ∀ coordinate, generators coordinate ^ (cutoff + 1) = 0)
    (exponential : ∀ coordinate parameter, representation (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • generators coordinate))
    (potential : E) (coordinate : Fin 2) :
    Differentiable ℝ (fun parameter => representation (realRadicalAxis coordinate parameter) potential - potential) := by
  have equality : (fun parameter => representation (realRadicalAxis coordinate parameter) potential) =
      finiteExponentialVector (fun power => (generators coordinate ^ power) potential) (cutoff + 1) := by
    funext parameter
    rw [exponential, nilpotentExponential_real_parameter _ _ (nilpotent coordinate)]
  have smooth := (finiteExponentialVector_differentiable
    (fun power => (generators coordinate ^ power) potential) (cutoff + 1)).sub_const potential
  rw [← equality] at smooth
  exact smooth

theorem realRadicalCocycle_H1_zero_iff_lattice (representation : Representation ℂ RealPlaneRadical E)
    (continuous : ∀ element, Continuous (representation element))
    (generators : Fin 2 → Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : ∀ coordinate, generators coordinate ^ (cutoff + 1) = 0)
    (exponential : ∀ coordinate parameter, representation (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • generators coordinate))
    (cycle : groupCohomology.cocycles₁ (Rep.of representation))
    (regular : ∀ coordinate, DifferentiableAt ℝ (fun parameter => cycle (realRadicalAxis coordinate parameter)) 0) :
    groupCohomology.H1π (Rep.of representation) cycle = 0 ↔
      groupCohomology.H1π (Rep.of (representation.comp radicalLatticeReal))
        (realRadicalCocycleLattice representation cycle) = 0 := by
  constructor
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero ⊢
    obtain ⟨potential, boundary⟩ := zero
    refine ⟨potential, ?_⟩
    funext element
    exact congrFun boundary (radicalLatticeReal element)
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero
    obtain ⟨potential, boundary⟩ := zero
    change E at potential
    let realBoundary : groupCohomology.cocycles₁ (Rep.of representation) :=
      ⟨groupCohomology.d₀₁ (Rep.of representation) potential,
        groupCohomology.d₀₁_apply_mem_cocycles₁ (A := Rep.of representation) potential⟩
    have equality : cycle = realBoundary := by
      apply realRadicalCocycle_eq_of_generators representation continuous generators cutoff nilpotent exponential cycle realBoundary regular
      · intro coordinate
        exact (realRadicalBoundary_differentiable representation generators cutoff nilpotent exponential potential coordinate) 0
      · intro coordinate
        rw [realRadicalAxis_one]
        exact (congrFun boundary (radicalLatticeGenerator coordinate)).symm
    rw [equality, groupCohomology.H1π_eq_zero_iff]
    exact ⟨potential, rfl⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
