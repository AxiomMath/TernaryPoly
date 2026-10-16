module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.LiftCommutation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalCocycleDetection
public import Mathlib.GroupTheory.NoncommCoprod

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

def realRadicalAxisHom (coordinate : Fin 2) : Multiplicative ℝ →* RealPlaneRadical where
  toFun parameter := realRadicalAxis coordinate parameter.toAdd
  map_one' := realRadicalAxis_zero coordinate
  map_mul' first second := realRadicalAxis_add coordinate first.toAdd second.toAdd

theorem realRadicalAxisCoordinates_contDiff (coordinate : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => (realRadicalAxis coordinate parameter).toAdd) := by
  classical
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter : ℝ => (Pi.single coordinate parameter : Fin 2 → ℝ))
  apply contDiff_pi.mpr
  intro position
  fin_cases coordinate <;> fin_cases position <;> simp <;> fun_prop

def realRadicalCoordinatesHom : RealPlaneRadical →* Multiplicative ℝ × Multiplicative ℝ where
  toFun radical := (Multiplicative.ofAdd (radical.toAdd 0), Multiplicative.ofAdd (radical.toAdd 1))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem realRadicalTwoCocycle_exists_axisLifts {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (representation : Representation ℂ RealPlaneRadical E)
    (continuous : ∀ element, Continuous (representation element))
    (generators : Fin 2 → Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : ∀ coordinate, generators coordinate ^ (cutoff + 1) = 0)
    (exponential : ∀ coordinate parameter, representation (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • generators coordinate))
    (cycle : groupCohomology.cocycles₂ (Rep.of representation)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cycle (Multiplicative.ofAdd point.1, Multiplicative.ofAdd point.2)))
    (zero : groupCohomology.H2π (Rep.res radicalLatticeReal (Rep.of representation))
      (twoCocycleRestriction radicalLatticeReal (Rep.of representation) cycle) = 0) :
    ∃ lifts : Fin 2 → Multiplicative ℝ →* TwoCocycleExtension (Rep.of representation) cycle unit_zero,
      (∀ coordinate element, (lifts coordinate element).element = realRadicalAxisHom coordinate element) ∧
      (∀ coordinate, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => (lifts coordinate (Multiplicative.ofAdd parameter)).coefficient)) ∧
      ∀ first second, Commute (lifts 0 first) (lifts 1 second) := by
  obtain ⟨primitive, boundary⟩ := (groupCohomology.H2π_eq_zero_iff _).mp zero
  change RadicalLattice → E at primitive
  have boundary_value (first second : RadicalLattice) :
      representation (radicalLatticeReal first) (primitive second) - primitive (first * second) + primitive first =
        cycle (radicalLatticeReal first, radicalLatticeReal second) := congrFun boundary (first, second)
  let action (coordinate : Fin 2) (parameter : ℝ) : E →L[ℝ] E :=
    (⟨representation (realRadicalAxis coordinate parameter), continuous _⟩ : E →L[ℂ] E).restrictScalars ℝ
  have action_eq (coordinate : Fin 2) (parameter : ℝ) (vector : E) :
      action coordinate parameter vector = representation (realRadicalAxisHom coordinate (Multiplicative.ofAdd parameter)) vector := rfl
  have action_exponential (coordinate : Fin 2) (parameter : ℝ) (vector : E) :
      action coordinate parameter vector = IsNilpotent.exp ((parameter : ℂ) • generators coordinate) vector :=
    LinearMap.congr_fun (exponential coordinate parameter) vector
  have axis_regular (coordinate : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ =>
      cycle (realRadicalAxisHom coordinate (Multiplicative.ofAdd point.1),
        realRadicalAxisHom coordinate (Multiplicative.ofAdd point.2))) :=
    regular.comp (((realRadicalAxisCoordinates_contDiff coordinate).comp contDiff_fst).prodMk
      ((realRadicalAxisCoordinates_contDiff coordinate).comp contDiff_snd))
  have exists_lift (coordinate : Fin 2) := twoCocycleRealLift_exists representation cycle unit_zero
    (realRadicalAxisHom coordinate) (generators coordinate) cutoff (nilpotent coordinate) (action coordinate)
    (action_eq coordinate) (action_exponential coordinate) (axis_regular coordinate)
    (-primitive (radicalLatticeGenerator coordinate))
  choose lifts projects units lift_smooth using exists_lift
  have unit_commute : Commute (lifts 0 (Multiplicative.ofAdd 1)) (lifts 1 (Multiplicative.ofAdd 1)) := by
    apply TwoCocycleExtension.ext
    · change (lifts 0 (Multiplicative.ofAdd 1)).coefficient +
          representation (lifts 0 (Multiplicative.ofAdd 1)).element (lifts 1 (Multiplicative.ofAdd 1)).coefficient +
            cycle ((lifts 0 (Multiplicative.ofAdd 1)).element, (lifts 1 (Multiplicative.ofAdd 1)).element) =
        (lifts 1 (Multiplicative.ofAdd 1)).coefficient +
          representation (lifts 1 (Multiplicative.ofAdd 1)).element (lifts 0 (Multiplicative.ofAdd 1)).coefficient +
            cycle ((lifts 1 (Multiplicative.ofAdd 1)).element, (lifts 0 (Multiplicative.ofAdd 1)).element)
      simp only [units, projects]
      change -primitive (radicalLatticeGenerator 0) +
          representation (realRadicalAxis 0 1) (-primitive (radicalLatticeGenerator 1)) +
            cycle (realRadicalAxis 0 1, realRadicalAxis 1 1) =
        -primitive (radicalLatticeGenerator 1) +
          representation (realRadicalAxis 1 1) (-primitive (radicalLatticeGenerator 0)) +
            cycle (realRadicalAxis 1 1, realRadicalAxis 0 1)
      rw [realRadicalAxis_one, realRadicalAxis_one, map_neg, map_neg,
        ← boundary_value, ← boundary_value, mul_comm (radicalLatticeGenerator 0) (radicalLatticeGenerator 1)]
      abel
    · exact mul_comm _ _
  have commutation (coordinate : Fin 2)
      (element : TwoCocycleExtension (Rep.of representation) cycle unit_zero)
      (commutes : Commute element (lifts coordinate (Multiplicative.ofAdd 1))) :
      ∀ parameter, Commute element (lifts coordinate parameter) := by
    apply twoCocycleRealLift_commute_of_one representation cycle unit_zero (realRadicalAxisHom coordinate)
      (generators coordinate) cutoff (nilpotent coordinate) (action coordinate) (action_eq coordinate)
      (action_exponential coordinate) (lifts coordinate) (projects coordinate)
      ((lift_smooth coordinate).differentiable (by simp) 0) element (fun _ => Commute.all _ _)
      (continuous element.element) _ _ commutes
    · exact (regular.comp (contDiff_const.prodMk (realRadicalAxisCoordinates_contDiff coordinate))).differentiable (by simp) 0
    · exact (regular.comp ((realRadicalAxisCoordinates_contDiff coordinate).prodMk contDiff_const)).differentiable (by simp) 0
  have commute (first second : Multiplicative ℝ) : Commute (lifts 0 first) (lifts 1 second) := by
    have first_commutes := commutation 0 (lifts 1 (Multiplicative.ofAdd 1)) unit_commute.symm first
    exact commutation 1 (lifts 0 first) first_commutes.symm second
  exact ⟨lifts, projects, lift_smooth, commute⟩

theorem realRadicalTwoCocycle_H2_zero_of_lattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (representation : Representation ℂ RealPlaneRadical E)
    (continuous : ∀ element, Continuous (representation element))
    (generators : Fin 2 → Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : ∀ coordinate, generators coordinate ^ (cutoff + 1) = 0)
    (exponential : ∀ coordinate parameter, representation (realRadicalAxis coordinate parameter) =
      IsNilpotent.exp ((parameter : ℂ) • generators coordinate))
    (cycle : groupCohomology.cocycles₂ (Rep.of representation)) (unit_zero : cycle (1, 1) = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cycle (Multiplicative.ofAdd point.1, Multiplicative.ofAdd point.2)))
    (zero : groupCohomology.H2π (Rep.res radicalLatticeReal (Rep.of representation))
      (twoCocycleRestriction radicalLatticeReal (Rep.of representation) cycle) = 0) :
    groupCohomology.H2π (Rep.of representation) cycle = 0 := by
  obtain ⟨lifts, projects, _, commute⟩ := realRadicalTwoCocycle_exists_axisLifts representation continuous
    generators cutoff nilpotent exponential cycle unit_zero regular zero
  let splitting := ((lifts 0).noncommCoprod (lifts 1) commute).comp realRadicalCoordinatesHom
  have splitting_projects (element : RealPlaneRadical) :
      twoCocycleExtensionProjection (Rep.of representation) cycle unit_zero (splitting element) = element := by
    change (lifts 0 (Multiplicative.ofAdd (element.toAdd 0))).element *
      (lifts 1 (Multiplicative.ofAdd (element.toAdd 1))).element = element
    rw [projects, projects]
    exact realRadicalAxis_product element
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun element => -(splitting element).coefficient, ?_⟩
  funext pair
  exact twoCocycleExtension_section_boundary (Rep.of representation) cycle unit_zero splitting splitting_projects pair.1 pair.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
