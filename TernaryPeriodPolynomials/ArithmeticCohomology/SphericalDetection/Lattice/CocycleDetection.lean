module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G] (representation : Rep ℂ G)

theorem oneCocycle_mul (cycle : groupCohomology.cocycles₁ representation) (first second : G) :
    cycle (first * second) = representation.ρ first (cycle second) + cycle first :=
  (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second

theorem oneCocycle_generator_closed (cycle : groupCohomology.cocycles₁ representation)
    (first second : G) (commute : Commute first second) :
    (representation.ρ first - 1) (cycle second) = (representation.ρ second - 1) (cycle first) := by
  have first_eq := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
  have second_eq := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property second first
  rw [commute.eq] at first_eq
  have equality := first_eq.symm.trans second_eq
  change representation.ρ first (cycle second) - cycle second = representation.ρ second (cycle first) - cycle first
  exact sub_eq_sub_iff_add_eq_add.mpr equality

theorem oneCocycle_pow_zero (cycle : groupCohomology.cocycles₁ representation)
    (generator : G) (zero : cycle generator = 0) (power : ℕ) : cycle (generator ^ power) = 0 := by
  induction power with
  | zero =>
    rw [pow_zero]
    exact groupCohomology.cocycles₁_map_one cycle
  | succ power induction =>
    rw [pow_succ, oneCocycle_mul,
      zero, induction, map_zero, zero_add]

theorem oneCocycle_inverse_zero (cycle : groupCohomology.cocycles₁ representation)
    (element : G) (zero : cycle element = 0) : cycle element⁻¹ = 0 := by
  have equation := groupCohomology.cocycles₁_map_inv cycle element
  rw [zero, neg_zero] at equation
  have inverse_eq := congrArg (representation.ρ element⁻¹) equation
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at inverse_eq
  exact inverse_eq

theorem oneCocycle_zpow_zero (cycle : groupCohomology.cocycles₁ representation)
    (generator : G) (zero : cycle generator = 0) (power : ℤ) : cycle (generator ^ power) = 0 := by
  cases power with
  | ofNat power =>
    change cycle (generator ^ (power : ℤ)) = 0
    rw [zpow_natCast]
    exact oneCocycle_pow_zero representation cycle generator zero power
  | negSucc power =>
    rw [zpow_negSucc]
    exact oneCocycle_inverse_zero representation cycle _
      (oneCocycle_pow_zero representation cycle generator zero (power + 1))

theorem oneCocycle_eq_zero_of_two_generators (cycle : groupCohomology.cocycles₁ representation)
    (first second : G) (generated : ∀ element : G, ∃ first_power second_power : ℤ,
      element = first ^ first_power * second ^ second_power)
    (first_zero : cycle first = 0) (second_zero : cycle second = 0) : cycle = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro element
  obtain ⟨first_power, second_power, rfl⟩ := generated element
  change cycle (first ^ first_power * second ^ second_power) = 0
  rw [oneCocycle_mul,
    oneCocycle_zpow_zero representation cycle first first_zero first_power,
    oneCocycle_zpow_zero representation cycle second second_zero second_power, map_zero, zero_add]

theorem oneCocycle_eq_of_two_generators (first_cycle second_cycle : groupCohomology.cocycles₁ representation)
    (first second : G) (generated : ∀ element : G, ∃ first_power second_power : ℤ,
      element = first ^ first_power * second ^ second_power)
    (first_eq : first_cycle first = second_cycle first)
    (second_eq : first_cycle second = second_cycle second) : first_cycle = second_cycle := by
  apply sub_eq_zero.mp
  apply oneCocycle_eq_zero_of_two_generators representation (first_cycle - second_cycle) first second generated
  · change first_cycle first - second_cycle first = 0
    rw [first_eq, sub_self]
  · change first_cycle second - second_cycle second = 0
    rw [second_eq, sub_self]

theorem oneCocycle_H1_zero_iff_generator_boundaries (cycle : groupCohomology.cocycles₁ representation)
    (first second : G) (generated : ∀ element : G, ∃ first_power second_power : ℤ,
      element = first ^ first_power * second ^ second_power) :
    groupCohomology.H1π representation cycle = 0 ↔
      ∃ potential : representation,
        cycle first = (representation.ρ first - 1) potential ∧
        cycle second = (representation.ρ second - 1) potential := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    refine ⟨potential, ?_, ?_⟩
    · exact (congrFun equality first).symm
    · exact (congrFun equality second).symm
  · rintro ⟨potential, first_eq, second_eq⟩
    refine ⟨potential, ?_⟩
    let boundary : groupCohomology.cocycles₁ representation :=
      ⟨groupCohomology.d₀₁ representation potential, groupCohomology.d₀₁_apply_mem_cocycles₁ potential⟩
    have equality : cycle = boundary := oneCocycle_eq_of_two_generators representation cycle boundary
      first second generated first_eq second_eq
    exact congrArg (fun value : groupCohomology.cocycles₁ representation => value.val) equality.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
