module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Evaluation
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicFiniteEvaluation

theorem exists_coefficients {Scalars Vector Point : Type*} [Field Scalars]
    [AddCommGroup Vector] [Module Scalars Vector] [FiniteDimensional Scalars Vector]
    (realization : Vector →ₗ[Scalars] (Point → Scalars)) (injective : Function.Injective realization)
    (functional : Vector →ₗ[Scalars] Scalars) :
    ∃ samples : Finset Point, ∃ coefficients : samples → Scalars,
      ∀ vector, functional vector = ∑ point : samples, coefficients point * realization vector point.val := by
  classical
  obtain ⟨samples, detectsZero⟩ := FiniteEvaluation.exists_samples realization injective
  let sampleMap : Vector →ₗ[Scalars] (samples → Scalars) :=
    LinearMap.pi (fun point => (LinearMap.proj point.val).comp realization)
  have kernel : sampleMap.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro vector membership
    apply (Submodule.mem_bot Scalars).mpr
    apply detectsZero vector
    intro point inside
    exact congrFun membership ⟨point, inside⟩
  obtain ⟨inverse, inverseProperty⟩ := sampleMap.exists_leftInverse_of_injective kernel
  let extension := functional.comp inverse
  refine ⟨samples, (fun point => extension (Pi.single point 1)), ?_⟩
  intro vector
  have reconstruction : extension (sampleMap vector) = functional vector := by
    change functional ((inverse.comp sampleMap) vector) = _
    rw [inverseProperty, LinearMap.id_apply]
  have decomposition : sampleMap vector = ∑ point : samples, (realization vector point.val) • Pi.single point 1 := by
    funext point
    simp [sampleMap, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [← reconstruction, decomposition, map_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_meromorphic {Vector Point : Type*} [AddCommGroup Vector] [Module ℂ Vector]
    [FiniteDimensional ℂ Vector] (realization : Vector →ₗ[ℂ] (Point → ℂ))
    (injective : Function.Injective realization) (domain : Set ℂ) (family : domain → Vector)
    (scalarContinuations : ∀ point, ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : domain, continuation parameter.val = realization (family parameter) point)
    (functional : Vector →ₗ[ℂ] ℂ) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : domain, continuation parameter.val = functional (family parameter) := by
  obtain ⟨samples, coefficients, expression⟩ := exists_coefficients realization injective functional
  choose continuations meromorphic equalities using fun point : samples => scalarContinuations point.val
  refine ⟨fun parameter => ∑ point : samples, coefficients point * continuations point parameter, ?_, ?_⟩
  · intro parameter
    apply MeromorphicAt.fun_sum
    intro point _
    exact analyticAt_const.meromorphicAt.mul (meromorphic point parameter)
  · intro parameter
    rw [expression]
    apply Finset.sum_congr rfl
    intro point _
    rw [equalities point parameter]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicFiniteEvaluation
