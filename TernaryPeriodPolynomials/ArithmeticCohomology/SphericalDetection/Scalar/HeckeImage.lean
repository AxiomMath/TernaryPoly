module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Commutativity
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Smooth spherical vectors whose actual scalar realization is holomorphic of the specified weight. -/
def cuspClassicalVectors (cusp : CuspidalRepresentation) (halfWeight : ℤ) : Submodule ℂ cusp.smooth where
  carrier := {vector | vector.val ∈ cuspSphericalValues cusp ∧
    (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) ∧
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinear cusp halfWeight 1 vector)}
  zero_mem' := by
    refine ⟨(cuspSphericalValues cusp).zero_mem, ?_, ?_⟩
    · intro angle
      simp
    · rw [map_zero]
      exact mdifferentiable_const
  add_mem' first second := by
    refine ⟨(cuspSphericalValues cusp).add_mem first.1 second.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_add, map_add, first.2.1 angle, second.2.1 angle, smul_add]
    · rw [map_add]
      exact first.2.2.add second.2.2
  smul_mem' scalar vector member := by
    refine ⟨(cuspSphericalValues cusp).smul_mem scalar member.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_smul, map_smul, member.2.1 angle]
      exact smul_comm _ _ _
    · rw [map_smul]
      exact member.2.2.const_smul scalar

theorem cuspFiniteRationalSlash_scalar_holomorphic (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinear cusp halfWeight 1 vector))
    (rational : BinaryRationalGL)
    (positive : 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinear cusp halfWeight 1
      (cuspFiniteRationalSlash cusp rational vector)) := by
  rw [cuspFiniteRationalSlash_eq_slash cusp central_positive halfWeight vector rotation rational positive]
  exact (holomorphic.slash _ _).const_smul _

theorem cuspPrimeHeckeSum_classical (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (prime : Nat.Primes) (vector : cusp.smooth)
    (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight) :
    cuspPrimeHeckeSum cusp prime vector ∈ cuspClassicalVectors cusp halfWeight := by
  refine ⟨cuspPrimeHeckeSum_spherical cusp prime vector classical_vector.1,
    cuspPrimeHeckeSum_rotation cusp prime (2 * halfWeight) vector classical_vector.2.1, ?_⟩
  simp only [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  apply MDifferentiable.add
  · exact cuspFiniteRationalSlash_scalar_holomorphic cusp central_positive halfWeight vector
      classical_vector.2.1 classical_vector.2.2 _ (by
        rw [binaryHeckeDilate_det]
        exact_mod_cast prime.property.pos)
  · apply MDifferentiable.sum
    intro index _
    exact cuspFiniteRationalSlash_scalar_holomorphic cusp central_positive halfWeight vector
      classical_vector.2.1 classical_vector.2.2 _ (by
        rw [binaryHeckeTranslate_det]
        exact_mod_cast prime.property.pos)

/-- The same unnormalized Hecke formula, acting on scalar functions. -/
def scalarPrimeHecke (halfWeight : ℤ) (prime : Nat.Primes) :
    Module.End ℂ (UpperHalfPlane → ℂ) where
  toFun function point :=
    (prime.val : ℂ) ^ (-halfWeight) * function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
    (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val, function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate prime.val prime.property.pos index) • point)
  map_add' first second := by
    funext point
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar function := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem cuspPrimeHeckeSum_scalar_intertwines (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (prime : Nat.Primes) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) :
    cuspScalarWeightedLinear cusp halfWeight 1 (cuspPrimeHeckeSum cusp prime vector) =
      scalarPrimeHecke halfWeight prime (cuspScalarWeightedLinear cusp halfWeight 1 vector) := by
  funext point
  simpa only [scalarPrimeHecke, LinearMap.coe_mk, AddHom.coe_mk, cuspScalarWeightedLinear,
    binaryHeckeDilate_smul, binaryHeckeTranslate_smul] using
    cuspPrimeHeckeSum_scalar cusp central_positive halfWeight vector rotation prime point

def cuspClassicalScalarImage (cusp : CuspidalRepresentation) (halfWeight : ℤ) :
    Submodule ℂ (UpperHalfPlane → ℂ) :=
  ((cuspScalarWeightedLinear cusp halfWeight 1).comp (cuspClassicalVectors cusp halfWeight).subtype).range

theorem cuspClassicalScalarImage_mem (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (function : UpperHalfPlane → ℂ) :
    function ∈ cuspClassicalScalarImage cusp halfWeight ↔
      ∃ vector : cusp.smooth, vector ∈ cuspClassicalVectors cusp halfWeight ∧
        cuspScalarWeightedLinear cusp halfWeight 1 vector = function := by
  constructor
  · rintro ⟨vector, equality⟩
    exact ⟨vector.val, vector.property, equality⟩
  · rintro ⟨vector, member, equality⟩
    exact ⟨⟨vector, member⟩, equality⟩

theorem cuspClassicalScalarImage_stable (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (prime : Nat.Primes) (function : UpperHalfPlane → ℂ)
    (member : function ∈ cuspClassicalScalarImage cusp halfWeight) :
    scalarPrimeHecke halfWeight prime function ∈ cuspClassicalScalarImage cusp halfWeight := by
  obtain ⟨vector, classical_vector, rfl⟩ := (cuspClassicalScalarImage_mem cusp halfWeight function).mp member
  rw [← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight prime vector classical_vector.2.1]
  exact (cuspClassicalScalarImage_mem cusp halfWeight _).mpr ⟨_,
    cuspPrimeHeckeSum_classical cusp central_positive halfWeight prime vector classical_vector, rfl⟩

def cuspScalarImageHecke (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (prime : Nat.Primes) : Module.End ℂ (cuspClassicalScalarImage cusp halfWeight) :=
  (scalarPrimeHecke halfWeight prime).restrict
    (cuspClassicalScalarImage_stable cusp central_positive halfWeight prime)

theorem cuspScalarImageHecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (first second : Nat.Primes) :
    Commute (cuspScalarImageHecke cusp central_positive halfWeight first)
      (cuspScalarImageHecke cusp central_positive halfWeight second) := by
  change _ = _
  ext function point
  obtain ⟨vector, classical_vector, equality⟩ :=
    (cuspClassicalScalarImage_mem cusp halfWeight function.val).mp function.property
  change scalarPrimeHecke halfWeight first (scalarPrimeHecke halfWeight second function.val) point =
    scalarPrimeHecke halfWeight second (scalarPrimeHecke halfWeight first function.val) point
  rw [← equality, ← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight second vector classical_vector.2.1,
    ← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight first vector classical_vector.2.1,
    ← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight first _
      (cuspPrimeHeckeSum_rotation cusp second (2 * halfWeight) vector classical_vector.2.1),
    ← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight second _
      (cuspPrimeHeckeSum_rotation cusp first (2 * halfWeight) vector classical_vector.2.1),
    cuspPrimeHeckeSum_commute cusp first second vector classical_vector.1]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
