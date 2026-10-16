module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileTestFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ProfileBoxes
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.GodementFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages

variable {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}

structure RealFamily (data : InducingData degree) where
  Source : Type
  [normedGroup : NormedAddCommGroup Source]
  [normedSpace : NormedSpace ℂ Source]
  [complete : CompleteSpace Source]
  family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence
  tests : ℂ → SchwartzMap RealSpace Source
  continuous : Continuous (fun vector => (family vector).val.val)
  holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector)
  bounded : ∀ parameters : Set ℂ, IsCompact parameters → UniformSchwartzBounds.Bounded (tests '' parameters)

attribute [instance] RealFamily.normedGroup RealFamily.normedSpace RealFamily.complete

theorem exists_realFamily (flat : IsFlatSection data sectionFunction) (point : IntegralFiniteGL)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ result : RealFamily data, ∀ parameter value,
      (result.family (result.tests parameter value)).val =
        cutoff (coordinateEquiv.symm value) •
          profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point)
            (coordinateEquiv.symm value)) := by
  obtain ⟨indices, radii, positive, tests, _, _, holomorphic, bounded, image⟩ :=
    FlatProfileTestFamilies.exists_family flat point cutoff smooth compact supported
  refine ⟨{
    Source := ProductStages.Source data.cusp radii positive
    family := ProductStages.smoothMap data.cusp radii positive
    tests := tests
    continuous := ProductStages.smoothMap_continuous data.cusp radii positive
    holomorphic := holomorphic
    bounded := fun parameters compact => UniformSchwartzBounds.image_family tests parameters (bounded parameters compact)
  }, ?_⟩
  intro parameter value
  apply Subtype.ext
  exact (ProductStages.smoothMap_hilbert data.cusp radii positive _).trans (image parameter value)

abbrev Key (flat : IsFlatSection data sectionFunction) := Set.range (profileKey flat)

instance keyFintype (flat : IsFlatSection data sectionFunction) : Fintype (Key flat) :=
  (key_finite_range flat).fintype

def representative (flat : IsFlatSection data sectionFunction) (key : Key flat) : IntegralFiniteGL :=
  Classical.choose key.property

theorem representative_key (flat : IsFlatSection data sectionFunction) (key : Key flat) :
    profileKey flat (representative flat key) = key.val :=
  Classical.choose_spec key.property

structure Boxes where
  scale : ℚˣ
  indices : Finset (FiniteLatticeCosets.Space ⧸ FiniteLatticeCosets.latticeSubgroup
    (FiniteLatticeMeasure.rationalScale scale))
  coefficients : (FiniteLatticeCosets.Space ⧸ FiniteLatticeCosets.latticeSubgroup
    (FiniteLatticeMeasure.rationalScale scale)) → ℂ

def Boxes.test (boxes : Boxes) (value : Rectangular FiniteAdeles) : ℂ :=
  ∑ coset ∈ boxes.indices, boxes.coefficients coset *
    RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale boxes.scale) coset.out value

theorem exists_boxes (flat : IsFlatSection data sectionFunction) (key : Key flat) :
    ∃ boxes : Boxes, ∀ point : IntegralFiniteGL,
      boxes.test (embedding (CompactFiniteFrames.frame point)) = if profileKey flat point = key.val then 1 else 0 := by
  obtain ⟨scale, indices, coefficients, equality⟩ := FiniteProfileBoxes.exists_expansion flat key.val
  exact ⟨⟨scale, indices, coefficients⟩, equality⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages
