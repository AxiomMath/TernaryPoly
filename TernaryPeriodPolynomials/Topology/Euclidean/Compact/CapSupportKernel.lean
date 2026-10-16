module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationSupport
public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsComplexNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCapNormalization SingularLocalSupport
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularCoverNaturality
open EquivariantSingularSmall SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

/-- Every degreewise restriction-kernel element belongs to the actual kernel complex. -/
theorem kernel_degree_exists {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (r : C ⟶ D)
    (a : ℕ) (x : C.X a) (hx : r.f a x = 0) :
    ∃ y : (kernel r).X a, (kernel.ι r).f a y = x := by
  have h := (ShortComplex.kernelSequence_exact r).map
    (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a)
  have he := h.moduleCat_range_eq_ker
  have hmem : x ∈ LinearMap.ker (r.f a).hom := hx
  change x ∈ LinearMap.ker ((ShortComplex.kernelSequence r).map
    (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a)).g.hom at hmem
  rw [← he] at hmem
  exact hmem

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Literal scalar singular generators are carried to the literal image simplex. -/
theorem scalarSpaceMap_generator {Y : TopCat.{0}} (f : Y ⟶ X) (a : ℕ)
    (σ : SingularSimplex Y a) :
    (scalarSpaceMap f).f a (chainGenerator ℚ Y a σ) =
      chainGenerator ℚ X a (projection f a σ) :=
  congrArg (fun m => m.hom 1) (generator_map f a σ)

/-- Vanishing on the genuine complement-chain image forces actual geometric restriction
of an identity-cover cochain to vanish. -/
theorem restriction_zero_of_evaluation (K : Set X) (a : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (h : ∀ c, evaluation X V a φ ((RationalRelativeSingular.inclusion Kᶜ).f a c) = 0) :
    (localRestriction (𝟙 X) Kᶜ (constantRep V)).f a φ = 0 := by
  funext σ
  have hz := h (chainGenerator ℚ (TopCat.of ↥(Kᶜ)) a σ)
  change evaluation X V a φ ((scalarSpaceMap (sInclusion Kᶜ)).f a _) = 0 at hz
  rw [scalarSpaceMap_generator, evaluation_generator] at hz
  have hφ : φ (projection (sInclusion Kᶜ) a σ) = 0 :=
    (fiberEquiv X V _).injective (hz.trans (map_zero _).symm)
  apply Subtype.ext
  funext e
  change (φ (projection (sInclusion Kᶜ) a σ)).val _ = 0
  rw [hφ]
  rfl


/-- Actual support evaluation is injective in every degree. -/
theorem supportEvaluation_injective (K : Set X) (a : ℕ) :
    Function.Injective (supportEvaluation X V K a) := by
  intro φ ψ h
  apply (ModuleCat.mono_iff_injective ((supportInclusion (𝟙 X) (constantRep V) K).f a)).mp inferInstance
  apply (cochainHomEquiv X V a).injective
  apply LinearMap.ext
  intro c
  exact (supportEvaluation_projection X V K a φ c).symm.trans
    ((LinearMap.congr_fun h _).trans (supportEvaluation_projection X V K a ψ c))

end TernaryPoly.EuclideanCompactCap
