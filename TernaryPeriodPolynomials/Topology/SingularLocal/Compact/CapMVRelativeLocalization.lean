module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVScalarExcision

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SphereOddDegree RationalRelativeSingular RationalRelativeExcision RationalLocalOrientation
open RationalSingularAugmentation

/-- Chains in a smaller excluded subset vanish in the actual quotient by a larger excluded subset. -/
theorem inclusion_project_zero {X : Type} [TopologicalSpace X] (A C : Set X) (hAC : A ⊆ C) :
    RationalRelativeSingular.inclusion A ≫ cokernel.π (RationalRelativeSingular.inclusion C) = 0 := by
  have h := inclusion_naturality (ContinuousMap.id X) A C hAC
  rw [chainMap_id,Category.comp_id] at h
  rw [h,Category.assoc,cokernel.condition,comp_zero]

/-- Canonical scalar localization kills actual small chains in every excluded subset disjoint
from the chosen support. -/
theorem localizeSmallScalar_zero {X : TopCat.{0}} (A K : Set X) (hAK : A ⊆ Kᶜ)
    (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    smallPush (sInclusion A) 𝒰 ≫
      localizeSmallScalar K hK U hKU 𝒰 href = 0 := by
  have := scalarSupportExcision_mono K hK U hKU
  rw [← cancel_mono (supportExcisionMap K U),zero_comp,Category.assoc,localizeSmallScalar_excision,
    ← Category.assoc,smallPush_inclusion,Category.assoc]
  change smallChainsInclusion ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰) ≫
    (RationalRelativeSingular.inclusion A ≫ cokernel.π (RationalRelativeSingular.inclusion Kᶜ)) = 0
  rw [inclusion_project_zero A Kᶜ hAK,comp_zero]

/-- The actual relative-small scalar chains localize to actual relative scalar chains of the
open support neighborhood, without any choice of representatives. -/
def relativeLocalizeScalar {X : TopCat.{0}} (A K : Set X) (hAK : A ⊆ Kᶜ)
    (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    cokernel (smallPush (sInclusion A) 𝒰) ⟶
      relativeChains ((Subtype.val : U → X) ⁻¹' K)ᶜ :=
  cokernel.desc _ (localizeSmallScalar K hK U hKU 𝒰 href)
    (localizeSmallScalar_zero A K hAK hK U hKU 𝒰 href)

/-- The actual relative-localization morphism retains its chain-level localization formula. -/
theorem relativeLocalizeScalar_projection {X : TopCat.{0}} (A K : Set X) (hAK : A ⊆ Kᶜ)
    (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    cokernel.π (smallPush (sInclusion A) 𝒰) ≫
      relativeLocalizeScalar A K hAK hK U hKU 𝒰 href = localizeSmallScalar K hK U hKU 𝒰 href :=
  cokernel.π_desc _ _ _

/-- Localization followed by the genuine excision inclusion is the actual relative-small
comparison followed by the literal map enlarging the excluded subset. -/
theorem relativeLocalizeScalar_excision {X : TopCat.{0}} (A K : Set X) (hAK : A ⊆ Kᶜ)
    (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    relativeLocalizeScalar A K hAK hK U hKU 𝒰 href ≫ supportExcisionMap K U =
      relativeSmallMap A 𝒰 ≫ relativeMap (ContinuousMap.id X) A Kᶜ hAK := by
  apply (cancel_epi (cokernel.π (smallPush (sInclusion A) 𝒰))).mp
  rw [← Category.assoc,relativeLocalizeScalar_projection,localizeSmallScalar_excision,
    ← Category.assoc,relativeSmallMap_projection,Category.assoc]
  simp only [RationalRelativeSingular.relativeMap,cokernel.map,cokernel.π_desc,chainMap_id,Category.id_comp]

end TernaryPoly.SingularLocalCompactCapMV
