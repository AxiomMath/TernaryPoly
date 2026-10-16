module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVHomology
public import TernaryPeriodPolynomials.Topology.SingularHomology.SmallChainsQuasiIso
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionSmall

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open ContractibleSingularHomology RationalRelativeSingular

/-- Pull an actual open cover back along an actual continuous map. -/
def pulledCover {X Y : TopCat.{0}} (f : X ⟶ Y) (𝒰 : OpenCoverData Y) : OpenCoverData X where
  sets := (fun U : Set Y => f ⁻¹' U) '' 𝒰.sets
  isOpen_mem := by
    rintro _ ⟨U,hU,rfl⟩
    exact (𝒰.isOpen_mem U hU).preimage f.hom.continuous
  covers x := by
    obtain ⟨U,hU,hx⟩ := 𝒰.covers (f x)
    exact ⟨f ⁻¹' U,⟨U,hU,rfl⟩,hx⟩

/-- Pushforward of an actually small simplex for a pulled-back cover is small. -/
theorem pushed_small {X Y : TopCat.{0}} (f : X ⟶ Y) (𝒰 : OpenCoverData Y) (n : ℕ)
    (σ : singularSimplices X n) (hσ : IsSmallSimplex (pulledCover f 𝒰) σ) :
    IsSmallSimplex 𝒰 (pushSimplex f n σ) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hσ⟩ := hσ
  refine ⟨U,hU,?_⟩
  rintro _ ⟨x,rfl⟩
  have hx := hσ (Set.mem_range_self x)
  change f ((singularSimplexAsContinuousMap X n σ) x) ∈ U at hx
  simpa only [mvSimplexMap,pushSimplex_continuousMap,ContinuousMap.comp_apply] using hx

/-- Actual scalar pushforward preserves small-chain submodules for the pulled cover. -/
theorem push_small_chains {X Y : TopCat.{0}} (f : X ⟶ Y) (𝒰 : OpenCoverData Y) (n : ℕ)
    (c : singularChainGroup ℚ X n) (hc : c ∈ smallChainSubmodule ℚ X (pulledCover f 𝒰) n) :
    (singularChainMap ℚ f n).hom c ∈ smallChainSubmodule ℚ Y 𝒰 n := by
  apply smallChainSubmodule_induction (c := c) (𝒰 := pulledCover f 𝒰) (R := ℚ) (n := n) (p := fun x =>
    (singularChainMap ℚ f n).hom x ∈ smallChainSubmodule ℚ Y 𝒰 n) _ _ _ _ hc
  · intro σ hσ
    rw [singularChainMap_generator]
    exact chainGenerator_mem_smallChainSubmodule (pushed_small f 𝒰 n σ hσ)
  · simpa only [map_zero] using (Submodule.zero_mem (smallChainSubmodule ℚ Y 𝒰 n))
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem (smallChainSubmodule ℚ Y 𝒰 n) hx hy
  · intro r x hx
    simpa only [map_smul] using Submodule.smul_mem (smallChainSubmodule ℚ Y 𝒰 n) r hx

/-- The actual pushforward chain map on small chains for a pulled-back cover. -/
def smallPush {X Y : TopCat.{0}} (f : X ⟶ Y) (𝒰 : OpenCoverData Y) :
    smallChainComplex ℚ X (pulledCover f 𝒰) ⟶ smallChainComplex ℚ Y 𝒰 where
  f n := ModuleCat.ofHom (((singularChainMap ℚ f n).hom.comp
    (smallChainSubmodule ℚ X (pulledCover f 𝒰) n).subtype).codRestrict
      (smallChainSubmodule ℚ Y 𝒰 n) (fun c => push_small_chains f 𝒰 n c.val c.property))
  comm' i j hij := by
    obtain rfl : i = j+1 := hij.symm
    simp only [smallChainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun g => g c.val) (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map f |>.comm (j+1) j)

/-- The actual small pushforward commutes with literal inclusions into scalar singular chains. -/
theorem smallPush_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (𝒰 : OpenCoverData Y) :
    smallPush f 𝒰 ≫ smallChainsInclusion ℚ Y 𝒰 =
      smallChainsInclusion ℚ X (pulledCover f 𝒰) ≫
        ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map f := by
  ext n c
  rfl

/-- The actual inclusion from small subspace chains to small ambient chains is monic. -/
instance smallSubspacePush_mono {X : TopCat.{0}} (A : Set X) (𝒰 : OpenCoverData X) :
    Mono (smallPush (sInclusion A) 𝒰) := by
  have : Mono (smallChainsInclusion ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰)) := by
    apply mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have h := smallPush_inclusion (sInclusion A) 𝒰
  have : Mono (smallPush (sInclusion A) 𝒰 ≫ smallChainsInclusion ℚ X 𝒰) := by
    rw [h]
    change Mono (smallChainsInclusion ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰) ≫ inclusion A)
    infer_instance
  exact mono_of_mono (smallPush (sInclusion A) 𝒰) (smallChainsInclusion ℚ X 𝒰)

/-- The genuine relative-small scalar complex maps to the literal relative scalar chains. -/
def relativeSmallMap {X : TopCat.{0}} (A : Set X) (𝒰 : OpenCoverData X) :
    cokernel (smallPush (sInclusion A) 𝒰) ⟶ relativeChains A :=
  cokernel.map _ (inclusion A)
    (smallChainsInclusion ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰))
    (smallChainsInclusion ℚ X 𝒰) (smallPush_inclusion (sInclusion A) 𝒰)

/-- Verified subdivision on both actual absolute complexes proves relative small-chain excision. -/
instance relativeSmallMap_quasiIso {X : TopCat.{0}} (A : Set X) (𝒰 : OpenCoverData X) :
    QuasiIso (relativeSmallMap A 𝒰) := by
  have h₁ := smallChains_inclusion_quasiIso ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰)
  have h₂ := smallChains_inclusion_quasiIso ℚ X 𝒰
  exact @RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _
    (smallPush (sInclusion A) 𝒰) (inclusion A) inferInstance inferInstance
    (smallChainsInclusion ℚ (TopCat.of A) (pulledCover (sInclusion A) 𝒰))
    (smallChainsInclusion ℚ X 𝒰) (smallPush_inclusion (sInclusion A) 𝒰) h₁ h₂

/-- The genuine relative-small comparison preserves the actual quotient projection. -/
theorem relativeSmallMap_projection {X : TopCat.{0}} (A : Set X) (𝒰 : OpenCoverData X) :
    cokernel.π (smallPush (sInclusion A) 𝒰) ≫ relativeSmallMap A 𝒰 =
      smallChainsInclusion ℚ X 𝒰 ≫ cokernel.π (inclusion A) := by
  exact cokernel.π_desc _ _ _

end TernaryPoly.SingularLocalCompactCapMV
