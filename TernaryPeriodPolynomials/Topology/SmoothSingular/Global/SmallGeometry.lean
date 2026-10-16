module

/- Adapted from the rational predecessor EquivariantSingularSmallGeometry.lean by explicit base-ring
replacement to ℝ and the actual SmoothSingularGlobal chain model. -/
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallComplex
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization SmoothSingularGlobal
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- Invariance of an actual subset under the given deck action. -/
def InvariantSet (S : Set E) : Prop := ∀ (g : G) (x : E), x ∈ S → g • x ∈ S

/-- Every member of an invariant cover is individually invariant under the actual deck action. -/
def InvariantCover (𝒰 : OpenCoverData E) : Prop := ∀ S ∈ 𝒰.sets, InvariantSet G E S

/-- The actual underlying simplex map respects the actual pointwise deck action. -/
theorem simplexMap_smul (n : ℕ) (g : G) (σ : SingularSimplex E n) :
    mvSimplexMap (g • σ) = g • mvSimplexMap σ :=
  singularEquiv_smul G E n g σ

/-- Subordination to an invariant subset is preserved by the deck action. -/
theorem subordinate_invariant (S : Set E) (hS : InvariantSet G E S) (n : ℕ)
    (g : G) (σ : SingularSimplex E n) (hσ : IsSubordinate S σ) : IsSubordinate S (g • σ) := by
  rintro _ ⟨x,rfl⟩
  rw [simplexMap_smul]
  exact hS g (mvSimplexMap σ x) (hσ ⟨x,rfl⟩)

/-- Smallness for an invariant open cover is preserved by the actual deck action. -/
theorem small_invariant (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) (n : ℕ)
    (g : G) (σ : SingularSimplex E n) (hσ : IsSmallSimplex 𝒰 σ) : IsSmallSimplex 𝒰 (g • σ) := by
  obtain ⟨S,hS,hσ⟩ := hσ
  exact ⟨S,hS,subordinate_invariant G E S (h𝒰 S hS) n g σ hσ⟩

/-- The genuine equivariant small-singular-chain complex of an invariant open cover. -/
def smallComplex (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) : ChainComplex (Rep ℝ G) ℕ :=
  familyComplex G E (fun _ => IsSmallSimplex 𝒰) (small_invariant G E 𝒰 h𝒰)
    (fun n => singularBoundary_maps_smallChainSubmodule (R := ℝ) (X := E) (𝒰 := 𝒰) n)

/-- The actual equivariant small-chain inclusion. -/
def smallInclusion (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) :
    smallComplex G E 𝒰 h𝒰 ⟶ equivariantChains G E :=
  familyInclusion G E (fun _ => IsSmallSimplex 𝒰) (small_invariant G E 𝒰 h𝒰)
    (fun n => singularBoundary_maps_smallChainSubmodule (R := ℝ) (X := E) (𝒰 := 𝒰) n)

/-- The genuine equivariant singular-chain complex subordinate to an actual invariant subset. -/
def subordinateComplex (S : Set E) (hS : InvariantSet G E S) : ChainComplex (Rep ℝ G) ℕ :=
  familyComplex G E (fun _ => IsSubordinate S) (subordinate_invariant G E S hS)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℝ) (X := E) (S := S) n)

/-- The literal inclusion of the actual invariant subset's subordinate singular chains. -/
def subordinateInclusion (S : Set E) (hS : InvariantSet G E S) :
    subordinateComplex G E S hS ⟶ equivariantChains G E :=
  familyInclusion G E (fun _ => IsSubordinate S) (subordinate_invariant G E S hS)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℝ) (X := E) (S := S) n)

/-- Forgetting the action identifies the actual small complex with the scalar subdivision-port complex. -/
def forgetSmallIso (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) :
    ((forget₂ (Rep ℝ G) (ModuleCat ℝ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (smallComplex G E 𝒰 h𝒰) ≅ smallChainComplex ℝ E 𝒰 :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    obtain rfl : i = j+1 := hij.symm
    simp only [smallComplex, familyComplex, smallChainComplex,
      Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d, Iso.refl_hom]
    rfl)

/-- Forgetting the action identifies the actual subordinate complex with the scalar subordinate complex. -/
def forgetSubordinateIso (S : Set E) (hS : InvariantSet G E S) :
    ((forget₂ (Rep ℝ G) (ModuleCat ℝ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (subordinateComplex G E S hS) ≅ subChainComplex ℝ E S :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    obtain rfl : i = j+1 := hij.symm
    simp only [subordinateComplex, familyComplex, subChainComplex,
      Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d, Iso.refl_hom]
    rfl)

/-- The forgetful identification preserves the literal small-chain inclusion, not merely its homology class. -/
theorem forgetSmallInclusion (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) :
    ((forget₂ (Rep ℝ G) (ModuleCat ℝ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (smallInclusion G E 𝒰 h𝒰) ≫ (forgetChainIso G E).hom =
      (forgetSmallIso G E 𝒰 h𝒰).hom ≫ smallChainsInclusion ℝ E 𝒰 := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- Actual small-chain representation degrees are projective for free actions. -/
instance smallComplex_projective [IsCancelSMul G E] (𝒰 : OpenCoverData E)
    (h𝒰 : InvariantCover G E 𝒰) (n : ℕ) : Projective ((smallComplex G E 𝒰 h𝒰).X n) :=
  familyComplex_projective G E (fun _ => IsSmallSimplex 𝒰) (small_invariant G E 𝒰 h𝒰)
    (fun n => singularBoundary_maps_smallChainSubmodule (R := ℝ) (X := E) (𝒰 := 𝒰) n) n

/-- Actual subordinate-chain representation degrees are projective for free actions. -/
instance subordinateComplex_projective [IsCancelSMul G E] (S : Set E)
    (hS : InvariantSet G E S) (n : ℕ) : Projective ((subordinateComplex G E S hS).X n) :=
  familyComplex_projective G E (fun _ => IsSubordinate S) (subordinate_invariant G E S hS)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℝ) (X := E) (S := S) n) n

end TernaryPoly.SmoothSingularGlobal
