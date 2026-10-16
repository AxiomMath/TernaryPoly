module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphCap
public import Mathlib.Geometry.Manifold.HasGroupoid

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- The literal nested projection has the quotient-covering fact for its canonical action. -/
instance nestedCoveringFact (A D : Set B) :
    Fact (IsQuotientCoveringMap (nestedProjection p A D) G) :=
  ⟨restrictedQuotientCovering (restrictedProjection p D) (Subtype.val ⁻¹' A)⟩

/-- Flattening an iterated restriction is an actual equivariant covering homeomorphism. -/
def nestedCoverHomeomorph (A D : Set B) :
    CoverHomeomorph (G := G) (nestedProjection p A D) (restrictedProjection p (A ∩ D)) where
  total := nestedTotalHomeomorph p A D
  base := nestedBaseHomeomorph A D
  square := nestedFlatten_square p A D
  equivariant _ _ := rfl

/-- The actual flattening to a contained open retains its exact base and total-space values. -/
def nestedSubsetCoverHomeomorph (A D : Set B) (hAD : A ⊆ D) :
    CoverHomeomorph (G := G) (nestedProjection p A D) (restrictedProjection p A) where
  total := {
    toFun x := ⟨x.val.val,x.property⟩
    invFun x := ⟨⟨x.val,hAD x.property⟩,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  base := {
    toFun x := ⟨x.val.val,x.property⟩
    invFun x := ⟨⟨x.val,hAD x.property⟩,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  square := rfl
  equivariant _ _ := rfl

/-- Restriction to the whole base is the actual original covering up to literal subtype removal. -/
def univCoverHomeomorph : CoverHomeomorph (G := G) (restrictedProjection p Set.univ) p where
  total := Homeomorph.Set.univ E
  base := Homeomorph.Set.univ B
  square := rfl
  equivariant _ _ := rfl

end TernaryPoly.SingularLocalCompactDuality
