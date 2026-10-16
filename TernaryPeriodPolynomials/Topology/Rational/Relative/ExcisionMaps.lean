module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Naturality

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeExcision
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The literal intersection viewed as a subspace of V. -/
def inside (U V : Set X) : Set V := {v | v.val ∈ U}

/-- The literal pair inclusion (V,U∩V) into (X,U), on actual relative rational chains. -/
def excisionMap (U V : Set X) : relativeChains (inside U V) ⟶ relativeChains U :=
  relativeMap ⟨Subtype.val,continuous_subtype_val⟩ (inside U V) U (fun _ h => h)

/-- The excision map is induced by the actual scalar subspace inclusion. -/
theorem excisionMap_projection (U V : Set X) :
    cokernel.π (inclusion (inside U V)) ≫ excisionMap U V =
      inclusion V ≫ cokernel.π (inclusion U) := by
  simp [excisionMap,relativeMap,cokernel.map]

/-- The nested subtype intersection is homeomorphic to the actual ambient intersection. -/
def insideHomeomorph (U V : Set X) : inside U V ≃ₜ ↥(U ∩ V) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Pair maps compose as their actual cokernel maps. -/
theorem relativeMap_comp {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) (S : Set X) (T : Set Y) (W : Set Z)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g T W) :
    relativeMap f S T hf ≫ relativeMap g T W hg =
      relativeMap (g.comp f) S W (hg.comp hf) := by
  apply (cancel_epi (cokernel.π (inclusion S))).mp
  simp only [relativeMap,cokernel.map,cokernel.π_desc_assoc,cokernel.π_desc,Category.assoc]
  rw [← Category.assoc,← RationalSingularAugmentation.chainMap_comp]

/-- Inclusion of a smaller excisive neighborhood commutes with the actual excision maps. -/
theorem excisionMap_natural (U V W : Set X) (hVW : V ⊆ W) :
    relativeMap (RationalSingularAugmentation.inclusion X V W hVW) (inside U V) (inside U W)
      (fun _ hx => hx) ≫ excisionMap U W = excisionMap U V := by
  unfold excisionMap
  erw [relativeMap_comp]
  rfl

end TernaryPoly.RationalRelativeExcision
