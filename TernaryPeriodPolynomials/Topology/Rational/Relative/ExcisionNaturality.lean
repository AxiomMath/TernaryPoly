module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionPoint

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeExcision
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual excision homology isomorphisms commute with smaller excisive neighborhoods. -/
theorem excisionHomologyIso_natural (U V W : Opens X) (hUV : U ⊔ V = ⊤)
    (hUW : U ⊔ W = ⊤) (hVW : V ≤ W) (n : ℕ) :
    homologyMap (relativeMap (RationalSingularAugmentation.inclusion X V W hVW)
      (inside (U : Set X) (V : Set X)) (inside (U : Set X) (W : Set X)) (fun _ hx => hx)) n ≫
        (excisionHomologyIso U W hUW n).hom = (excisionHomologyIso U V hUV n).hom := by
  rw [excisionHomologyIso_hom,excisionHomologyIso_hom,← homologyMap_comp]
  erw [excisionMap_natural (U : Set X) (V : Set X) (W : Set X) hVW]

/-- The literal inclusion of punctured neighborhoods is itself an actual map of pairs. -/
def pointNeighborhoodMap (x : X) (V W : Set X) (hxV : x ∈ V) (hxW : x ∈ W) (hVW : V ⊆ W) :
    relativeChains ({(⟨x,hxV⟩ : V)}ᶜ : Set V) ⟶ relativeChains ({(⟨x,hxW⟩ : W)}ᶜ : Set W) :=
  relativeMap (RationalSingularAugmentation.inclusion X V W hVW) _ _
    (fun _ hv h => hv (Subtype.ext (congrArg (Subtype.val : W → X) h)))

/-- The actual point-local pair inclusion commutes with inclusion of a smaller neighborhood. -/
theorem pointExcisionMap_natural (x : X) (V W : Set X) (hxV : x ∈ V) (hxW : x ∈ W) (hVW : V ⊆ W) :
    pointNeighborhoodMap x V W hxV hxW hVW ≫ pointExcisionMap x W hxW = pointExcisionMap x V hxV := by
  rw [pointExcisionMap_eq_relativeMap,pointExcisionMap_eq_relativeMap]
  unfold pointNeighborhoodMap
  erw [relativeMap_comp]
  rfl

/-- Actual local homology isomorphisms are natural under inclusion of smaller open neighborhoods. -/
theorem pointLocalHomologyIso_natural [T1Space X] (x : X) (V W : Opens X)
    (hxV : x ∈ V) (hxW : x ∈ W) (hVW : V ≤ W) (n : ℕ) :
    homologyMap (pointNeighborhoodMap x (V : Set X) (W : Set X) hxV hxW hVW) n ≫
      (pointLocalHomologyIso x W hxW n).hom = (pointLocalHomologyIso x V hxV n).hom := by
  rw [pointLocalHomologyIso_hom,pointLocalHomologyIso_hom,← homologyMap_comp]
  erw [pointExcisionMap_natural x (V : Set X) (W : Set X) hxV hxW hVW]

end TernaryPoly.RationalRelativeExcision
