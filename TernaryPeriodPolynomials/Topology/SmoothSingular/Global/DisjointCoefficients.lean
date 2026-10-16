module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointCover

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory TopologicalSpace
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)

/-- The actual quotient component opens as objects of the open-set lattice. -/
def opens (i : ι) : Opens (TopCat.of OrbitSpace) := ⟨U.domain i,U.isOpen_domain i⟩

theorem subset_iSup : V ⊆ (iSup U.opens : Opens (TopCat.of OrbitSpace)) := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp (U.covers hx)
  exact Opens.mem_iSup.mpr ⟨i,hi⟩

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Actual coefficient restrictions to a disjoint cover. -/
def restrictCoefficients : coefficientSections ρ V →ₗ[ℝ]
    (∀ i, coefficientSections ρ (U.domain i)) where
  toFun f i := coefficientRestriction ρ (U.subset i) f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every family of actual coefficient sections on disjoint opens is compatible. -/
theorem coefficients_compatible (w : ∀ i, coefficientSections ρ (U.domain i)) :
    (coefficientPresheaf ρ).IsCompatible U.opens w := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    exact False.elim ((U.disjoint hij).le_bot ⟨x.property.2.1,x.property.2.2⟩)

/-- The genuine coefficient sheaf glues every disjoint family to the original covered open. -/
def extendCoefficients (w : ∀ i, coefficientSections ρ (U.domain i)) : coefficientSections ρ V :=
  coefficientRestriction ρ U.subset_iSup (gluedCoefficient ρ U.opens w (U.coefficients_compatible ρ w))

/-- The actual disjoint coefficient extension has each prescribed component value. -/
theorem extendCoefficients_value (w : ∀ i, coefficientSections ρ (U.domain i))
    (i : ι) (x : CoverOpen V) (hx : coordinateProjection x.val ∈ U.domain i) :
    (U.extendCoefficients ρ w).val x = (w i).val ⟨x.val,x.property.1,hx⟩ :=
  gluedCoefficientFun_apply ρ U.opens w (U.coefficients_compatible ρ w) i
    ⟨x.val,liftedDomain_mono U.subset_iSup x.property⟩ ⟨x.property.1,hx⟩

/-- Actual coefficients are uniquely determined by their disjoint restrictions. -/
theorem restrictCoefficients_injective : Function.Injective (U.restrictCoefficients ρ) := by
  intro f g h
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  obtain ⟨i,hi⟩ := mem_iUnion.mp (U.covers x.property.2)
  exact congrArg (fun c : coefficientSections ρ (U.domain i) =>
    c.val ⟨x.val,x.property.1,hi⟩) (congrFun h i)

/-- Restricting the actual glued coefficient family recovers its original values. -/
theorem restrict_extendCoefficients (w : ∀ i, coefficientSections ρ (U.domain i)) :
    U.restrictCoefficients ρ (U.extendCoefficients ρ w) = w := by
  funext i
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact U.extendCoefficients_value ρ w i ⟨x.val,x.property.1,U.subset i x.property.2⟩ x.property.2

/-- The actual coefficient section space is the genuine product of its disjoint component spaces. -/
def coefficientEquiv : coefficientSections ρ V ≃ₗ[ℝ] (∀ i, coefficientSections ρ (U.domain i)) :=
  LinearEquiv.ofBijective (U.restrictCoefficients ρ)
    ⟨U.restrictCoefficients_injective ρ,fun w => ⟨U.extendCoefficients ρ w,U.restrict_extendCoefficients ρ w⟩⟩

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
