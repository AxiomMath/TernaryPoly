module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallCochains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Cech

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open SphereOddDegree

/-- Freeness of the actual principal-six action is preserved in the genuine lifted coordinate domains. -/
instance coverOpenFree (V : Set OrbitSpace) : IsCancelSMul DeckGroup (CoverOpen V) where
  right_cancel' g h x he := by
    have he' := congrArg (fun y : CoverOpen V => coordinateChart.symm y.val) he
    change coordinateChart.symm (deckMap g x.val) = coordinateChart.symm (deckMap h x.val) at he'
    rw [deckMap_inverseChart g x.property.1, deckMap_inverseChart h x.property.1] at he'
    exact IsCancelSMul.right_cancel g h (coordinateChart.symm x.val) he'

/-- The genuine quotient projection from a lifted domain, retaining its actual coordinates. -/
def coverProjection (V : Set OrbitSpace) : TopCat.of (CoverOpen V) ⟶ TopCat.of OrbitSpace :=
  TopCat.ofHom ⟨fun x => coordinateProjection x.val,
    coordinateProjection_continuousOn.comp_continuous continuous_subtype_val (fun x => x.property.1)⟩

/-- The genuine lifted projection is constant on the actual deck orbits. -/
theorem coverProjection_deck (V : Set OrbitSpace) (g : DeckGroup) (x : CoverOpen V) :
    coverProjection V (g • x) = coverProjection V x := coordinateProjection_deck g x.property.1

/-- Every quotient open cover pulls back to a genuine invariant cover of the actual lifted domain. -/
def liftedOpenCover {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) : OpenCoverData (TopCat.of (CoverOpen V)) where
  sets := Set.range (fun i => coverProjection V ⁻¹' U i)
  isOpen_mem := by
    rintro _ ⟨i, rfl⟩
    exact (hU i).preimage (coverProjection V).hom.continuous
  covers := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.property.2)
    exact ⟨coverProjection V ⁻¹' U i, ⟨i, rfl⟩, hi⟩

/-- Each actual pulled-back cover member is individually invariant under the genuine deck action. -/
theorem liftedOpenCover_invariant {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) :
    InvariantCover DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover) := by
  rintro _ ⟨i, rfl⟩ g x hx
  change coverProjection V (g • x) ∈ U i
  rw [coverProjection_deck]
  exact hx

/-- Actual cover-small equivariant chains on the genuine lifted quotient domain. -/
def coveringSmallChains {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) : ChainComplex (Rep ℝ DeckGroup) ℕ :=
  smallComplex DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
    (liftedOpenCover_invariant U hU V hcover)

/-- The actual cover-small chain inclusion is an equivariant homotopy equivalence. -/
def coveringSmallHomotopyEquiv {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) :
    _root_.HomotopyEquiv (coveringSmallChains U hU V hcover)
      (equivariantChains DeckGroup (TopCat.of (CoverOpen V))) :=
  smallHomotopyEquiv DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
    (liftedOpenCover_invariant U hU V hcover)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual real equivariant singular Hom cochains on the genuine cover-small chain complex. -/
abbrev coveringSmallCochains {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) :=
  homCochains (coveringSmallChains U hU V hcover) (Rep.of ρ)

/-- The literal restriction of genuine singular Hom cochains to actual quotient-cover-small chains. -/
def coveringSmallRestriction {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
    (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) :
    coveringCochains ρ V ⟶ coveringSmallCochains ρ U hU V hcover :=
  smallRestriction DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
    (liftedOpenCover_invariant U hU V hcover) (Rep.of ρ)

/-- Genuine singular subdivision descent holds after actual equivariant Hom, by the proved
projective-chain homotopy equivalence, for every actual quotient open cover and real coefficient module. -/
theorem coveringSmallRestriction_quasiIso {ι : Type*} (U : ι → Set OrbitSpace)
    (hU : ∀ i, IsOpen (U i)) (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i) :
    QuasiIso (coveringSmallRestriction ρ U hU V hcover) :=
  smallRestriction_quasiIso DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
    (liftedOpenCover_invariant U hU V hcover) (Rep.of ρ)

end TernaryPoly.SmoothSingularGlobal
