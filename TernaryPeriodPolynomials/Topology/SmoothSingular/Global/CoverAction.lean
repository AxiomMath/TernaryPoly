module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Cochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set
open SymmetricSpaceCovering SymmetricSpaceCharts SmoothCoveringDeRham

/-- The genuine lifted coordinate space over a quotient subset. -/
abbrev CoverOpen (U : Set OrbitSpace) := liftedDomain U

/-- Actual principal-six deck action on each invariant lifted domain. -/
instance coverOpenMulAction (U : Set OrbitSpace) : MulAction DeckGroup (CoverOpen U) where
  smul g x := ⟨deckMap g x, deckMap_liftedDomain g U x.property⟩
  one_smul x := Subtype.ext (deckMap_one x.property.1)
  mul_smul g h x := Subtype.ext (deckMap_mul g h x.property.1)

/-- The actual deck action is continuous on the lifted domain. -/
instance coverOpenContinuousConstSMul (U : Set OrbitSpace) :
    ContinuousConstSMul DeckGroup (CoverOpen U) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact (deckMap_smooth g).continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property.1)

/-- Genuine continuous inclusion between the actual lifted domains. -/
def coverInclusion {U V : Set OrbitSpace} (hVU : V ⊆ U) :
    TopCat.of (CoverOpen V) ⟶ TopCat.of (CoverOpen U) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, liftedDomain_mono hVU x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Lifted-domain inclusion is equivariant for the actual deck action. -/
theorem coverInclusion_equivariant {U V : Set OrbitSpace} (hVU : V ⊆ U)
    (g : DeckGroup) (x : CoverOpen V) : coverInclusion hVU (g • x) = g • coverInclusion hVU x := rfl

/-- The actual real equivariant singular Hom complex over a quotient subset. -/
abbrev coveringCochains {F : Type} [AddCommGroup F] [Module ℝ F]
    (ρ : Representation ℝ DeckGroup F) (U : Set OrbitSpace) : CochainComplex (ModuleCat ℝ) ℕ :=
  cochains DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ)

end TernaryPoly.SmoothSingularGlobal
