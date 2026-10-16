module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSingularHomotopy
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SubBicomplex

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SymmetricSpaceCovering

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- Literal finite-tuple-support submodules of the genuine singular Čech bicomplex. -/
def finiteSingularSubmodules : BicomplexSubmodules
    (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) where
  term p q := finiteFamilySubmodule (fun t : Fin (p+1) → C.Index =>
    (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).X q)
  horizontal_mem p q w hw := singularCechHorizontal_finiteSupport ρ C q p w hw
  vertical_mem p q w hw := by
    have he := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) q (p+1) →ₗ[ℝ]
      SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (q+1) (p+1) => f w)
        (singularCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain) p q)
    exact (congrArg (fun z : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (q+1) (p+1) =>
      (familySupport z).Finite) he).mpr (singularCechVertical_finiteSupport ρ C q (p+1) w hw)

/-- The actual finite-tuple-support singular Čech bicomplex. -/
def finiteSingularBicomplex : RealBicomplex := (finiteSingularSubmodules ρ C).toBicomplex

/-- Every positive horizontal row of this actual finite-support singular bicomplex is exact. -/
theorem finiteSingular_horizontal_exact (p q : ℕ)
    (w : ((finiteSingularBicomplex ρ C).X (p+1)).X q)
    (hw : horizontal (finiteSingularBicomplex ρ C) (p+1) q w = 0) :
    ∃ z : ((finiteSingularBicomplex ρ C).X p).X q,
      horizontal (finiteSingularBicomplex ρ C) p q z = w := by
  have hd := congrArg Subtype.val
    ((congrArg (fun f => f w) ((finiteSingularSubmodules ρ C).horizontal_eq (p+1) q)).symm.trans hw)
  change horizontal (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) (p+1) q w.val = 0 at hd
  let z := singularCechH ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) (by rw [C.covers]) q p w.val
  have hzf : (familySupport z).Finite := singularCechH_finiteSupport ρ _ _ _ q p w.val w.property
  refine ⟨⟨z,hzf⟩,?_⟩
  apply (congrArg (fun f => f ⟨z,hzf⟩) ((finiteSingularSubmodules ρ C).horizontal_eq p q)).trans
  apply Subtype.ext
  exact singularCechH_primitive ρ _ _ _ q p w.val hd

end TernaryPoly.SmoothSingularGlobal
