module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LinearPrimitives

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- All vertically augmented singular columns in the actual finite-support common coefficient
span are exact, using genuine overlap primitives which preserve literal zero. -/
theorem finiteCoefficientSingularTotalAugmentation_exactRows :
    (finiteCoefficientSingularTotalAugmentation ρ C).ExactRows where
  injective q := by
    intro w z h
    apply Subtype.ext
    funext t
    apply coefficientSingularMap_injective ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)
    exact congrFun (congrArg Subtype.val h) t
  augmentation_exact q w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteSingularSubmodules ρ C).vertical_eq q 0)).symm.trans hw)
    change vertical (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) q 0 w.val = 0 at hd
    have hde := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) 0 (q+1) →ₗ[ℝ]
      SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) 1 (q+1) => f w.val)
      (singularCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain) q 0)
    obtain ⟨z,hzf,hz⟩ := finiteFamily_primitive _
      (fun t => coefficientSingularMap ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t))
      w.val w.property (fun t => cechOverlap_singular_zero_zero ρ (C.sheet ∘ t)
        (w.val t) (congrFun (hde.symm.trans hd) t))
    exact ⟨⟨z,hzf⟩,Subtype.ext (funext hz)⟩
  horizontal_exact p q w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteSingularSubmodules ρ C).vertical_eq q (p+1))).symm.trans hw)
    change vertical (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) q (p+1) w.val = 0 at hd
    have hde := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+1) (q+1) →ₗ[ℝ]
      (SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+2) (q+1)) => f w.val)
      (singularCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain) q (p+1))
    obtain ⟨z,hzf,hz⟩ := finiteFamily_primitive _
      (fun t => ((coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).d p (p+1)).hom)
      w.val w.property (fun t => cechOverlap_singular_primitive_zero ρ (C.sheet ∘ t) p
        (w.val t) (congrFun (hde.symm.trans hd) t))
    refine ⟨⟨z,hzf⟩,?_⟩
    apply (congrArg (fun f => f ⟨z,hzf⟩) ((finiteSingularSubmodules ρ C).vertical_eq q p)).trans
    apply Subtype.ext
    have hv := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) p (q+1) →ₗ[ℝ]
      SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+1) (q+1) => f z)
      (singularCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain) q p)
    exact hv.trans (funext hz)

end TernaryPoly.SmoothSingularGlobal
