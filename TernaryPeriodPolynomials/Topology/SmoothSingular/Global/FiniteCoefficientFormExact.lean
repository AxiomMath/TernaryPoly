module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormExact

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- All vertically augmented smooth columns in the actual finite-support common coefficient
span are exact, with support control supplied by literal-zero-preserving local primitives. -/
theorem finiteCoefficientFormTotalAugmentation_exactRows :
    (finiteCoefficientFormTotalAugmentation ρ C).ExactRows where
  injective q := by
    intro w z h
    apply Subtype.ext
    funext t
    apply coefficientForm_injective ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) t)
    exact congrFun (congrArg Subtype.val h) t
  augmentation_exact q w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteFormSubmodules ρ C).vertical_eq q 0)).symm.trans hw)
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) q 0 w.val = 0 at hd
    have hde := congrArg (fun f : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) 0 (q+1) →ₗ[ℝ]
      FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) 1 (q+1) => f w.val)
      (formCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) q 0)
    have ht (t : Fin (q+1) → C.Index) : differential ρ (cechDomain_isOpen
      (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) t) 0 (w.val t) = 0 :=
      congrFun (hde.symm.trans hd) t
    obtain ⟨z,hzf,hz⟩ := finiteFamily_primitive _
      (fun t => coefficientFormMap ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) t)) w.val w.property (fun t => by
          let u := closedFormCoefficient ρ _ (w.val t) (ht t)
          have hu := coefficientForm_closedFormCoefficient ρ _ (w.val t) (ht t)
          refine ⟨u,hu,fun hw0 => ?_⟩
          apply coefficientForm_injective ρ _
          exact (hu.trans hw0).trans (map_zero (coefficientFormMap ρ
            (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
              (fun i => (C.sheet i).quotientDomain_isOpen) t))).symm)
    exact ⟨⟨z,hzf⟩,Subtype.ext (funext hz)⟩
  horizontal_exact p q w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteFormSubmodules ρ C).vertical_eq q (p+1))).symm.trans hw)
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) q (p+1) w.val = 0 at hd
    have hde := congrArg (fun f : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+1) (q+1) →ₗ[ℝ]
      FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+2) (q+1) => f w.val)
      (formCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) q (p+1))
    obtain ⟨z,hzf,hz⟩ := finiteFormCech_column_exact ρ C p q w.val w.property
      (fun t => congrFun (hde.symm.trans hd) t)
    refine ⟨⟨z,hzf⟩,?_⟩
    apply (congrArg (fun f => f ⟨z,hzf⟩) ((finiteFormSubmodules ρ C).vertical_eq q p)).trans
    apply Subtype.ext
    have hv := congrArg (fun f : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) p (q+1) →ₗ[ℝ]
      FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) (p+1) (q+1) => f z)
      (formCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) q p)
    exact hv.trans (funext hz)

end TernaryPoly.SmoothSingularGlobal
