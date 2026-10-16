module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactSheets
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientCechMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OverlapPrimitives

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- Every vertically augmented smooth Čech column of the genuine convex-sheet cover is exact.
This supplies the actual exact rows after the bicomplex axes are exchanged. -/
theorem compactCoverCoefficientForm_exactRows :
    (coefficientFormTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)).ExactRows where
  injective q := by
    intro w z h
    funext t
    apply coefficientForm_injective ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) t)
    exact congrFun h t
  augmentation_exact q w hw := by
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) q 0 w = 0 at hw
    rw [formCechBicomplex_vertical] at hw
    have ht (t : Fin (q+1) → C.Index) : differential ρ
        (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) t) 0 (w t) = 0 :=
      congrFun hw t
    refine ⟨fun t => closedFormCoefficient ρ _ (w t) (ht t),?_⟩
    funext t
    exact coefficientForm_closedFormCoefficient ρ _ (w t) (ht t)
  horizontal_exact p q w hw := by
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) q (p+1) w = 0 at hw
    rw [formCechBicomplex_vertical] at hw
    have ht (t : Fin (q+1) → C.Index) : differential ρ
        (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) t) (p+1) (w t) = 0 :=
      congrFun hw t
    choose z hz using fun t => cechOverlap_form_primitive ρ (C.sheet ∘ t) p (w t) (ht t)
    refine ⟨z,?_⟩
    change vertical (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) q p z = w
    rw [formCechBicomplex_vertical]
    exact funext hz

omit [FiniteDimensional ℝ F] in
/-- Every vertically augmented singular Čech column of the genuine convex-sheet cover is exact,
with actual equivariant singular cochains and actual coefficient sections. -/
theorem compactCoverCoefficientSingular_exactRows :
    (coefficientSingularTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)).ExactRows where
  injective q := by
    intro w z h
    funext t
    apply coefficientSingularMap_injective ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)
    exact congrFun h t
  augmentation_exact q w hw := by
    change vertical (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) q 0 w = 0 at hw
    rw [singularCechBicomplex_vertical] at hw
    have ht (t : Fin (q+1) → C.Index) :
        (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).d 0 1 (w t) = 0 :=
      congrFun hw t
    choose z hz using fun t => cechOverlap_singular_zero ρ (C.sheet ∘ t) (w t) (ht t)
    exact ⟨z,funext hz⟩
  horizontal_exact p q w hw := by
    change vertical (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) q (p+1) w = 0 at hw
    rw [singularCechBicomplex_vertical] at hw
    have ht (t : Fin (q+1) → C.Index) :
        (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).d (p+1) (p+2) (w t) = 0 :=
      congrFun hw t
    choose z hz using fun t => cechOverlap_singular_primitive ρ (C.sheet ∘ t) p (w t) (ht t)
    refine ⟨z,?_⟩
    change vertical (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) q p z = w
    rw [singularCechBicomplex_vertical]
    exact funext hz

end TernaryPoly.SmoothSingularGlobal
