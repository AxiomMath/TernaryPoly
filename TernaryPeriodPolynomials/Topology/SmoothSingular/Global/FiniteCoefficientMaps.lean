module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientCech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSingularBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RestrictedVerticalAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

section Forms
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- The actual coefficient-to-form augmentation preserves finite tuple support. -/
theorem coefficientForm_finiteSupport (n : ℕ)
    (w : (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).X n)
    (hw : w ∈ (finiteCoefficientSubmodules ρ C).term n) :
    (coefficientFormTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)).augment n w ∈ (finiteFormSubmodules ρ C).term n 0 :=
  finiteFamily_map _ (fun t => coefficientFormMap ρ (cechDomain_isOpen
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) t)) hw

/-- The actual finite-support common coefficients augment the actual supported smooth bicomplex. -/
def finiteCoefficientFormTotalAugmentation : TotalAugmentation (finiteCoefficientCechComplex ρ C)
    (finiteFormBicomplex ρ C).flip :=
  restrictedVerticalAugmentation (finiteFormSubmodules ρ C) (finiteCoefficientSubmodules ρ C)
    (coefficientFormTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) (coefficientForm_finiteSupport ρ C)

end Forms
section Singular
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- The actual coefficient-to-singular augmentation preserves finite tuple support. -/
theorem coefficientSingular_finiteSupport (n : ℕ)
    (w : (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).X n)
    (hw : w ∈ (finiteCoefficientSubmodules ρ C).term n) :
    (coefficientSingularTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)).augment n w ∈
      (finiteSingularSubmodules ρ C).term n 0 :=
  finiteFamily_map _ (fun t => coefficientSingularMap ρ (cechDomain
    (fun i => (C.sheet i).quotientDomain) t)) hw

/-- The same actual finite-support common coefficients augment the actual supported singular bicomplex. -/
def finiteCoefficientSingularTotalAugmentation : TotalAugmentation (finiteCoefficientCechComplex ρ C)
    (finiteSingularBicomplex ρ C).flip :=
  restrictedVerticalAugmentation (finiteSingularSubmodules ρ C) (finiteCoefficientSubmodules ρ C)
    (coefficientSingularTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain))
      (coefficientSingular_finiteSupport ρ C)

end Singular
end TernaryPoly.SmoothSingularGlobal
