module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteInjectiveFamilies
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSingularCech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientCechMaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subcomplex

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SymmetricSpaceCovering

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- The actual finite-support coefficient Čech differential is closed on its literal families.
This follows from the actual injective singular augmentation and its proved naturality. -/
theorem coefficientCech_d_finiteSupport (n : ℕ)
    (w : CoefficientCechTerms ρ (fun i => (C.sheet i).quotientDomain) (n+1))
    (hw : (familySupport w).Finite) :
    (familySupport ((coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).d n (n+1) w)).Finite := by
  have hF : (familySupport (coefficientCechToSingular ρ (fun i => (C.sheet i).quotientDomain) (n+1) w)).Finite :=
    finiteFamily_map _ (fun t => coefficientSingularMap ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)) hw
  have hD := singularCechHorizontal_finiteSupport ρ C 0 n _ hF
  have he := congrArg (fun f => f.hom w)
    ((coefficientSingularCechChain ρ (fun i => (C.sheet i).quotientDomain)).comm n (n+1))
  have hDF : (familySupport (coefficientCechToSingular ρ (fun i => (C.sheet i).quotientDomain) (n+2)
      ((coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).d n (n+1) w))).Finite :=
    (congrArg (fun z : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) 0 (n+2) =>
      (familySupport z).Finite) he).mp hD
  exact finiteFamily_of_injective_map
    (fun t => coefficientSingularMap ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t))
    (fun t => coefficientSingularMap_injective ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)) _ hDF

/-- The genuine finite-support common coefficient Čech subcomplex. -/
def finiteCoefficientSubmodules : CochainSubmodules
    (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)) where
  term n := finiteFamilySubmodule (fun t : Fin (n+1) → C.Index =>
    coefficientSections ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t))
  differential_mem n w hw := coefficientCech_d_finiteSupport ρ C n w hw

/-- The actual common coefficient complex for the supported comparison. -/
def finiteCoefficientCechComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  (finiteCoefficientSubmodules ρ C).toComplex

end TernaryPoly.SmoothSingularGlobal
