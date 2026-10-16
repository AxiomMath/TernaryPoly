module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSmallComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SymmetricSpaceCovering

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- The actual finite-support singular Čech rows are exact, augmented by the auxiliary
actual small-cochain complex with finite literal restriction support. -/
theorem finiteSmallTotalAugmentation_exactRows : (finiteSmallTotalAugmentation ρ C).ExactRows where
  injective n := by
    intro w z h
    apply Subtype.ext
    apply (singularCechTotalAugmentation_exactRows ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).injective n
    exact congrArg Subtype.val h
  augmentation_exact n w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteSingularSubmodules ρ C).horizontal_eq 0 n)).symm.trans hw)
    change horizontal (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) 0 n w.val = 0 at hd
    obtain ⟨z,hz⟩ := (singularCechTotalAugmentation_exactRows ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).augmentation_exact n w.val hd
    have hzf : z ∈ (finiteRestrictionSmallSubmodules ρ C).term n := by
      change (familySupport (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n z)).Finite
      exact (congrArg (fun v : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n 1 =>
        (familySupport v).Finite) hz).mpr w.property
    exact ⟨⟨z,hzf⟩,Subtype.ext hz⟩
  horizontal_exact := finiteSingular_horizontal_exact ρ C

/-- The auxiliary actual finite-restriction small-singular cohomology is computed by the
actual finite-support singular Čech total. Its compact-model identification remains separate. -/
def finiteSmallCechTotalIso : (finiteRestrictionSmallComplex ρ C).homology 2 ≅
    (totalWindow (finiteSingularBicomplex ρ C)).homology :=
  (finiteRestrictionSmallComplex ρ C).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (finiteSmallTotalAugmentation ρ C).totalAugmentationHomologyIso
      (finiteSmallTotalAugmentation_exactRows ρ C)

end TernaryPoly.SmoothSingularGlobal
