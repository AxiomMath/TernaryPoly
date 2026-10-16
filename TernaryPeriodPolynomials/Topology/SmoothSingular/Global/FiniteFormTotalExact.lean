module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechTotalExact

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- All actual finite-support smooth Čech rows are exact, including the genuine compact
augmentation, with all support and descent hypotheses discharged. -/
theorem finiteFormTotalAugmentation_exactRows : (finiteFormTotalAugmentation ρ C).ExactRows where
  injective n := by
    intro w z h
    apply Subtype.ext
    apply (formCechTotalAugmentation_exactRows_of_cover ρ
      (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)
      (by rw [C.covers])).injective n
    exact congrArg Subtype.val h
  augmentation_exact n w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteFormSubmodules ρ C).horizontal_eq 0 n)).symm.trans hw)
    change horizontal (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) 0 n w.val = 0 at hd
    rw [formCechBicomplex_horizontal] at hd
    obtain ⟨z,hz⟩ := finiteFormCech_zero_exact ρ C n w.val w.property hd
    exact ⟨z,Subtype.ext hz⟩
  horizontal_exact p q w hw := by
    have hd := congrArg Subtype.val
      ((congrArg (fun f => f w) ((finiteFormSubmodules ρ C).horizontal_eq (p+1) q)).symm.trans hw)
    change horizontal (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) (p+1) q w.val = 0 at hd
    rw [formCechBicomplex_horizontal] at hd
    obtain ⟨z,hzf,hz⟩ := finiteFormCech_positive_exact ρ C q p w.val w.property hd
    refine ⟨⟨z,hzf⟩,?_⟩
    apply (congrArg (fun f => f ⟨z,hzf⟩) ((finiteFormSubmodules ρ C).horizontal_eq p q)).trans
    apply Subtype.ext
    change horizontal (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) p q z = w.val
    rw [formCechBicomplex_horizontal]
    exact hz

/-- Actual compact global degree-two de Rham cohomology is computed by the genuine
finite-support Čech–de Rham total window. -/
def compactFormsCechTotalIso : (globalCompactComplex ρ).homology 2 ≅
    (totalWindow (finiteFormBicomplex ρ C)).homology :=
  (globalCompactComplex ρ).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (finiteFormTotalAugmentation ρ C).totalAugmentationHomologyIso
      (finiteFormTotalAugmentation_exactRows ρ C)

end TernaryPoly.SmoothSingularGlobal
