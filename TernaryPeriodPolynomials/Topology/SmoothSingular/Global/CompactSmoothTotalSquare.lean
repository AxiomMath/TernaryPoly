module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormTotalExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalHomologyNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- Literal support forgetting from the supported smooth Čech total window. -/
def finiteFormTotalForget : totalWindow (finiteFormBicomplex ρ C) ⟶
    totalWindow (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) :=
  totalWindowMap (finiteFormSubmodules ρ C).inclusion

/-- The actual compact and ordinary smooth augmentations commute with literal support
forgetting at the total-chain level. -/
theorem finiteFormTotalAugmentation_forget :
    (finiteFormTotalAugmentation ρ C).totalAugmentationMap ≫ finiteFormTotalForget ρ C =
      (HomologicalComplex.shortComplexFunctor' (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map
        (compactInclusion ρ isOpen_univ) ≫
      (formCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen)).totalAugmentationMap :=
  totalAugmentationMap_naturality (finiteFormSubmodules ρ C).inclusion
    (finiteFormTotalAugmentation ρ C)
    (formCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen)) (compactInclusion ρ isOpen_univ)
      (finiteFormColumnAugmentation_forget ρ C)

/-- The compact smooth descent isomorphism respects the true compact-support inclusion
and the actual finite-support total-window inclusion. -/
theorem compactFormsCechTotalIso_forget :
    (compactFormsCechTotalIso ρ C).hom ≫ ShortComplex.homologyMap (finiteFormTotalForget ρ C) =
      HomologicalComplex.homologyMap (compactInclusion ρ isOpen_univ) 2 ≫
        (globalFormsCechTotalIso ρ (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen) (by rw [C.covers])).hom := by
  have hh := congrArg (fun f => (ShortComplex.homologyMap f :
    ((globalCompactComplex ρ).sc' 1 2 3).homology ⟶
      (totalWindow (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen))).homology))
      (finiteFormTotalAugmentation_forget ρ C)
  rw [ShortComplex.homologyMap_comp,ShortComplex.homologyMap_comp] at hh
  let iA := ((globalCompactComplex ρ).homologyIsoSc' 1 2 3 (by simp) (by simp)).hom
  let iB := ((globalComplex ρ).homologyIsoSc' 1 2 3 (by simp) (by simp)).hom
  let hA := ShortComplex.homologyMap (finiteFormTotalAugmentation ρ C).totalAugmentationMap
  let hB := ShortComplex.homologyMap (formCechTotalAugmentation ρ
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)).totalAugmentationMap
  let sg := ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
    (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map (compactInclusion ρ isOpen_univ))
  let hg := HomologicalComplex.homologyMap (compactInclusion ρ isOpen_univ) 2
  calc
    _ = iA ≫ (hA ≫ ShortComplex.homologyMap (finiteFormTotalForget ρ C)) := Category.assoc _ _ _
    _ = iA ≫ (sg ≫ hB) := congrArg (fun f => iA ≫ f) hh
    _ = (iA ≫ sg) ≫ hB := (Category.assoc _ _ _).symm
    _ = (hg ≫ iB) ≫ hB := congrArg (fun f => f ≫ hB)
      (homologyIsoSc_degreeTwo_naturality (compactInclusion ρ isOpen_univ))
    _ = _ := Category.assoc _ _ _

end TernaryPoly.SmoothSingularGlobal
