module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyZero

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceBoundaryMV SymmetricSpaceBoundaryFaceAugmentation
open scoped MonoidAlgebra

/-- The actual inclusion of the level-six group into the fixed level-three arithmetic group K. -/
def principalToK : principalSix →* GoodBuilding.K := Subgroup.inclusion principalSix_le_K

/-- The target is literally OrdinaryIncidenceChains.Cycles with its restricted arithmetic action. -/
abbrev ordinaryCyclesRep : Rep ℚ principalSix :=
  Rep.of (OrdinaryIncidenceChains.complex.cyclesAction.comp principalToK)

/-- The actual geometric flag action is the ordinary incidence-edge action of the same matrix. -/
theorem flag_action_ordinary (g : principalSix) (F : Flag) :
    (g • F : Flag)=OrdinaryIncidenceChains.edgeAction (principalToK g) F := rfl

@[simp] theorem edgeCoefficients_single (F : Flag) (r : ℚ) :
    edgeCoefficients (MonoidAlgebra.single F r)=Finsupp.single F r := rfl

theorem edgeCoefficients_action (g : principalSix) (c : ℚ[Flag]) :
    edgeCoefficients (flagLabels.ρ g c)=
      OrdinaryIncidenceChains.edgeRepresentation (principalToK g) (edgeCoefficients c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single F r =>
    change edgeCoefficients (Representation.ofMulAction ℚ principalSix Flag g (MonoidAlgebra.single F r))=_
    rw [Representation.ofMulAction_single,edgeCoefficients_single,edgeCoefficients_single]
    exact (congrArg (fun e : OrdinaryIncidenceChains.Edge => Finsupp.single e r)
      (flag_action_ordinary g F)).trans
        (OrdinaryIncidenceChains.edgeRepresentation_single (principalToK g) F r).symm

/-- Incidence and ordinary graph boundary have the same literal kernel; their vertex signs are opposite. -/
theorem incidence_eq_zero_iff (c : ℚ[Flag]) : incidence c=0 ↔
    OrdinaryIncidenceChains.boundary (edgeCoefficients c)=0 := by
  constructor
  · intro h
    have he := scalarIncidence_boundary c
    rw [h,map_zero] at he
    exact neg_eq_zero.mp he.symm
  · intro h
    apply (ConcreteCategory.bijective_of_isIso scalarVertexIso.hom).injective
    rw [scalarIncidence_boundary,h,map_zero,neg_zero]

def ordinaryCycleInclusionLinear : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ℚ[Flag] :=
  edgeCoefficients.symm.toLinearMap.comp OrdinaryIncidenceChains.complex.Cycles.subtype

theorem ordinaryCycleInclusion_equivariant (g : principalSix) (c : OrdinaryIncidenceChains.Cycles) :
    ordinaryCycleInclusionLinear (ordinaryCyclesRep.ρ g c)=flagLabels.ρ g (ordinaryCycleInclusionLinear c) := by
  apply edgeCoefficients.injective
  change edgeCoefficients (edgeCoefficients.symm
    (OrdinaryIncidenceChains.complex.cyclesAction (principalToK g) c).val)=
      edgeCoefficients (flagLabels.ρ g (edgeCoefficients.symm c.val))
  rw [edgeCoefficients.apply_symm_apply,edgeCoefficients_action,edgeCoefficients.apply_symm_apply]
  rfl

/-- Literal edge-coefficient inclusion of ordinary cycles into the flag permutation module. -/
def ordinaryCycleInclusion : ordinaryCyclesRep ⟶ flagLabels :=
  Rep.ofHom ⟨ordinaryCycleInclusionLinear,fun g => LinearMap.ext (ordinaryCycleInclusion_equivariant g)⟩

theorem ordinaryCycleInclusion_incidence : ordinaryCycleInclusion ≫ incidence=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  change incidence (edgeCoefficients.symm c.val)=0
  apply (incidence_eq_zero_iff _).mpr
  rw [edgeCoefficients.apply_symm_apply]
  exact c.property

instance ordinaryCycleInclusion_mono : Mono ordinaryCycleInclusion :=
  (Rep.mono_iff_injective _).mpr (fun _ _ h => Subtype.ext (edgeCoefficients.symm.injective h))

/-- Ordinary cycles satisfy the kernel universal property through their actual representation. -/
theorem ordinaryCycles_exact :
    (ShortComplex.mk ordinaryCycleInclusion incidence ordinaryCycleInclusion_incidence).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ forgetRep).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c hc
  change incidence c=0 at hc
  refine ⟨⟨edgeCoefficients c,(incidence_eq_zero_iff c).mp hc⟩,?_⟩
  exact edgeCoefficients.symm_apply_apply c

/-- The categorical incidence kernel is the literal ordinary cycle representation, with no edge sign change. -/
def kernelOrdinaryCyclesIso : kernel incidence ≅ ordinaryCyclesRep :=
  (limit.isLimit (parallelPair incidence 0)).conePointUniqueUpToIso ordinaryCycles_exact.fIsKernel

theorem kernelOrdinaryCyclesIso_inclusion : kernelOrdinaryCyclesIso.hom ≫ ordinaryCycleInclusion=kernel.ι incidence :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (parallelPair incidence 0))
    ordinaryCycles_exact.fIsKernel WalkingParallelPair.zero

/-- Actual boundary H1 is literally the ordinary rational incidence-cycle representation restricted to level six. -/
def boundaryH1OrdinaryCyclesIso : boundaryChains.homology 1 ≅ ordinaryCyclesRep :=
  boundaryH1Iso ≪≫ kernelOrdinaryCyclesIso

theorem boundaryH1OrdinaryCyclesIso_edge : boundaryH1OrdinaryCyclesIso.hom ≫ ordinaryCycleInclusion=boundaryEdgeMap :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m => boundaryH1Iso.hom ≫ m) kernelOrdinaryCyclesIso_inclusion).trans boundaryH1Iso_edge)

/-- The cycle coefficients are exactly those of the genuine MV edge map. -/
theorem boundaryH1OrdinaryCyclesIso_coefficients (c : boundaryChains.homology 1) :
    (boundaryH1OrdinaryCyclesIso.hom c).val=edgeCoefficients (boundaryEdgeMap c) := by
  have h := congrArg (fun f => f c) boundaryH1OrdinaryCyclesIso_edge
  exact (edgeCoefficients.apply_symm_apply _).symm.trans (congrArg edgeCoefficients h)

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
