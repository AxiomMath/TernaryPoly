module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceBoundaryMV SymmetricSpaceBoundaryFaceAugmentation
open scoped MonoidAlgebra

theorem vertexSplit_augmentation (c : OrdinaryIncidenceChains.VertexChains) :
    labelSumLinear Line (vertexSplit c).1+labelSumLinear Plane (vertexSplit c).2=
      OrdinaryIncidencePaths.augmentation c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Prod.fst_zero,Prod.snd_zero,add_zero]
  | add c d hc hd =>
    simp only [map_add,Prod.fst_add,Prod.snd_add]
    calc
      _ = (labelSumLinear Line (vertexSplit c).1+labelSumLinear Plane (vertexSplit c).2)+
        (labelSumLinear Line (vertexSplit d).1+labelSumLinear Plane (vertexSplit d).2) := by abel
      _ = _ := congrArg₂ (·+·) hc hd
  | single v r =>
    cases v with
    | inl L => simp only [vertexSplit_single_line,labelSumLinear_single,OrdinaryIncidencePaths.augmentation_single,
        map_zero,add_zero]
    | inr P => simp only [vertexSplit_single_plane,labelSumLinear_single,OrdinaryIncidencePaths.augmentation_single,
        map_zero,zero_add]

theorem vertexAugmentation_apply (c : (lineLabels ⊞ planeLabels : Rep ℚ principalSix)) :
    vertexAugmentation c=labelSumLinear Line ((biprod.fst : lineLabels ⊞ planeLabels ⟶ lineLabels) c)+
      labelSumLinear Plane ((biprod.snd : lineLabels ⊞ planeLabels ⟶ planeLabels) c) :=
  congrArg (fun f : lineLabels ⊞ planeLabels ⟶ Rep.trivial ℚ principalSix ℚ => f c) biprod.desc_eq

/-- The actual permutation-module augmentation is exactly ordinary vertex coefficient sum. -/
theorem scalarVertexIso_augmentation (c : (lineLabels ⊞ planeLabels : Rep ℚ principalSix)) :
    vertexAugmentation c=OrdinaryIncidencePaths.augmentation (scalarVertexIso.hom c) := by
  have h := vertexSplit_augmentation (scalarVertexIso.hom c)
  rw [scalarVertexIso_split,scalarProductIso_fst_apply,scalarProductIso_snd_apply] at h
  exact (vertexAugmentation_apply c).trans h

/-- Actual finite graph paths fill every zero-total vertex chain, so the signed incidence sequence is exact. -/
theorem incidence_exact : (ShortComplex.mk incidence vertexAugmentation incidence_vertexAugmentation).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ forgetRep).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change vertexAugmentation x=0 at hx
  have hv : OrdinaryIncidencePaths.augmentation (scalarVertexIso.hom x)=0 :=
    (scalarVertexIso_augmentation x).symm.trans hx
  obtain ⟨c,hc⟩ := OrdinaryIncidencePaths.zero_augmentation_filling OrdinaryIncidence.incidence
    OrdinaryIncidence.connected.preconnected (Classical.choice OrdinaryIncidence.connected.nonempty)
      (scalarVertexIso.hom x) hv
  refine ⟨edgeCoefficients.symm (-c),?_⟩
  apply (ConcreteCategory.bijective_of_isIso scalarVertexIso.hom).injective
  change scalarVertexIso.hom (incidence (edgeCoefficients.symm (-c)))=scalarVertexIso.hom x
  rw [scalarIncidence_boundary,edgeCoefficients.apply_symm_apply,map_neg,neg_neg]
  exact hc

instance labelSum_epi {ι : Type} [MulAction principalSix ι] [Nonempty ι] : Epi (labelSum (ι := ι)) :=
  (Rep.epi_iff_surjective _).mpr (fun r => ⟨MonoidAlgebra.single (Classical.choice (inferInstance : Nonempty ι)) r,
    labelSum_single _ r⟩)

instance vertexAugmentation_epi : Epi vertexAugmentation := by
  have : Nonempty Line := ⟨⟨ModThreeGoodAction.firstLine,ModThreeGoodAction.firstLine_finrank,trivial⟩⟩
  exact biprod.epi_desc_of_epi_left (labelSum (ι := Line)) (labelSum (ι := Plane))

/-- Connectedness identifies the actual signed incidence cokernel with the trivial rational representation. -/
def incidenceCokernelIso : cokernel incidence ≅ Rep.trivial ℚ principalSix ℚ :=
  (colimit.isColimit (parallelPair incidence 0)).coconePointUniqueUpToIso incidence_exact.gIsCokernel

theorem incidenceCokernelIso_augmentation : cokernel.π incidence ≫ incidenceCokernelIso.hom=vertexAugmentation :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (parallelPair incidence 0)) incidence_exact.gIsCokernel WalkingParallelPair.one

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
