module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteLadderClosure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspFiniteRaisingPMap_mem_closure_range (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp level weight) :
    (cuspRaisingOperator cusp weight vector).val ∈ (cuspFiniteRaisingPMap cusp level weight).closure.toFun.range := by
  let source : (cuspFiniteRaisingPMap cusp level weight).domain := ⟨vector.val, member, vector.property⟩
  have graph_member := (cuspFiniteRaisingPMap cusp level weight).mem_graph source
  have closed_graph_member := LinearPMap.le_graph_of_le (LinearPMap.le_closure (cuspFiniteRaisingPMap cusp level weight)) graph_member
  exact LinearPMap.mem_range_iff.mpr ⟨vector.val, closed_graph_member⟩

theorem cuspFiniteRaising_decomposition (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight)
    (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2)) :
    ∃ (preimage : (cuspFiniteRaisingPMap cusp level weight).closure.domain) (remainder : cusp.H),
      preimage.val ∈ cuspHilbertWeightValues cusp level weight ∧
      remainder ∈ cuspHilbertWeightValues cusp level (weight + 2) ∧
      remainder ∈ (cuspFiniteRaisingPMap cusp level weight).closure.toFun.rangeᗮ ∧
      vector = ((cuspFiniteRaisingPMap cusp level weight).closure preimage : cusp.H) + remainder ∧
      ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
        inner ℂ remainder (cuspRaisingOperator cusp weight smooth).val = 0 := by
  let range := (cuspFiniteRaisingPMap cusp level weight).closure.toFun.range
  let : CompleteSpace range := (cuspFiniteRaisingPMap_closure_range_isClosed cusp spherical level weight positive).completeSpace_coe
  obtain ⟨image, image_mem, orthogonal⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := range) vector
  obtain ⟨preimage, image_eq⟩ := image_mem
  change ((cuspFiniteRaisingPMap cusp level weight).closure preimage : cusp.H) = image at image_eq
  have weights := cuspFiniteRaisingPMap_closure_weights cusp spherical level weight preimage
  have image_weight : image ∈ cuspHilbertWeightValues cusp level (weight + 2) := image_eq ▸ weights.2
  refine ⟨preimage, vector - image, weights.1, Submodule.sub_mem _ member image_weight, orthogonal, ?_, ?_⟩
  · rw [image_eq]
    abel
  · intro smooth smooth_mem
    exact (Submodule.mem_orthogonal' range (vector - image)).mp orthogonal _
      (cuspFiniteRaisingPMap_mem_closure_range cusp level weight smooth smooth_mem)

theorem cuspFiniteRaising_exists_weak_kernel_of_not_mem (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight)
    (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (outside : vector ∉ (cuspFiniteRaisingPMap cusp level weight).closure.toFun.range) :
    ∃ remainder : cusp.H, remainder ≠ 0 ∧ remainder ∈ cuspHilbertWeightValues cusp level (weight + 2) ∧
      ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
        inner ℂ remainder (cuspRaisingOperator cusp weight smooth).val = 0 := by
  obtain ⟨preimage, remainder, _, remainder_mem, _, decomposition, annihilates⟩ :=
    cuspFiniteRaising_decomposition cusp spherical level weight positive vector member
  refine ⟨remainder, ?_, remainder_mem, annihilates⟩
  intro zero
  rw [zero, add_zero] at decomposition
  apply outside
  exact ⟨preimage, decomposition.symm⟩

theorem cuspWeakLoweringKernel_lowering_zero (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp level (weight + 2))
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
      inner ℂ vector.val (cuspRaisingOperator cusp weight smooth).val = 0) :
    cuspLoweringOperator cusp (weight + 2) vector = 0 := by
  let lowered := cuspLoweringOperator cusp (weight + 2) vector
  have lowered_mem : lowered ∈ cuspFiniteWeightValues cusp level weight := by
    simpa only [add_sub_cancel_right] using cuspFiniteWeightValues_lowering cusp level (weight + 2) vector member
  have orthogonal : inner ℂ vector.val lowered.val = 0 := by
    apply inner_eq_zero_symm.mp
    exact cuspRotationWeight_inner_add_two cusp lowered.val vector.val weight lowered_mem.2 member.2
  have shift : cuspRaisingOperator cusp (weight + 2) lowered = cuspRaisingOperator cusp weight lowered + Complex.I • lowered := by
    simp only [cuspRaisingOperator, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Int.cast_add, Int.cast_ofNat]
    module
  have skew := cuspLoweringOperator_skew cusp (weight + 2) vector lowered
  rw [shift, Submodule.coe_add, Submodule.coe_smul, inner_add_right, inner_smul_right,
    annihilates lowered lowered_mem, orthogonal, mul_zero, add_zero, add_zero] at skew
  apply Subtype.ext
  exact inner_self_eq_zero.mp skew

end TernaryPeriodPolynomials.SphericalDetection.Helpers
