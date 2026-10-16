module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.Vectors
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable def boundedRealization (data : CuspidalRepresentation) :
    data.smooth →ₗ[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ where
  toFun vector := ⟨data.realize vector, memℓp_infty (by
    obtain ⟨bound, boundProperty⟩ := data.bounded vector
    exact ⟨bound, by rintro _ ⟨matrix, rfl⟩; exact boundProperty matrix⟩)⟩
  map_add' first second := by
    apply Subtype.ext
    exact map_add data.realize first second
  map_smul' scalar vector := by
    apply Subtype.ext
    exact map_smul data.realize scalar vector

noncomputable def cuspSupNorm {data : CuspidalRepresentation} (vector : data.smooth) : ℝ :=
  ‖boundedRealization data vector‖

theorem cuspSupNorm_nonneg {data : CuspidalRepresentation} (vector : data.smooth) :
    0 ≤ cuspSupNorm vector := norm_nonneg _

theorem realize_le_cuspSupNorm {data : CuspidalRepresentation} (vector : data.smooth)
    (matrix : BinaryAdelicGL) : ‖data.realize vector matrix‖ ≤ cuspSupNorm vector :=
  lp.norm_apply_le_norm (by simp) (boundedRealization data vector) matrix

theorem cuspSupNorm_le {data : CuspidalRepresentation} (vector : data.smooth)
    (bound : ℝ) (boundProperty : ∀ matrix, ‖data.realize vector matrix‖ ≤ bound) :
    cuspSupNorm vector ≤ bound :=
  lp.norm_le_of_forall_le' bound boundProperty

theorem cuspSupNorm_eq_zero {data : CuspidalRepresentation} (vector : data.smooth) :
    cuspSupNorm vector = 0 ↔ vector = 0 := by
  constructor
  · intro zeroNorm
    apply data.injective
    funext matrix
    rw [map_zero, Pi.zero_apply]
    exact norm_eq_zero.mp (le_antisymm
      ((realize_le_cuspSupNorm vector matrix).trans zeroNorm.le) (norm_nonneg _))
  · rintro rfl
    exact norm_eq_zero.mpr (map_zero (boundedRealization data))

theorem cuspSupNorm_smul {data : CuspidalRepresentation} (scalar : ℂ)
    (vector : data.smooth) : cuspSupNorm (scalar • vector) = ‖scalar‖ * cuspSupNorm vector := by
  simp only [cuspSupNorm, map_smul, norm_smul]

theorem cuspSupNorm_add_le {data : CuspidalRepresentation} (first second : data.smooth) :
    cuspSupNorm (first + second) ≤ cuspSupNorm first + cuspSupNorm second := by
  simp only [cuspSupNorm, map_add]
  exact norm_add_le _ _

theorem cuspSupNorm_translate {data : CuspidalRepresentation} (matrix : BinaryAdelicGL)
    (vector : data.smooth) :
    cuspSupNorm (⟨data.π matrix vector.val,
      data.smooth_stable matrix vector.val vector.property⟩ : data.smooth) =
        cuspSupNorm vector := by
  apply le_antisymm
  · apply cuspSupNorm_le
    intro point
    rw [data.equivariant]
    exact realize_le_cuspSupNorm vector _
  · apply cuspSupNorm_le
    intro point
    have bound := realize_le_cuspSupNorm
      (⟨data.π matrix vector.val, data.smooth_stable matrix vector.val vector.property⟩ : data.smooth)
      (point * matrix⁻¹)
    rw [data.equivariant, inv_mul_cancel_right] at bound
    exact bound

theorem finiteDimensional_cuspSupNorm_bound {data : CuspidalRepresentation}
    (subspace : Submodule ℂ data.smooth) [FiniteDimensional ℂ subspace] :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ vector : data.smooth, vector ∈ subspace →
      cuspSupNorm vector ≤ bound * ‖vector.val‖ := by
  let realization : subspace →L[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
    ⟨(boundedRealization data).comp subspace.subtype,
      ((boundedRealization data).comp subspace.subtype).continuous_of_finiteDimensional⟩
  exact ⟨‖realization‖, realization.opNorm_nonneg, fun vector membership =>
    realization.le_opNorm ⟨vector, membership⟩⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
