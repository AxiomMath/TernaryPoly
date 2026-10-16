module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicNormContinuity

instance adelicGL_locallyCompact {size : ℕ} :
    LocallyCompactSpace (GeneralLinearGroup (Fin size) Adeles) := by
  let : LocallyCompactSpace (Matrix (Fin size) (Fin size) Adeles) :=
    inferInstanceAs (LocallyCompactSpace (Fin size → Fin size → Adeles))
  infer_instance

def finiteUnit : Adelesˣ →* FiniteAdelesˣ :=
  Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom

theorem finiteUnit_continuous : Continuous finiteUnit :=
  Units.continuous_map continuous_snd

theorem integralUnits_isOpen :
    IsOpen (Set.range (Units.map integralEmbedding.toMonoidHom)) :=
  (TopologicalMatrices.units_map_isOpenEmbedding integralEmbedding.toMonoidHom
    integralEmbedding_isOpenEmbedding).isOpen_range

theorem norm_of_integral_finite (unit : Adelesˣ)
    (integral : finiteUnit unit ∈ Set.range (Units.map integralEmbedding.toMonoidHom)) :
    (adeleNorm unit : ℝ) = |unit.val.1| := by
  obtain ⟨source, equality⟩ := integral
  conv_lhs => rw [InducedHeight.unit_split unit source equality.symm, map_mul, NNReal.coe_mul,
    Norms.integralUnit_norm, NNReal.coe_one, mul_one, Norms.realUnit_norm]
  rfl

theorem norm_continuous : Continuous (fun unit : Adelesˣ => (adeleNorm unit : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro reference
  have near : ∀ᶠ unit : Adelesˣ in 𝓝 reference,
      finiteUnit (reference⁻¹ * unit) ∈ Set.range (Units.map integralEmbedding.toMonoidHom) := by
    apply (integralUnits_isOpen.preimage
      (finiteUnit_continuous.comp (continuous_const.mul continuous_id))).mem_nhds
    exact ⟨1, by simp⟩
  have localContinuous : Continuous (fun unit : Adelesˣ =>
      (adeleNorm reference : ℝ) * |(reference⁻¹ * unit).val.1|) :=
    continuous_const.mul
      ((Units.continuous_val.comp (continuous_const.mul continuous_id)).fst.abs)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with unit membership
  rw [← norm_of_integral_finite (reference⁻¹ * unit) membership, ← NNReal.coe_mul, ← map_mul,
    mul_inv_cancel_left]

theorem normPower_continuous (exponent : ℂ) : Continuous (fun unit : Adelesˣ => normPower unit exponent) := by
  have logarithm : Continuous (fun unit : Adelesˣ => Real.log (adeleNorm unit : ℝ)) :=
    norm_continuous.log (fun unit => (show (0 : ℝ) < (adeleNorm unit : ℝ) from adeleNorm_pos unit).ne')
  exact (continuous_const.mul (Complex.continuous_ofReal.comp logarithm)).cexp

theorem determinant_continuous {size : ℕ} :
    Continuous (GeneralLinearGroup.det : GeneralLinearGroup (Fin size) Adeles → Adelesˣ) := by
  apply Units.continuous_iff.mpr
  exact ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

theorem determinant_norm_continuous {size : ℕ} :
    Continuous (fun matrix : GeneralLinearGroup (Fin size) Adeles =>
      (adeleNorm (GeneralLinearGroup.det matrix) : ℝ)) :=
  norm_continuous.comp determinant_continuous

theorem determinant_weight_continuous {size : ℕ} (exponent : ℝ) :
    Continuous (fun matrix : GeneralLinearGroup (Fin size) Adeles =>
      (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) ^ exponent) :=
  determinant_norm_continuous.rpow_const (fun matrix => Or.inl
    (show (0 : ℝ) < (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) from adeleNorm_pos _).ne')

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicNormContinuity
