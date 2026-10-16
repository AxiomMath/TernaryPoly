module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.IntegralHermite
public import Mathlib.Analysis.PSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryIntegralHermite TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteMatrixWeight

def weight (binary : BinaryFiniteGL) : ℝ :=
  (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ)

theorem weight_pos (binary : BinaryFiniteGL) : 0 < weight binary := adeleNorm_pos _

theorem weight_mul (first second : BinaryFiniteGL) : weight (first * second) = weight first * weight second := by
  simp only [weight, atFinite_mul, map_mul, NNReal.coe_mul]

theorem weight_integral (binary : IntegralBinaryGL) :
    weight (GeneralLinearGroup.map integralEmbedding binary) = 1 := by
  rw [weight, Norm.adeleNorm_det_integral]
  rfl

theorem weight_rational (binary : BinaryRationalGL) :
    weight (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) binary) = |(binary.val.det : ℝ)|⁻¹ := by
  have determinant : GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) binary) =
      FiniteLatticeMeasure.rationalScale (GeneralLinearGroup.det binary) := by
    apply Units.ext
    exact (RingHom.map_det (algebraMap ℚ FiniteAdeles) binary.val).symm
  rw [weight, Norm.det_atFinite, determinant, ← FiniteLatticeMeasure.lattice_real_measure,
    FiniteLatticeMeasure.rational_lattice_measure]
  rfl

theorem weight_representative (index : Index) :
    weight (representative index) = |(index.1.val : ℝ)|⁻¹ * |(index.2.1.val : ℝ)|⁻¹ := by
  rw [representative, weight_rational, upper_val, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, sub_zero, Rat.cast_mul, Rat.cast_intCast, abs_mul, mul_inv]

def coset (index : Index) : Set BinaryFiniteGL :=
  (fun binary => representative index * binary) '' integralGroup

theorem coset_isCompact (index : Index) : IsCompact (coset index) :=
  integralGroup_isCompact.image (continuous_const.mul continuous_id)

theorem coset_isOpen (index : Index) : IsOpen (coset index) :=
  (Homeomorph.mulLeft (representative index)).isOpenMap _ integralGroup_isOpen

theorem coset_eq_preimage (index : Index) :
    coset index = (fun binary => (representative index)⁻¹ * binary) ⁻¹' integralGroup := by
  ext binary
  constructor
  · rintro ⟨element, membership, rfl⟩
    simpa only [Set.mem_preimage, inv_mul_cancel_left] using membership
  · intro membership
    exact ⟨(representative index)⁻¹ * binary, membership, mul_inv_cancel_left _ _⟩

theorem coset_measure (index : Index) : BinaryProductHaar.finiteMeasure (coset index) =
    BinaryProductHaar.finiteMeasure integralGroup := by
  rw [coset_eq_preimage, measure_preimage_mul]

theorem weight_on_coset (index : Index) (binary : BinaryFiniteGL) (membership : binary ∈ coset index) :
    weight binary = weight (representative index) := by
  obtain ⟨_, ⟨integer, rfl⟩, rfl⟩ := membership
  rw [weight_mul, weight_integral, mul_one]

theorem representative_integral (index : Index) : IntegralMatrix (representative index) := by
  refine ⟨!![(index.1.val : IntegralAdeles), (index.2.2.val : IntegralAdeles); 0, (index.2.1.val : IntegralAdeles)], ?_⟩
  change _ = (upper index.1 index.2.1 (index.2.2.val : ℤ)).val.map (algebraMap ℚ FiniteAdeles)
  rw [upper_val]
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp

theorem integral_eq_union : {binary : BinaryFiniteGL | IntegralMatrix binary} = ⋃ index : Index, coset index := by
  ext binary
  constructor
  · intro integral
    obtain ⟨index, compactPart, equality⟩ := exists_representative binary integral
    exact Set.mem_iUnion.mpr ⟨index, GeneralLinearGroup.map integralEmbedding compactPart,
      ⟨compactPart, rfl⟩, equality.symm⟩
  · intro membership
    obtain ⟨index, _, ⟨compactPart, rfl⟩, rfl⟩ := Set.mem_iUnion.mp membership
    exact integral_mul _ _ (representative_integral index) (integral_embedded compactPart)

theorem integral_isOpen : IsOpen {binary : BinaryFiniteGL | IntegralMatrix binary} := by
  rw [integral_eq_union]
  exact isOpen_iUnion coset_isOpen

def decay (exponent : ℕ) (integer : NonzeroInteger) : ℝ := |(integer.val : ℝ)|⁻¹ ^ exponent

theorem decay_nonnegative (exponent : ℕ) (integer : NonzeroInteger) : 0 ≤ decay exponent integer :=
  pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _

theorem decay_summable (exponent : ℕ) (large : 1 < exponent) : Summable (decay exponent) := by
  have bound : (1 : ℝ) < exponent := by exact_mod_cast large
  have result := (Real.summable_abs_int_rpow bound).subtype (fun integer : ℤ => integer ≠ 0)
  change Summable (fun integer : NonzeroInteger => |(integer.val : ℝ)|⁻¹ ^ exponent)
  simpa only [Function.comp_def, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast, inv_pow] using result

theorem natAbs_real (integer : ℤ) : (integer.natAbs : ℝ) = |(integer : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun value : ℤ => (value : ℝ)) (Int.natCast_natAbs integer)

theorem decay_count (integer : NonzeroInteger) :
    (integer.val.natAbs : ℝ) * decay 3 integer = decay 2 integer := by
  have nonzero : |(integer.val : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast integer.property)
  rw [natAbs_real, decay, decay]
  field_simp

theorem weight_cubed (index : Index) :
    weight (representative index) ^ 3 = decay 3 index.1 * decay 3 index.2.1 := by
  rw [weight_representative, mul_pow]
  rfl

theorem fiber_summable (first : NonzeroInteger) :
    Summable (fun pair : NonzeroInteger × Fin first.val.natAbs => decay 3 first * decay 3 pair.1) := by
  apply (summable_prod_of_nonneg (fun pair : NonzeroInteger × Fin first.val.natAbs =>
    mul_nonneg (decay_nonnegative 3 first) (decay_nonnegative 3 pair.1))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc] using ((decay_summable 3 (by norm_num)).mul_left (decay 3 first)).mul_left (first.val.natAbs : ℝ)

theorem fiber_sum (first : NonzeroInteger) :
    (∑' pair : NonzeroInteger × Fin first.val.natAbs, decay 3 first * decay 3 pair.1) =
      decay 2 first * ∑' second : NonzeroInteger, decay 3 second := by
  rw [(fiber_summable first).tsum_prod]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, decay_count, tsum_mul_left]

theorem representative_summable : Summable (fun index : Index => weight (representative index) ^ 3) := by
  have result : Summable (fun index : Index => decay 3 index.1 * decay 3 index.2.1) := by
    apply (summable_sigma_of_nonneg (fun index : Index =>
      mul_nonneg (decay_nonnegative 3 index.1) (decay_nonnegative 3 index.2.1))).mpr
    refine ⟨fiber_summable, ?_⟩
    simpa only [fiber_sum] using (decay_summable 2 (by norm_num)).mul_right (∑' second : NonzeroInteger, decay 3 second)
  exact result.congr (fun index => (weight_cubed index).symm)

theorem cube_integrableOn_coset (index : Index) :
    IntegrableOn (fun binary => weight binary ^ 3) (coset index) BinaryProductHaar.finiteMeasure := by
  have constant : IntegrableOn (fun _ : BinaryFiniteGL => weight (representative index) ^ 3)
      (coset index) BinaryProductHaar.finiteMeasure :=
    integrableOn_const (coset_isCompact index).measure_lt_top.ne
  exact constant.congr_fun (fun binary membership =>
    congrArg (fun value : ℝ => value ^ 3) (weight_on_coset index binary membership).symm)
      (coset_isOpen index).measurableSet

theorem cube_norm_integral_coset (index : Index) :
    (∫ binary in coset index, ‖weight binary ^ 3‖ ∂BinaryProductHaar.finiteMeasure) =
      mass * weight (representative index) ^ 3 := by
  rw [setIntegral_congr_fun (coset_isOpen index).measurableSet (fun binary membership =>
    congrArg (fun value : ℝ => ‖value ^ 3‖) (weight_on_coset index binary membership))]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (weight_pos _).le _), setIntegral_const,
    smul_eq_mul, Measure.real, coset_measure]
  rfl

theorem cube_integrableOn :
    IntegrableOn (fun binary => weight binary ^ 3) {binary | IntegralMatrix binary} BinaryProductHaar.finiteMeasure := by
  rw [integral_eq_union]
  apply integrableOn_iUnion_of_summable_integral_norm cube_integrableOn_coset
  simpa only [cube_norm_integral_coset] using representative_summable.mul_left mass

def majorant (binary : BinaryFiniteGL) : ℝ :=
  {binary | IntegralMatrix binary}.indicator (fun binary => weight binary ^ 3) binary

theorem majorant_integrable : Integrable majorant BinaryProductHaar.finiteMeasure :=
  (integrable_indicator_iff integral_isOpen.measurableSet).mpr cube_integrableOn

theorem majorant_nonnegative (binary : BinaryFiniteGL) : 0 ≤ majorant binary := by
  unfold majorant
  exact Set.indicator_nonneg (fun value _ => pow_nonneg (weight_pos value).le _) binary

theorem integrable_of_bound {E : Type*} [NormedAddCommGroup E]
    (function : BinaryFiniteGL → E) (measurable : AEStronglyMeasurable function BinaryProductHaar.finiteMeasure)
    (bound : ℝ) (supported : ∀ binary, ¬ IntegralMatrix binary → function binary = 0)
    (estimate : ∀ binary, IntegralMatrix binary → ‖function binary‖ ≤ bound * weight binary ^ 3) :
    Integrable function BinaryProductHaar.finiteMeasure := by
  apply (majorant_integrable.const_mul bound).mono' measurable
  apply Filter.Eventually.of_forall
  intro binary
  by_cases integral : IntegralMatrix binary
  · simpa only [majorant, Set.indicator_of_mem (show binary ∈ {binary | IntegralMatrix binary} from integral)] using estimate binary integral
  · simp only [supported binary integral, norm_zero, majorant, Set.indicator_of_notMem (show binary ∉ {binary | IntegralMatrix binary} from integral),
      mul_zero, le_refl]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteMatrixWeight
