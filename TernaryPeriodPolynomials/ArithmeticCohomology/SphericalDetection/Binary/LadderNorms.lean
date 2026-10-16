module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLoweringOperator (cusp : CuspidalRepresentation) (weight : ℤ) :
    Module.End ℂ (cuspAffineSmoothValues cusp) :=
  cuspAffineDifferential cusp 1 - Complex.I • cuspAffineDifferential cusp Complex.I +
    (Complex.I * (weight : ℂ) / 2) • 1

def cuspRaisingOperator (cusp : CuspidalRepresentation) (weight : ℤ) :
    Module.End ℂ (cuspAffineSmoothValues cusp) :=
  cuspAffineDifferential cusp 1 + Complex.I • cuspAffineDifferential cusp Complex.I +
    (Complex.I * (weight : ℂ) / 2) • 1

theorem cuspLoweringOperator_apply (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp) :
    (cuspLoweringOperator cusp weight vector).val = cuspLoweringVector cusp weight vector.val := rfl

theorem cuspRaisingOperator_apply (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp) :
    (cuspRaisingOperator cusp weight vector).val = cuspRaisingVector cusp weight vector.val := rfl

theorem cuspLadder_commutator (cusp : CuspidalRepresentation) (weight : ℤ) :
    cuspRaisingOperator cusp (weight - 2) * cuspLoweringOperator cusp weight -
      cuspLoweringOperator cusp (weight + 2) * cuspRaisingOperator cusp weight = (weight : ℂ) • 1 := by
  apply LinearMap.ext
  intro vector
  have commutator := LinearMap.congr_fun (cuspAffineDifferential_commutator cusp) vector
  change cuspAffineDifferential cusp Complex.I (cuspAffineDifferential cusp 1 vector) -
    cuspAffineDifferential cusp 1 (cuspAffineDifferential cusp Complex.I vector) =
      cuspAffineDifferential cusp 1 vector at commutator
  change cuspRaisingOperator cusp (weight - 2) (cuspLoweringOperator cusp weight vector) -
    cuspLoweringOperator cusp (weight + 2) (cuspRaisingOperator cusp weight vector) = (weight : ℂ) • vector
  calc
    _ = (2 * Complex.I) •
        (cuspAffineDifferential cusp Complex.I (cuspAffineDifferential cusp 1 vector) -
          cuspAffineDifferential cusp 1 (cuspAffineDifferential cusp Complex.I vector) -
            cuspAffineDifferential cusp 1 vector) + (-(Complex.I ^ 2 * (weight : ℂ))) • vector := by
      simp only [cuspRaisingOperator, cuspLoweringOperator, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul,
        Int.cast_sub, Int.cast_add, Int.cast_ofNat]
      module
    _ = _ := by rw [commutator]; simp

theorem cuspRotationWeight_inner_add_two (cusp : CuspidalRepresentation)
    (first second : cusp.H) (weight : ℤ)
    (first_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) first = (angle : ℂ) ^ weight • first)
    (second_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) second = (angle : ℂ) ^ (weight + 2) • second) :
    inner ℂ first second = 0 := by
  let angle : Circle := ⟨Complex.I, by change dist Complex.I 0 = 1; simp⟩
  have unit_phase : (starRingEnd ℂ) ((angle : ℂ) ^ weight) * (angle : ℂ) ^ weight = 1 := by
    rw [← Circle.coe_zpow, mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have nonzero : (angle : ℂ) ≠ 0 := Complex.I_ne_zero
  have square : (angle : ℂ) ^ (2 : ℤ) = -1 := by
    change Complex.I ^ (2 : ℤ) = -1
    norm_num
  have equality := cuspUnitary_inner cusp (atInfinity (binaryRotations angle)) first second
  rw [first_rotation, second_rotation, inner_smul_left, inner_smul_right,
    zpow_add₀ nonzero, square] at equality
  have negative : -inner ℂ first second = inner ℂ first second := by
    calc
      _ = ((starRingEnd ℂ) ((angle : ℂ) ^ weight) * (angle : ℂ) ^ weight) *
          (-1) * inner ℂ first second := by rw [unit_phase]; ring
      _ = _ := by convert equality using 1; ring
  exact CharZero.neg_eq_self_iff.mp negative

theorem cuspLoweringOperator_skew (cusp : CuspidalRepresentation) (weight : ℤ)
    (first second : cuspAffineSmoothValues cusp) :
    inner ℂ (cuspLoweringOperator cusp weight first).val second.val +
      inner ℂ first.val (cuspRaisingOperator cusp weight second).val = 0 := by
  have horizontal := cuspAffineDifferential_skew cusp 1 first second
  have vertical := cuspAffineDifferential_skew cusp Complex.I first second
  change inner ℂ
      ((cuspAffineDifferential cusp 1 first).val -
        Complex.I • (cuspAffineDifferential cusp Complex.I first).val +
          (Complex.I * (weight : ℂ) / 2) • first.val) second.val +
    inner ℂ first.val
      ((cuspAffineDifferential cusp 1 second).val +
        Complex.I • (cuspAffineDifferential cusp Complex.I second).val +
          (Complex.I * (weight : ℂ) / 2) • second.val) = 0
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right,
    map_div₀, map_mul, map_intCast, map_ofNat, Complex.conj_I]
  linear_combination horizontal + Complex.I * vertical

theorem cuspRaisingOperator_skew (cusp : CuspidalRepresentation) (weight : ℤ)
    (first second : cuspAffineSmoothValues cusp) :
    inner ℂ (cuspRaisingOperator cusp weight first).val second.val +
      inner ℂ first.val (cuspLoweringOperator cusp weight second).val = 0 := by
  have horizontal := cuspAffineDifferential_skew cusp 1 first second
  have vertical := cuspAffineDifferential_skew cusp Complex.I first second
  change inner ℂ
      ((cuspAffineDifferential cusp 1 first).val +
        Complex.I • (cuspAffineDifferential cusp Complex.I first).val +
          (Complex.I * (weight : ℂ) / 2) • first.val) second.val +
    inner ℂ first.val
      ((cuspAffineDifferential cusp 1 second).val -
        Complex.I • (cuspAffineDifferential cusp Complex.I second).val +
          (Complex.I * (weight : ℂ) / 2) • second.val) = 0
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_sub_right, inner_smul_right,
    map_div₀, map_mul, map_intCast, map_ofNat, Complex.conj_I]
  linear_combination horizontal - Complex.I * vertical

theorem cuspRaisingOperator_sub_two (cusp : CuspidalRepresentation) (weight : ℤ) :
    cuspRaisingOperator cusp (weight - 2) = cuspRaisingOperator cusp weight - Complex.I • 1 := by
  simp only [cuspRaisingOperator, Int.cast_sub, Int.cast_ofNat]
  module

theorem cuspLoweringOperator_add_two (cusp : CuspidalRepresentation) (weight : ℤ) :
    cuspLoweringOperator cusp (weight + 2) = cuspLoweringOperator cusp weight + Complex.I • 1 := by
  simp only [cuspLoweringOperator, Int.cast_add, Int.cast_ofNat]
  module

theorem cuspLadder_norm_identity (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp)
    (rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) vector.val = (angle : ℂ) ^ weight • vector.val) :
    ‖(cuspRaisingOperator cusp weight vector).val‖ ^ 2 -
      ‖(cuspLoweringOperator cusp weight vector).val‖ ^ 2 = (weight : ℝ) * ‖vector.val‖ ^ 2 := by
  have lower_rotation := cuspLoweringVector_rotation cusp vector.val weight vector.property rotation
  have upper_rotation := cuspRaisingVector_rotation cusp vector.val weight vector.property rotation
  have lower_orth : inner ℂ vector.val (cuspLoweringOperator cusp weight vector).val = 0 := by
    apply inner_eq_zero_symm.mp
    apply cuspRotationWeight_inner_add_two cusp _ _ (weight - 2) lower_rotation
    simpa only [sub_add_cancel] using rotation
  have upper_orth : inner ℂ vector.val (cuspRaisingOperator cusp weight vector).val = 0 :=
    cuspRotationWeight_inner_add_two cusp _ _ weight rotation upper_rotation
  have lower_skew := cuspLoweringOperator_skew cusp weight vector (cuspLoweringOperator cusp weight vector)
  have upper_skew := cuspRaisingOperator_skew cusp weight vector (cuspRaisingOperator cusp weight vector)
  have lower_shift :
      inner ℂ vector.val (cuspRaisingOperator cusp (weight - 2) (cuspLoweringOperator cusp weight vector)).val =
        inner ℂ vector.val (cuspRaisingOperator cusp weight (cuspLoweringOperator cusp weight vector)).val := by
    rw [cuspRaisingOperator_sub_two]
    change inner ℂ vector.val
      ((cuspRaisingOperator cusp weight (cuspLoweringOperator cusp weight vector)).val -
        Complex.I • (cuspLoweringOperator cusp weight vector).val) = _
    rw [inner_sub_right, inner_smul_right, lower_orth, mul_zero, sub_zero]
  have upper_shift :
      inner ℂ vector.val (cuspLoweringOperator cusp (weight + 2) (cuspRaisingOperator cusp weight vector)).val =
        inner ℂ vector.val (cuspLoweringOperator cusp weight (cuspRaisingOperator cusp weight vector)).val := by
    rw [cuspLoweringOperator_add_two]
    change inner ℂ vector.val
      ((cuspLoweringOperator cusp weight (cuspRaisingOperator cusp weight vector)).val +
        Complex.I • (cuspRaisingOperator cusp weight vector).val) = _
    rw [inner_add_right, inner_smul_right, upper_orth, mul_zero, add_zero]
  have commutator := congrArg (fun operator : Module.End ℂ (cuspAffineSmoothValues cusp) =>
    inner ℂ vector.val (operator vector).val) (cuspLadder_commutator cusp weight)
  change inner ℂ vector.val
      ((cuspRaisingOperator cusp (weight - 2) (cuspLoweringOperator cusp weight vector)).val -
        (cuspLoweringOperator cusp (weight + 2) (cuspRaisingOperator cusp weight vector)).val) =
    inner ℂ vector.val ((weight : ℂ) • vector.val) at commutator
  rw [inner_sub_right, inner_smul_right, lower_shift, upper_shift] at commutator
  have complex_identity :
      inner ℂ (cuspRaisingOperator cusp weight vector).val (cuspRaisingOperator cusp weight vector).val -
        inner ℂ (cuspLoweringOperator cusp weight vector).val (cuspLoweringOperator cusp weight vector).val =
          (weight : ℂ) * inner ℂ vector.val vector.val := by
    linear_combination upper_skew - lower_skew + commutator
  simp only [inner_self_eq_norm_sq_to_K] at complex_identity
  change (‖(cuspRaisingOperator cusp weight vector).val‖ : ℂ) ^ 2 -
      (‖(cuspLoweringOperator cusp weight vector).val‖ : ℂ) ^ 2 =
        (weight : ℂ) * (‖vector.val‖ : ℂ) ^ 2 at complex_identity
  exact_mod_cast complex_identity

theorem cuspRaisingVector_ne_zero_of_pos (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (nonzero : vector ≠ 0) (positive : 0 < weight) : cuspRaisingVector cusp weight vector ≠ 0 := by
  intro zero
  have identity := cuspLadder_norm_identity cusp weight ⟨vector, regular⟩ rotation
  rw [cuspRaisingOperator_apply, cuspLoweringOperator_apply, zero, norm_zero, zero_pow (by decide),
    zero_sub] at identity
  have positive_norm : 0 < ‖vector‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have positive_weight : 0 < (weight : ℝ) := by exact_mod_cast positive
  nlinarith [sq_nonneg ‖cuspLoweringVector cusp weight vector‖]

theorem cuspLoweringVector_ne_zero_of_neg (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (nonzero : vector ≠ 0) (negative : weight < 0) : cuspLoweringVector cusp weight vector ≠ 0 := by
  intro zero
  have identity := cuspLadder_norm_identity cusp weight ⟨vector, regular⟩ rotation
  rw [cuspRaisingOperator_apply, cuspLoweringOperator_apply, zero, norm_zero, zero_pow (by decide),
    sub_zero] at identity
  have positive_norm : 0 < ‖vector‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have negative_weight : (weight : ℝ) < 0 := by exact_mod_cast negative
  nlinarith [sq_nonneg ‖cuspRaisingVector cusp weight vector‖]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
