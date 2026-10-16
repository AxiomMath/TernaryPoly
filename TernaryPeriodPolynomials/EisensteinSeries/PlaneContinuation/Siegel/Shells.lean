module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Siegel.Integration

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelMeasurability

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShells

abbrev Interval := Set.Icc (0 : ℝ) 1
abbrev Horizontal := Set.Icc (-1 : ℝ) 1
abbrev Parameter := IntegralBinaryGL × Interval × Interval × Horizontal × Circle

def argument (horizontal height : ℝ) : UpperHalfPlane :=
  ⟨⟨horizontal, Real.exp height⟩, Real.exp_pos height⟩

theorem argument_continuous : Continuous (fun value : ℝ × ℝ => argument value.1 value.2) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  have equality : (UpperHalfPlane.coe ∘ fun value : ℝ × ℝ => argument value.1 value.2) =
      fun value => (value.1 : ℂ) + (Real.exp value.2 : ℂ) * Complex.I := by
    funext value
    apply Complex.ext <;> simp only [Function.comp_apply, argument, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [equality]
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_snd)).mul continuous_const)

def parameterize (integer : ℤ) (natural : ℕ) (parameter : Parameter) : BinaryAdelicGL :=
  AdelicSiegelCover.chart parameter.1 (scale ((integer : ℝ) + parameter.2.1.val))
    (argument parameter.2.2.2.1.val ((natural : ℝ) + parameter.2.2.1.val)) (RealSiegelSet.rightFactor parameter.2.2.2.2)

theorem parameterize_continuous (integer : ℤ) (natural : ℕ) : Continuous (parameterize integer natural) := by
  unfold parameterize AdelicSiegelCover.chart
  apply Continuous.mul
  · exact atFinite_continuous.comp (integralMap_continuous.comp continuous_fst)
  · apply StageTranslation.atInfinity_continuous.comp
    apply Continuous.mul
    · exact scalar_continuous.comp (scale_continuous.comp
        (continuous_const.add (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))
    · apply Continuous.mul
      · apply unit_continuous.comp
        apply argument_continuous.comp (f := fun parameter : Parameter =>
          (parameter.2.2.2.1.val, (natural : ℝ) + parameter.2.2.1.val))
        exact (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))).prodMk
          (continuous_const.add (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd))))
      · exact RealSiegelSet.rightFactor_continuous.comp
          (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))

def shell (integer : ℤ) (natural : ℕ) : Set BinaryAdelicGL := Set.range (parameterize integer natural)

theorem shell_compact (integer : ℤ) (natural : ℕ) : IsCompact (shell integer natural) :=
  isCompact_range (parameterize_continuous integer natural)

theorem shell_subset_region (integer : ℤ) (natural : ℕ) : shell integer natural ⊆ AdelicSiegelCover.region := by
  rintro point ⟨parameter, rfl⟩
  refine ⟨parameter.1, scale ((integer : ℝ) + parameter.2.1.val), Real.exp_pos _,
    argument parameter.2.2.2.1.val ((natural : ℝ) + parameter.2.2.1.val), ?_, ?_,
    RealSiegelSet.rightFactor parameter.2.2.2.2, ⟨parameter.2.2.2.2, rfl⟩, rfl⟩
  · change 1 ≤ Real.exp ((natural : ℝ) + parameter.2.2.1.val)
    exact Real.one_le_exp (add_nonneg (Nat.cast_nonneg _) parameter.2.2.1.property.1)
  · exact abs_le.mpr parameter.2.2.2.1.property

theorem region_eq_union : AdelicSiegelCover.region = ⋃ integer : ℤ, ⋃ natural : ℕ, shell integer natural := by
  apply Set.Subset.antisymm
  · rintro point ⟨integral, scalar, positive, value, height, horizontal, right, ⟨rotation, rfl⟩, rfl⟩
    let integer := Int.floor (Real.log scalar.val)
    let natural := Nat.floor (Real.log value.im)
    have nonnegativeLog : 0 ≤ Real.log value.im := Real.log_nonneg height
    let first : Interval := ⟨Real.log scalar.val - integer, by
      constructor
      · exact sub_nonneg.mpr (Int.floor_le _)
      · have bounded := Int.lt_floor_add_one (Real.log scalar.val)
        dsimp only [integer]
        linarith⟩
    let second : Interval := ⟨Real.log value.im - natural, by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le nonnegativeLog)
      · have bounded := Nat.lt_floor_add_one (Real.log value.im)
        dsimp only [natural]
        linarith⟩
    refine Set.mem_iUnion.mpr ⟨integer, Set.mem_iUnion.mpr ⟨natural, (integral, first, second, ⟨value.re, abs_le.mp horizontal⟩, rotation), ?_⟩⟩
    have scalarEquality : scale ((integer : ℝ) + first.val) = scalar := by
      apply Units.ext
      change Real.exp ((integer : ℝ) + (Real.log scalar.val - integer)) = scalar.val
      rw [add_sub_cancel, Real.exp_log positive]
    have argumentEquality : argument value.re ((natural : ℝ) + second.val) = value := by
      apply UpperHalfPlane.ext
      apply Complex.ext
      · rfl
      · change Real.exp ((natural : ℝ) + (Real.log value.im - natural)) = value.im
        rw [add_sub_cancel, Real.exp_log value.im_pos]
    change AdelicSiegelCover.chart integral (scale ((integer : ℝ) + first.val))
      (argument value.re ((natural : ℝ) + second.val)) _ = _
    rw [scalarEquality, argumentEquality]
  · intro point membership
    obtain ⟨integer, natural, belongs⟩ := Set.mem_iUnion₂.mp membership
    exact shell_subset_region integer natural belongs

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelShells
