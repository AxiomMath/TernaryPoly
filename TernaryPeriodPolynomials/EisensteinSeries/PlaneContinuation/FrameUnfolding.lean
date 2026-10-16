module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameFlags

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameFlags

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameUnfolding

noncomputable def parameterize (pair : Flags .plane × BinaryRationalGL) : Frame :=
  changeBasis (ofMatrix pair.1.out) pair.2

theorem parameterize_val (flag : Flags .plane) (binary : BinaryRationalGL) :
    (parameterize (flag, binary)).val = columns flag.out.val * binary.val := rfl

theorem parameterize_surjective : Function.Surjective parameterize := by
  intro frame
  let flag : Flags .plane := QuotientGroup.mk (complete frame)
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk (complete frame) :=
    QuotientGroup.out_eq' flag
  obtain ⟨binary, equality⟩ := (flag_eq_iff flag.out (complete frame)).mp sameFlag
  refine ⟨(flag, binary), ?_⟩
  apply Subtype.ext
  rw [parameterize_val, ← equality, complete_columns]

theorem parameterize_injective : Function.Injective parameterize := by
  rintro ⟨firstFlag, firstBinary⟩ ⟨secondFlag, secondBinary⟩ equality
  have frameEquality : columns firstFlag.out.val * firstBinary.val =
      columns secondFlag.out.val * secondBinary.val := congrArg Subtype.val equality
  have binaryInverse : secondBinary.val * secondBinary⁻¹.val = 1 := secondBinary.val_inv
  have secondColumns : columns secondFlag.out.val =
      columns firstFlag.out.val * (firstBinary * secondBinary⁻¹).val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, frameEquality, Matrix.mul_assoc, binaryInverse, Matrix.mul_one]
  have sameFlag : firstFlag = secondFlag := by
    have quotientEquality := (flag_eq_iff firstFlag.out secondFlag.out).mpr
      ⟨firstBinary * secondBinary⁻¹, secondColumns⟩
    simpa only [QuotientGroup.out_eq'] using quotientEquality
  subst secondFlag
  have sameBinary : firstBinary = secondBinary :=
    Units.ext (columns_right_cancel firstFlag.out firstBinary.val secondBinary.val frameEquality)
  rw [sameBinary]

noncomputable def equivalence : (Flags .plane × BinaryRationalGL) ≃ Frame :=
  Equiv.ofBijective parameterize ⟨parameterize_injective, parameterize_surjective⟩

theorem equivalence_apply (flag : Flags .plane) (binary : BinaryRationalGL) :
    (equivalence (flag, binary)).val = columns flag.out.val * binary.val := rfl

theorem summable_iff {Target : Type*} [NormedAddCommGroup Target] (function : Frame → Target) :
    Summable function ↔ Summable (fun pair : Flags .plane × BinaryRationalGL =>
      function (parameterize pair)) := equivalence.summable_iff.symm

theorem hasSum_iff {Target : Type*} [NormedAddCommGroup Target] (function : Frame → Target) (value : Target) :
    HasSum function value ↔ HasSum (fun pair : Flags .plane × BinaryRationalGL =>
      function (parameterize pair)) value := equivalence.hasSum_iff.symm

theorem tsum_unfold {Target : Type*} [NormedAddCommGroup Target] [CompleteSpace Target]
    (function : Frame → Target) (summable : Summable function) :
    ∑' frame, function frame = ∑' flag : Flags .plane, ∑' binary : BinaryRationalGL,
      function (parameterize (flag, binary)) := by
  rw [← equivalence.tsum_eq function]
  exact ((summable_iff function).mp summable).tsum_prod

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameUnfolding
