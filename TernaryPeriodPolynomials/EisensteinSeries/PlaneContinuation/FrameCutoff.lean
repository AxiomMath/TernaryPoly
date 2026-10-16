module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Godement
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalHeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameCutoff

theorem frame_unipotent (point : AdelicGL) (first second : Adeles) :
    frame (planeUnipotent first second * point) = frame point := by
  have fixed : (planeUnipotent first second)⁻¹.val * standard = standard := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;> simp [columns, planeUnipotent, Matrix.one_apply]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, fixed]

theorem frame_planeLevi (point : AdelicGL) (binary : BinaryAdelicGL) (scalar : Adelesˣ) :
    frame (planeLevi binary scalar * point) = frame point * binary⁻¹.val := by
  have identity : (planeLevi binary scalar)⁻¹.val * standard = standard * binary⁻¹.val := by
    rw [standard, mul_standard]
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [columns, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, identity, Matrix.mul_assoc]

theorem frame_parabolic (point : AdelicGL) (parabolic : planeParabolic Adeles) :
    frame (parabolic.val * point) = frame point * (planeBinaryBlock parabolic)⁻¹.val := by
  rw [planeParabolic_factorization, mul_assoc, frame_unipotent, frame_planeLevi]

def mass (cutoff : Rectangular Adeles → ℂ) (point : AdelicGL) : ℂ :=
  ∫ binary : BinaryAdelicGL, cutoff (frame point * binary.val) ∂BinaryHaar.measure

def CompactInvariant (cutoff : Rectangular Adeles → ℂ) : Prop :=
  ∀ compact : AdelicGL, inMaximalCompact compact → ∀ value : Rectangular Adeles,
    cutoff (compact⁻¹.val * value) = cutoff value

theorem mass_constant (cutoff : Rectangular Adeles → ℂ) (invariant : CompactInvariant cutoff)
    (point : AdelicGL) : mass cutoff point = mass cutoff 1 := by
  have pointFrame : frame point = frame (compactPart point) * (planeBinaryBlock (parabolicPart point))⁻¹.val := by
    conv_lhs => rw [parabolicPart_mul_compactPart point]
    exact frame_parabolic _ _
  have integrandEquality (binary : BinaryAdelicGL) :
      cutoff (frame point * binary.val) =
        cutoff (standard * ((planeBinaryBlock (parabolicPart point))⁻¹ * binary).val) := by
    rw [pointFrame, frame, Matrix.mul_assoc, Matrix.mul_assoc,
      invariant _ (compactPart_mem point), Units.val_mul]
  unfold mass
  simp only [integrandEquality]
  rw [integral_mul_left_eq_self (fun binary : BinaryAdelicGL => cutoff (standard * binary.val))]
  simp only [frame, inv_one, Units.val_one, Matrix.one_mul]

def normalize (cutoff : Rectangular Adeles → ℂ) (value : Rectangular Adeles) : ℂ :=
  cutoff value / mass cutoff 1

theorem normalize_invariant (cutoff : Rectangular Adeles → ℂ) (invariant : CompactInvariant cutoff) :
    CompactInvariant (normalize cutoff) := by
  intro compact membership value
  simp only [normalize, invariant compact membership value]

theorem normalize_mass (cutoff : Rectangular Adeles → ℂ) (invariant : CompactInvariant cutoff)
    (nonzero : mass cutoff 1 ≠ 0) (point : AdelicGL) : mass (normalize cutoff) point = 1 := by
  unfold mass normalize
  rw [integral_div]
  change mass cutoff point / mass cutoff 1 = 1
  rw [mass_constant cutoff invariant point, div_self nonzero]

theorem recovery {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular Adeles → ℂ) (invariant : CompactInvariant cutoff)
    (nonzero : mass cutoff 1 ≠ 0) :
    VectorGodement.sectionFunction data (VectorGodement.recoveryTest induced (normalize cutoff)) parameter = function :=
  VectorGodement.recovery_of_mass_one induced (normalize cutoff) (normalize_mass cutoff invariant nonzero)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameCutoff
