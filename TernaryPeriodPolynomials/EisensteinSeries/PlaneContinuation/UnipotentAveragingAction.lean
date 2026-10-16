module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.SliceDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FundamentalAveraging

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction

theorem stabilizer_add (basis : BinaryRationalGL) (first second : Adeles) :
    SingularFrames.stabilizer basis (first + second) =
      SingularFrames.stabilizer basis first * SingularFrames.stabilizer basis second := by
  simp only [SingularFrames.stabilizer, BinaryStrongApproximation.unipotent_add]
  group

theorem stabilizer_zero (basis : BinaryRationalGL) : SingularFrames.stabilizer basis 0 = 1 := by
  have unipotentZero : binaryUnipotent (0 : Adeles) = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;> simp [binaryUnipotent]
  simp only [SingularFrames.stabilizer, unipotentZero, mul_one, mul_inv_cancel]

def Parameters (_basis : BinaryRationalGL) := Multiplicative Adeles

instance parameterGroup (basis : BinaryRationalGL) : Group (Parameters basis) :=
  inferInstanceAs (Group (Multiplicative Adeles))

def ofAdele (basis : BinaryRationalGL) (parameter : Adeles) : Parameters basis := Multiplicative.ofAdd parameter

def hom (basis : BinaryRationalGL) : Parameters basis →* BinaryAdelicGL where
  toFun parameter := SingularFrames.stabilizer basis (Multiplicative.toAdd parameter)
  map_one' := stabilizer_zero basis
  map_mul' first second := stabilizer_add basis (Multiplicative.toAdd first) (Multiplicative.toAdd second)

scoped instance action (basis : BinaryRationalGL) : MulAction (Parameters basis) BinaryAdelicGL :=
  MulAction.compHom BinaryAdelicGL (hom basis)

variable (basis : BinaryRationalGL)

theorem smul_eq (parameter : Parameters basis) (point : BinaryAdelicGL) :
    parameter • point = SingularFrames.stabilizer basis (Multiplicative.toAdd parameter) * point := rfl

theorem measurableAction : MeasurableConstSMul (Parameters basis) BinaryAdelicGL :=
  ⟨fun _ => measurable_const.mul measurable_id⟩

theorem invariantAction : SMulInvariantMeasure (Parameters basis) BinaryAdelicGL BinaryHaar.measure :=
  ⟨fun parameter _ _ => measure_preimage_mul BinaryHaar.measure (SingularFrames.stabilizer basis (Multiplicative.toAdd parameter)) _⟩

theorem stabilizer_commutes_rational (first : Adeles) (second : ℚ) :
    Commute (SingularFrames.stabilizer basis first)
      (GeneralLinearGroup.map rationalAdele (basis * binaryUnipotent second * basis⁻¹)) := by
  have rationalEquality : GeneralLinearGroup.map rationalAdele (basis * binaryUnipotent second * basis⁻¹) =
      SingularFrames.stabilizer basis (rationalAdele second) := by
    simp only [SingularFrames.stabilizer, map_mul, map_inv, BinaryStrongApproximation.unipotent_map]
  rw [rationalEquality]
  change SingularFrames.stabilizer basis first * SingularFrames.stabilizer basis (rationalAdele second) =
    SingularFrames.stabilizer basis (rationalAdele second) * SingularFrames.stabilizer basis first
  rw [← stabilizer_add, ← stabilizer_add, add_comm]

theorem commutingAction (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) :
    SMulCommClass (Parameters basis) (unipotents matrix) BinaryAdelicGL := by
  constructor
  intro parameter element point
  obtain ⟨rationalParameter, equality⟩ := kernel_conjugate_unipotent matrix nonzero basis zeroFirst element
  change SingularFrames.stabilizer basis (Multiplicative.toAdd parameter) *
      (GeneralLinearGroup.map rationalAdele element.val.val * point) =
    GeneralLinearGroup.map rationalAdele element.val.val * (SingularFrames.stabilizer basis (Multiplicative.toAdd parameter) * point)
  rw [equality, ← mul_assoc, (stabilizer_commutes_rational basis (Multiplicative.toAdd parameter) rationalParameter).eq, mul_assoc]

theorem unipotent_continuous : Continuous (fun parameter : Adeles => binaryUnipotent parameter) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp only [binaryUnipotent] <;> fun_prop
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp only [binaryUnipotent] <;> fun_prop

theorem stabilizer_continuous : Continuous (SingularFrames.stabilizer basis) :=
  (continuous_const.mul unipotent_continuous).mul continuous_const

theorem slice_invariant (parameter : Adeles) (point : BinaryAdelicGL) :
    SingularFrames.stabilizer basis parameter * point ∈ IdeleSlice.determinantSlice ↔ point ∈ IdeleSlice.determinantSlice :=
  IdeleSlice.determinantSlice_mul _ _ (SingularFrames.stabilizer_det basis parameter)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentAveragingAction
