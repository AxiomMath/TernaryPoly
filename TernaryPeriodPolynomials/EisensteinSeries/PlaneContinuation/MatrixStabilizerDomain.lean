module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SubgroupFundamentalDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.NonzeroThetaIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain

def stabilizer (matrix : Rectangular ℚ) : Subgroup BinaryRationalGL where
  carrier := {element | matrix * element.val = matrix}
  one_mem' := by simp
  mul_mem' {first second} firstMem secondMem := by
    change matrix * (first.val * second.val) = matrix
    rw [← Matrix.mul_assoc, firstMem, secondMem]
  inv_mem' {element} membership := by
    change matrix * element⁻¹.val = matrix
    have inverse : element.val * element⁻¹.val = 1 := element.val_inv
    calc
      _ = (matrix * element.val) * element⁻¹.val := by rw [membership]
      _ = matrix := by rw [Matrix.mul_assoc, inverse, Matrix.mul_one]

def orbitMap (matrix : Rectangular ℚ) (coset : BinaryRationalGL ⧸ stabilizer matrix) : Rectangular ℚ :=
  matrix * coset.out⁻¹.val

theorem orbitMap_mk (matrix : Rectangular ℚ) (element : BinaryRationalGL) :
    orbitMap matrix (QuotientGroup.mk element) = matrix * element⁻¹.val := by
  obtain ⟨correction, equality⟩ := QuotientGroup.mk_out_eq_mul (stabilizer matrix) element
  unfold orbitMap
  rw [equality, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mul_assoc]
  have fixed : matrix * correction.val⁻¹.val = matrix := (correction⁻¹).property
  rw [fixed]

theorem orbitMap_injective (matrix : Rectangular ℚ) : Function.Injective (orbitMap matrix) := by
  intro first second equality
  have membership : first.out⁻¹ * second.out ∈ stabilizer matrix := by
    change matrix * (first.out⁻¹.val * second.out.val) = matrix
    rw [← Matrix.mul_assoc]
    change orbitMap matrix first * second.out.val = matrix
    rw [equality]
    change (matrix * second.out⁻¹.val) * second.out.val = matrix
    have inverse : second.out⁻¹.val * second.out.val = 1 := second.out.inv_val
    rw [Matrix.mul_assoc, inverse, Matrix.mul_one]
  have quotientEquality := QuotientGroup.eq.mpr membership
  simpa only [QuotientGroup.out_eq'] using quotientEquality

theorem orbitMap_nonzero (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0)
    (coset : BinaryRationalGL ⧸ stabilizer matrix) : orbitMap matrix coset ≠ 0 := by
  intro zero
  apply nonzero
  have equality := congrArg (fun value : Rectangular ℚ => value * coset.out.val) zero
  have inverse : coset.out⁻¹.val * coset.out.val = 1 := coset.out.inv_val
  change (matrix * coset.out⁻¹.val) * coset.out.val = 0 * coset.out.val at equality
  simpa only [Matrix.mul_assoc, inverse, Matrix.mul_one, Matrix.zero_mul] using equality

def domain (matrix : Rectangular ℚ) : Set BinaryAdelicGL :=
  SubgroupFundamentalDomain.domain (stabilizer matrix) BinaryFundamentalDomain.domain

theorem domain_measurable (matrix : Rectangular ℚ) : MeasurableSet (domain matrix) :=
  SubgroupFundamentalDomain.measurable _ _ BinaryFundamentalDomain.domain_measurable

theorem domain_fundamental (matrix : Rectangular ℚ) :
    IsFundamentalDomain (stabilizer matrix) (domain matrix) BinaryHaar.measure :=
  SubgroupFundamentalDomain.fundamental _ _ BinaryFundamentalDomain.domain_measurable
    BinaryFundamentalDomain.domain_unique BinaryHaar.measure

def term {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ) (binary : BinaryAdelicGL) : ℂ :=
  SingularCuspidality.weightedMatrixTerm data.cusp vector test (GodementIntegral.innerCharacter data parameter) point matrix binary

theorem term_translate {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    term data test vector parameter point matrix (rational • binary) =
      term data test vector parameter point (matrix * rational.val) binary := by
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [term, SingularCuspidality.weightedMatrixTerm, GodementUnfolding.rational_smul,
    matrixTerm_rational_binary, map_mul, characterValue, one_mul, data.cusp.leftRational]
  rfl

theorem term_invariant {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (matrix : Rectangular ℚ)
    (element : stabilizer matrix) (binary : BinaryAdelicGL) :
    term data test vector parameter point matrix (element • binary) = term data test vector parameter point matrix binary := by
  change term data test vector parameter point matrix (element.val • binary) = _
  rw [term_translate, element.property]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain
