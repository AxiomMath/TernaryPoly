module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Norms

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineDecomposition

def binaryBlock (element : RationalGL3) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![element.val 1 1, element.val 1 2;
    element.val 2 1, element.val 2 2]

theorem line_det (element : RationalGL3) (membership : element ∈ lineParabolic ℚ) :
    element.val.det = element.val 0 0 * (binaryBlock element).det := by
  obtain ⟨firstZero, secondZero⟩ := membership
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [binaryBlock, firstZero, secondZero]
  ring

theorem line_corner_ne_zero (element : RationalGL3) (membership : element ∈ lineParabolic ℚ) :
    element.val 0 0 ≠ 0 := by
  intro vanishes
  apply GeneralLinearGroup.det_ne_zero element
  rw [line_det element membership, vanishes, zero_mul]

theorem line_binary_det_ne_zero (element : RationalGL3)
    (membership : element ∈ lineParabolic ℚ) : (binaryBlock element).det ≠ 0 := by
  intro vanishes
  apply GeneralLinearGroup.det_ne_zero element
  rw [line_det element membership, vanishes, mul_zero]

def binaryLeviBlock (element : RationalGL3) (membership : element ∈ lineParabolic ℚ) :
    BinaryRationalGL :=
  GeneralLinearGroup.mkOfDetNeZero (binaryBlock element)
    (line_binary_det_ne_zero element membership)

def rankOneBlock (element : RationalGL3) (membership : element ∈ lineParabolic ℚ) : ℚˣ :=
  Units.mk0 (element.val 0 0) (line_corner_ne_zero element membership)

theorem line_decomposition (element : RationalGL3) (membership : element ∈ lineParabolic ℚ) :
    element =
      lineLevi (rankOneBlock element membership) (binaryLeviBlock element membership) *
        lineUnipotent (element.val 0 1 / element.val 0 0) (element.val 0 2 / element.val 0 0) := by
  have firstZero := membership.1
  have secondZero := membership.2
  have corner := line_corner_ne_zero element membership
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi_val, upperUnipotent, binaryLeviBlock, binaryBlock, rankOneBlock,
      Matrix.mul_apply, Fin.sum_univ_three, firstZero, secondZero,
      mul_div_cancel₀ _ corner]

theorem map_lineUnipotent {Source Target : Type} [CommRing Source] [CommRing Target]
    (homomorphism : Source →+* Target) (first second : Source) :
    GeneralLinearGroup.map homomorphism (lineUnipotent first second) =
      lineUnipotent (homomorphism first) (homomorphism second) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [upperUnipotent]

theorem map_lineLevi {Source Target : Type} [CommRing Source] [CommRing Target]
    (homomorphism : Source →+* Target) (rankOneUnit : Sourceˣ)
    (binaryElement : GeneralLinearGroup (Fin 2) Source) :
    GeneralLinearGroup.map homomorphism (lineLevi rankOneUnit binaryElement) =
      lineLevi (Units.map homomorphism rankOneUnit)
        (GeneralLinearGroup.map homomorphism binaryElement) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [lineLevi_val]

theorem lineInduced_rankOneRational_norm_one {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ)
    (induced : IsInduced data .line cohomologicalPoint function)
    (rationalUnit : ℚˣ) (norm : adeleNorm (Units.map rationalAdele rationalUnit) = 1)
    (argument : AdelicGL) :
    function (lineLevi (Units.map rationalAdele rationalUnit) 1 * argument) = function argument := by
  rw [induced.2.2.2.2.1, data.chi.rational]
  simp [normPower, norm]

theorem induced_lineRational_invariant {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ)
    (induced : IsInduced data .line cohomologicalPoint function)
    (element : RationalGL3) (membership : element ∈ lineParabolic ℚ)
    (binaryNorm : adeleNorm (GeneralLinearGroup.det
      (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership))) = 1)
    (rankOneNorm : adeleNorm (Units.map rationalAdele (rankOneBlock element membership)) = 1)
    (argument : AdelicGL) : function (rationalGroup element * argument) = function argument := by
  have adelicDecomposition : rationalGroup element =
      lineLevi (Units.map rationalAdele (rankOneBlock element membership))
        (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership)) *
      lineUnipotent (rationalAdele (element.val 0 1 / element.val 0 0))
        (rationalAdele (element.val 0 2 / element.val 0 0)) := by
    conv_lhs => rw [line_decomposition element membership]
    rw [map_mul]
    exact congrArg₂ (fun first second : AdelicGL => first * second)
      (map_lineLevi rationalAdele _ _) (map_lineUnipotent rationalAdele _ _)
  have leviSplit : lineLevi (Units.map rationalAdele (rankOneBlock element membership))
      (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership)) =
      lineLevi 1 (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership)) *
        lineLevi (Units.map rationalAdele (rankOneBlock element membership)) 1 := by
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, lineLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (lineLeviHom Adeles).map_mul
        (1, GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership))
        (Units.map rationalAdele (rankOneBlock element membership), 1)
  rw [adelicDecomposition, leviSplit, mul_assoc, mul_assoc]
  exact (ParabolicInvariance.induced_binaryRational_norm_one data .line cohomologicalPoint
    function induced (binaryLeviBlock element membership) binaryNorm _).trans
      ((lineInduced_rankOneRational_norm_one data function induced _ rankOneNorm _).trans
        (induced.2.2.2.1 _ _ argument))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineDecomposition
