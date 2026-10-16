module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Reduction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PlaneDecomposition

def binaryBlock (element : RationalGL3) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![element.val 0 0, element.val 0 1;
    element.val 1 0, element.val 1 1]

theorem plane_det (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) :
    element.val.det = (binaryBlock element).det * element.val 2 2 := by
  obtain ⟨firstZero, secondZero⟩ := membership
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [binaryBlock, firstZero, secondZero]
  ring

theorem plane_corner_ne_zero (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) :
    element.val 2 2 ≠ 0 := by
  intro vanishes
  apply GeneralLinearGroup.det_ne_zero element
  rw [plane_det element membership, vanishes, mul_zero]

theorem plane_binary_det_ne_zero (element : RationalGL3)
    (membership : element ∈ planeParabolic ℚ) : (binaryBlock element).det ≠ 0 := by
  intro vanishes
  apply GeneralLinearGroup.det_ne_zero element
  rw [plane_det element membership, vanishes, zero_mul]

def binaryLeviBlock (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) :
    BinaryRationalGL :=
  GeneralLinearGroup.mkOfDetNeZero (binaryBlock element)
    (plane_binary_det_ne_zero element membership)

def rankOneBlock (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) : ℚˣ :=
  Units.mk0 (element.val 2 2) (plane_corner_ne_zero element membership)

theorem plane_decomposition (element : RationalGL3) (membership : element ∈ planeParabolic ℚ) :
    element =
      planeUnipotent (element.val 0 2 / element.val 2 2) (element.val 1 2 / element.val 2 2) *
        planeLevi (binaryLeviBlock element membership) (rankOneBlock element membership) := by
  have firstZero := membership.1
  have secondZero := membership.2
  have corner := plane_corner_ne_zero element membership
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock,
      binaryLeviBlock, binaryBlock, rankOneBlock, Matrix.mul_apply, Fin.sum_univ_three,
      firstZero, secondZero, corner]

theorem map_planeUnipotent {Source Target : Type} [CommRing Source] [CommRing Target]
    (homomorphism : Source →+* Target) (first second : Source) :
    GeneralLinearGroup.map homomorphism (planeUnipotent first second) =
      planeUnipotent (homomorphism first) (homomorphism second) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [planeUnipotent]

theorem map_planeLevi {Source Target : Type} [CommRing Source] [CommRing Target]
    (homomorphism : Source →+* Target) (binaryElement : GeneralLinearGroup (Fin 2) Source)
    (rankOneUnit : Sourceˣ) :
    GeneralLinearGroup.map homomorphism (planeLevi binaryElement rankOneUnit) =
      planeLevi (GeneralLinearGroup.map homomorphism binaryElement)
        (Units.map homomorphism rankOneUnit) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [planeLevi, planeBlock]

theorem induced_planeRational_invariant {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint function)
    (element : RationalGL3) (membership : element ∈ planeParabolic ℚ)
    (norm : adeleNorm (GeneralLinearGroup.det
      (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership))) = 1)
    (argument : AdelicGL) : function (rationalGroup element * argument) = function argument := by
  have adelicDecomposition : rationalGroup element =
      planeUnipotent (rationalAdele (element.val 0 2 / element.val 2 2))
        (rationalAdele (element.val 1 2 / element.val 2 2)) *
      planeLevi (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership))
        (Units.map rationalAdele (rankOneBlock element membership)) := by
    conv_lhs => rw [plane_decomposition element membership]
    rw [map_mul]
    exact congrArg₂ (fun first second : AdelicGL => first * second)
      (map_planeUnipotent rationalAdele _ _) (map_planeLevi rationalAdele _ _)
  rw [adelicDecomposition, mul_assoc, induced.2.2.2.1]
  have leviSplit : planeLevi
      (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership))
      (Units.map rationalAdele (rankOneBlock element membership)) =
      planeLevi (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership)) 1 *
        planeLevi 1 (Units.map rationalAdele (rankOneBlock element membership)) := by
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, planeLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (planeLeviHom Adeles).map_mul
        (GeneralLinearGroup.map rationalAdele (binaryLeviBlock element membership), 1)
        (1, Units.map rationalAdele (rankOneBlock element membership))
  rw [leviSplit, mul_assoc]
  exact (ParabolicInvariance.induced_binaryRational_norm_one data .plane cohomologicalPoint
    function induced (binaryLeviBlock element membership) norm _).trans
      (ParabolicInvariance.planeInduced_rankOneRational data function induced
        (rankOneBlock element membership) argument)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PlaneDecomposition
