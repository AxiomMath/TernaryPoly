module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def monoidHomLiftThroughInjective {G H M : Type*} [Monoid G] [Monoid H] [Monoid M]
    (source : G →* M) (embedding : H →* M) (injective : Function.Injective embedding)
    (lifts : ∀ element, ∃ lift, embedding lift = source element) : G →* H where
  toFun element := (lifts element).choose
  map_one' := injective (by rw [(lifts 1).choose_spec, map_one, map_one])
  map_mul' first second := injective (by
    rw [(lifts (first * second)).choose_spec, map_mul, map_mul,
      (lifts first).choose_spec, (lifts second).choose_spec])

theorem monoidHomLiftThroughInjective_spec {G H M : Type*} [Monoid G] [Monoid H] [Monoid M]
    (source : G →* M) (embedding : H →* M) (injective : Function.Injective embedding)
    (lifts : ∀ element, ∃ lift, embedding lift = source element) (element : G) :
    embedding (monoidHomLiftThroughInjective source embedding injective lifts element) = source element :=
  (lifts element).choose_spec

def upperLeftBlock {R : Type*} (matrix : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R :=
  fun row column => matrix row.castSucc column.castSucc

theorem upperLeftBlock_one {R : Type*} [Zero R] [One R] :
    upperLeftBlock (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem upperLeftBlock_mul_upper {R : Type*} [Semiring R]
    (first second : Matrix (Fin 3) (Fin 3) R) (zero0 : second 2 0 = 0) (zero1 : second 2 1 = 0) :
    upperLeftBlock (first * second) = upperLeftBlock first * upperLeftBlock second := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, zero0, zero1]

theorem upperLeftBlock_mul_lower {R : Type*} [Semiring R]
    (first second : Matrix (Fin 3) (Fin 3) R) (zero0 : first 0 2 = 0) (zero1 : first 1 2 = 0) :
    upperLeftBlock (first * second) = upperLeftBlock first * upperLeftBlock second := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperLeftBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, zero0, zero1]

def integralBinaryMatrix : GeneralLinearGroup (Fin 2) ℤ →* Matrix (Fin 2) (Fin 2) ℚ :=
  (Units.coeHom _).comp (GeneralLinearGroup.map (Int.castRingHom ℚ))

theorem integralBinaryMatrix_injective : Function.Injective integralBinaryMatrix := by
  intro first second equality
  apply Units.ext
  funext row column
  have entry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℚ => matrix row column) equality
  change (first.val row column : ℚ) = (second.val row column : ℚ) at entry
  exact_mod_cast entry

def identityPlaneBlockHom :
    flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) →* Matrix (Fin 2) (Fin 2) ℚ where
  toFun element := upperLeftBlock element.val.val
  map_one' := upperLeftBlock_one
  map_mul' first second := by
    have plane := (identityPlane_stabilizer_iff second.val).mp second.property |>.2
    exact upperLeftBlock_mul_upper first.val.val second.val.val plane.1 plane.2

def goodLineBlockHom :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →* Matrix (Fin 2) (Fin 2) ℚ where
  toFun element := upperLeftBlock element.val.val
  map_one' := upperLeftBlock_one
  map_mul' first second := by
    have line := (goodLine_stabilizer_iff first.val).mp first.property |>.2
    exact upperLeftBlock_mul_lower first.val.val second.val.val line.1 line.2

theorem identityPlaneBlockHom_integral
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    ∃ matrix, integralBinaryMatrix matrix = identityPlaneBlockHom element := by
  obtain ⟨first, second, matrix, equality⟩ := identityPlane_stabilizer_exists_blocks element
  refine ⟨matrix, ?_⟩
  change integralBinaryMatrix matrix = upperLeftBlock element.val.val
  rw [equality]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralBinaryMatrix, upperLeftBlock, GeneralLinearGroup.map_apply, planeUnipotent,
      planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem goodLineBlockHom_integral
    (element : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
    ∃ matrix, integralBinaryMatrix matrix = goodLineBlockHom element := by
  obtain ⟨first, second, matrix, equality⟩ := goodLine_stabilizer_exists_blocks element
  refine ⟨matrix, ?_⟩
  change integralBinaryMatrix matrix = upperLeftBlock element.val.val
  rw [equality]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralBinaryMatrix, upperLeftBlock, GeneralLinearGroup.map_apply, lowerPlaneUnipotent,
      planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

def identityPlaneLeviProjection :
    flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)) →* GeneralLinearGroup (Fin 2) ℤ :=
  monoidHomLiftThroughInjective identityPlaneBlockHom integralBinaryMatrix integralBinaryMatrix_injective
    identityPlaneBlockHom_integral

def goodLineLeviProjection :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →* GeneralLinearGroup (Fin 2) ℤ :=
  monoidHomLiftThroughInjective goodLineBlockHom integralBinaryMatrix integralBinaryMatrix_injective
    goodLineBlockHom_integral

theorem identityPlaneLeviProjection_spec
    (element : flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :
    integralBinaryMatrix (identityPlaneLeviProjection element) = upperLeftBlock element.val.val :=
  monoidHomLiftThroughInjective_spec identityPlaneBlockHom integralBinaryMatrix integralBinaryMatrix_injective
    identityPlaneBlockHom_integral element

theorem goodLineLeviProjection_spec
    (element : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
    integralBinaryMatrix (goodLineLeviProjection element) = upperLeftBlock element.val.val :=
  monoidHomLiftThroughInjective_spec goodLineBlockHom integralBinaryMatrix integralBinaryMatrix_injective
    goodLineBlockHom_integral element

end TernaryPeriodPolynomials.SphericalDetection.Helpers
