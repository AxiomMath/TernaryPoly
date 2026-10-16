module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalReconstruction
public import Mathlib.Tactic.LinearCombination
public import Mathlib.GroupTheory.GroupExtension.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {R : Type} [CommRing R]

def lineScalar (element : lineParabolic R) : Rˣ where
  val := element.val.val 0 0
  inv := element.val.inv 0 0
  val_inv := by
    have inverseZeros : element.val.inv 1 0 = 0 ∧ element.val.inv 2 0 = 0 :=
      inLine_inv element.property
    have identity := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 0 0)
      element.val.val_inv
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, inverseZeros.1,
      inverseZeros.2, mul_zero, add_zero, Matrix.one_apply, ite_true]
      using identity
  inv_val := by
    have identity := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 0 0)
      element.val.inv_val
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, element.property.1,
      element.property.2, mul_zero, add_zero, Matrix.one_apply, ite_true] using identity

def lineBinaryMatrix (element : lineParabolic R) : Matrix (Fin 2) (Fin 2) R :=
  !![element.val.val 1 1, element.val.val 1 2;
    element.val.val 2 1, element.val.val 2 2]

def lineBinaryInverse (element : lineParabolic R) : Matrix (Fin 2) (Fin 2) R :=
  !![element.val.inv 1 1, element.val.inv 1 2;
    element.val.inv 2 1, element.val.inv 2 2]

def lineBinary (element : lineParabolic R) : GeneralLinearGroup (Fin 2) R where
  val := lineBinaryMatrix element
  inv := lineBinaryInverse element
  val_inv := by
    ext row column
    have identity := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix row.succ column.succ)
      element.val.val_inv
    fin_cases row <;> fin_cases column <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
        lineBinaryMatrix, lineBinaryInverse,
        element.property.1, element.property.2] using identity
  inv_val := by
    ext row column
    have inverseZeros : element.val.inv 1 0 = 0 ∧ element.val.inv 2 0 = 0 :=
      inLine_inv element.property
    have lowerZero : element.val.inv row.succ 0 = 0 := by
      fin_cases row
      · exact inverseZeros.1
      · exact inverseZeros.2
    have identity := congrArg
      (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix row.succ column.succ)
      element.val.inv_val
    simp only [Matrix.mul_apply, Fin.sum_univ_three, lowerZero, zero_mul,
      zero_add] at identity
    fin_cases row <;> fin_cases column <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two,
        lineBinaryMatrix, lineBinaryInverse] using identity

def lineLeviProjection (R : Type) [CommRing R] :
    lineParabolic R →* (Rˣ × GeneralLinearGroup (Fin 2) R) where
  toFun element := (lineScalar element, lineBinary element)
  map_one' := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := by
    apply Prod.ext
    · apply Units.ext
      change (first.val.val * second.val.val) 0 0 =
        first.val.val 0 0 * second.val.val 0 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, second.property.1,
        second.property.2]
    · apply Units.ext
      ext row column
      change (lineBinary (first * second)).val row column =
        ((lineBinary first).val * (lineBinary second).val) row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
          lineBinary, lineBinaryMatrix,
          first.property.1, first.property.2]

def integralBadLineStabilizer : Subgroup IntegralGL3 :=
  arithmeticLevel ⊓ lineParabolic ℤ

def binaryRowStabilizer : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {element | ![0, 1] ᵥ* element.val = ![0, 1]}
  one_mem' := by simp
  mul_mem' {first second} firstLevel secondLevel := by
    change ![0, 1] ᵥ* (first.val * second.val) = ![0, 1]
    rw [← vecMul_vecMul, firstLevel, secondLevel]
  inv_mem' {element} level := by
    change ![0, 1] ᵥ* element.inv = ![0, 1]
    have identity := congrArg (fun vector => vector ᵥ* element.inv) level
    simpa only [vecMul_vecMul, element.val_inv, vecMul_one] using identity.symm

def binaryArithmeticLevel : Subgroup (GeneralLinearGroup (Fin 2) ℤ) :=
  binaryRowStabilizer.comap (GeneralLinearGroup.map (Int.castRingHom (ZMod 3)))

theorem mem_binaryArithmeticLevel_iff (binary : GeneralLinearGroup (Fin 2) ℤ) :
    binary ∈ binaryArithmeticLevel ↔
      ∀ column : Fin 2,
        (binary.val 1 column : ZMod 3) = if column = 1 then 1 else 0 := by
  change (![0, 1] ᵥ* (GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) binary).val =
    ![0, 1]) ↔ _
  constructor
  · intro level column
    have entry := congrFun level column
    fin_cases column <;>
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using entry
  · intro level
    funext column
    fin_cases column
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using level 0
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using level 1

theorem integralBadLineStabilizer_binary_level
    (element : integralBadLineStabilizer) :
    lineBinary (⟨element.val, element.property.2⟩ : lineParabolic ℤ) ∈
      binaryArithmeticLevel := by
  apply (mem_binaryArithmeticLevel_iff _).mpr
  intro column
  have level : lastRow ᵥ* (reductionThree element.val).val = lastRow :=
    element.property.1
  have entry := congrFun level column.succ
  fin_cases column <;>
      simpa [lastRow, lineBinary, lineBinaryMatrix, reductionThree,
        GeneralLinearGroup.map_apply, single_vecMul, one_smul] using entry

def integralBadLineLeviProjection :
    integralBadLineStabilizer →* (ℤˣ × binaryArithmeticLevel) where
  toFun element :=
    (lineScalar ⟨element.val, element.property.2⟩,
      ⟨lineBinary ⟨element.val, element.property.2⟩,
        integralBadLineStabilizer_binary_level element⟩)
  map_one' := by
    have identity := (lineLeviProjection ℤ).map_one
    apply Prod.ext
    · exact congrArg (fun pair : ℤˣ × GeneralLinearGroup (Fin 2) ℤ => pair.1) identity
    · apply Subtype.ext
      exact congrArg Prod.snd identity
  map_mul' first second := by
    have product := (lineLeviProjection ℤ).map_mul
      ⟨first.val, first.property.2⟩ ⟨second.val, second.property.2⟩
    apply Prod.ext
    · exact congrArg (fun pair : ℤˣ × GeneralLinearGroup (Fin 2) ℤ => pair.1) product
    · apply Subtype.ext
      exact congrArg Prod.snd product

def integralBadLineLeviSection :
    (ℤˣ × binaryArithmeticLevel) →* integralBadLineStabilizer where
  toFun pair :=
    ⟨lineLevi pair.1 pair.2.val,
      (integralLineLevi pair.1 pair.2.val
        ((mem_binaryArithmeticLevel_iff pair.2.val).mp pair.2.property)).property,
      lineLevi_mem pair.1 pair.2.val⟩
  map_one' := Subtype.ext ((lineLeviHom ℤ).map_one)
  map_mul' first second := Subtype.ext
    ((lineLeviHom ℤ).map_mul (first.1, first.2.val) (second.1, second.2.val))

theorem integralBadLineLeviProjection_section (pair : ℤˣ × binaryArithmeticLevel) :
    integralBadLineLeviProjection (integralBadLineLeviSection pair) = pair := by
  apply Prod.ext
  · apply Units.ext
    change (lineLevi pair.1 pair.2.val).val 0 0 = pair.1.val
    rw [lineLevi_val]
    rfl
  · apply Subtype.ext
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [integralBadLineLeviProjection, integralBadLineLeviSection,
        lineBinary, lineBinaryMatrix, lineLevi_val]

theorem integralBadLineLeviProjection_surjective :
    Function.Surjective integralBadLineLeviProjection := by
  intro pair
  exact ⟨integralBadLineLeviSection pair, integralBadLineLeviProjection_section pair⟩

theorem integralBadLineLeviSection_injective :
    Function.Injective integralBadLineLeviSection := by
  intro first second equality
  have projected := congrArg integralBadLineLeviProjection equality
  simpa only [integralBadLineLeviProjection_section] using projected

def lineRadicalCoordinates (element : lineParabolic R) : R × R :=
  (element.val.val 0 1 * (lineBinary element).inv 0 0 +
      element.val.val 0 2 * (lineBinary element).inv 1 0,
    element.val.val 0 1 * (lineBinary element).inv 0 1 +
      element.val.val 0 2 * (lineBinary element).inv 1 1)

theorem lineParabolic_radical_levi (element : lineParabolic R) :
    lineUnipotent (lineRadicalCoordinates element).1
        (lineRadicalCoordinates element).2 *
      lineLevi (lineScalar element) (lineBinary element) = element.val := by
  apply Units.ext
  ext row column
  have binaryIdentity := (lineBinary element).inv_val
  change lineBinaryInverse element * lineBinaryMatrix element = 1 at binaryIdentity
  have firstIdentity := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 0 0) binaryIdentity
  have secondIdentity := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 0 1) binaryIdentity
  have thirdIdentity := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 1 0) binaryIdentity
  have fourthIdentity := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) R => matrix 1 1) binaryIdentity
  simp [Matrix.mul_apply, Fin.sum_univ_two, lineBinaryMatrix, lineBinaryInverse] at firstIdentity secondIdentity thirdIdentity fourthIdentity
  rw [GeneralLinearGroup.coe_mul, lineLevi_val]
  fin_cases row <;> fin_cases column <;>
    simp [lineUnipotent, upperUnipotent, lineRadicalCoordinates, lineScalar,
      lineBinary, lineBinaryMatrix, lineBinaryInverse, Matrix.mul_apply, Fin.sum_univ_three,
      element.property.1, element.property.2] <;> first
      | linear_combination
          element.val.val 0 1 * firstIdentity + element.val.val 0 2 * thirdIdentity
      | linear_combination
          element.val.val 0 1 * secondIdentity + element.val.val 0 2 * fourthIdentity

theorem integralBadLineLeviProjection_eq_one_iff
    (element : integralBadLineStabilizer) :
    integralBadLineLeviProjection element = 1 ↔
      ∃ first second : ℤ, element.val = lineUnipotent first second := by
  constructor
  · intro projection
    have scalar := congrArg Prod.fst projection
    have binary := congrArg (fun pair : ℤˣ × binaryArithmeticLevel => pair.2.val)
      projection
    change lineScalar (⟨element.val, element.property.2⟩ : lineParabolic ℤ) = 1
      at scalar
    change lineBinary (⟨element.val, element.property.2⟩ : lineParabolic ℤ) = 1
      at binary
    let parabolicElement : lineParabolic ℤ := ⟨element.val, element.property.2⟩
    refine ⟨(lineRadicalCoordinates parabolicElement).1,
      (lineRadicalCoordinates parabolicElement).2, ?_⟩
    have decomposition := lineParabolic_radical_levi parabolicElement
    rw [scalar, binary, show lineLevi (1 : ℤˣ)
      (1 : GeneralLinearGroup (Fin 2) ℤ) = 1 from (lineLeviHom ℤ).map_one,
      mul_one] at decomposition
    exact decomposition.symm
  · rintro ⟨first, second, radical⟩
    apply Prod.ext
    · apply Units.ext
      change element.val.val 0 0 = 1
      rw [radical]
      rfl
    · apply Subtype.ext
      apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [integralBadLineLeviProjection, lineBinary, lineBinaryMatrix,
          radical, lineUnipotent, upperUnipotent]

theorem lineUnipotent_mem_integralBadLineStabilizer (first second : ℤ) :
    lineUnipotent first second ∈ integralBadLineStabilizer := by
  constructor
  · change lastRow ᵥ* (reductionThree (lineUnipotent first second)).val = lastRow
    funext column
    simp only [lastRow, single_vecMul, one_smul]
    change ((lineUnipotent first second).val 2 column : ZMod 3) =
      (Pi.single 2 1 : Fin 3 → ZMod 3) column
    fin_cases column <;> rfl
  · exact ⟨rfl, rfl⟩

def integralBadLineRadicalEmbedding :
    Multiplicative (ℤ × ℤ) →* integralBadLineStabilizer where
  toFun coordinates :=
    ⟨lineUnipotent coordinates.toAdd.1 coordinates.toAdd.2,
      lineUnipotent_mem_integralBadLineStabilizer
        coordinates.toAdd.1 coordinates.toAdd.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  map_mul' first second := by
    apply Subtype.ext
    apply Units.ext
    ext row column
    change (lineUnipotent (first.toAdd.1 + second.toAdd.1)
      (first.toAdd.2 + second.toAdd.2)).val row column =
        ((lineUnipotent first.toAdd.1 first.toAdd.2).val *
          (lineUnipotent second.toAdd.1 second.toAdd.2).val) row column
    fin_cases row <;> fin_cases column <;>
      simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem integralBadLineRadicalEmbedding_injective :
    Function.Injective integralBadLineRadicalEmbedding := by
  intro first second equality
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · exact congrArg (fun element : integralBadLineStabilizer => element.val.val 0 1)
      equality
  · exact congrArg (fun element : integralBadLineStabilizer => element.val.val 0 2)
      equality

theorem integralBadLineRadicalEmbedding_projection
    (coordinates : Multiplicative (ℤ × ℤ)) :
    integralBadLineLeviProjection (integralBadLineRadicalEmbedding coordinates) = 1 :=
  (integralBadLineLeviProjection_eq_one_iff _).mpr
    ⟨coordinates.toAdd.1, coordinates.toAdd.2, rfl⟩

def integralBadLineRadicalKernelMap :
    Multiplicative (ℤ × ℤ) →* integralBadLineLeviProjection.ker where
  toFun coordinates :=
    ⟨integralBadLineRadicalEmbedding coordinates,
      integralBadLineRadicalEmbedding_projection coordinates⟩
  map_one' := Subtype.ext integralBadLineRadicalEmbedding.map_one
  map_mul' first second := Subtype.ext
    (integralBadLineRadicalEmbedding.map_mul first second)

theorem integralBadLineRadicalKernelMap_bijective :
    Function.Bijective integralBadLineRadicalKernelMap := by
  constructor
  · intro first second equality
    apply integralBadLineRadicalEmbedding_injective
    exact congrArg Subtype.val equality
  · intro element
    obtain ⟨first, second, radical⟩ :=
      (integralBadLineLeviProjection_eq_one_iff element.val).mp element.property
    refine ⟨Multiplicative.ofAdd (first, second), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact radical.symm

def integralBadLineRadicalEquiv :
    Multiplicative (ℤ × ℤ) ≃* integralBadLineLeviProjection.ker :=
  MulEquiv.ofBijective integralBadLineRadicalKernelMap
    integralBadLineRadicalKernelMap_bijective

theorem integralBadLineRadicalEmbedding_range :
    integralBadLineRadicalEmbedding.range = integralBadLineLeviProjection.ker := by
  apply le_antisymm
  · rintro element ⟨coordinates, rfl⟩
    exact integralBadLineRadicalEmbedding_projection coordinates
  · intro element membership
    obtain ⟨coordinates, equality⟩ :=
      integralBadLineRadicalKernelMap_bijective.2 ⟨element, membership⟩
    exact ⟨coordinates, congrArg Subtype.val equality⟩

def integralBadLineExtension :
    GroupExtension (Multiplicative (ℤ × ℤ)) integralBadLineStabilizer
      (ℤˣ × binaryArithmeticLevel) where
  inl := integralBadLineRadicalEmbedding
  rightHom := integralBadLineLeviProjection
  inl_injective := integralBadLineRadicalEmbedding_injective
  range_inl_eq_ker_rightHom := integralBadLineRadicalEmbedding_range
  rightHom_surjective := integralBadLineLeviProjection_surjective

def integralBadLineSplitting : integralBadLineExtension.Splitting where
  toMonoidHom := integralBadLineLeviSection
  rightInverse_rightHom := integralBadLineLeviProjection_section

def integralBadLineSemidirectEquiv :
    SemidirectProduct (Multiplicative (ℤ × ℤ)) (ℤˣ × binaryArithmeticLevel)
        integralBadLineSplitting.conjAct ≃* integralBadLineStabilizer :=
  integralBadLineSplitting.semidirectProductMulEquiv

theorem integralBadLineStabilizer_rational_mem (element : integralBadLineStabilizer) :
    integralRational element.val ∈ fixedPointLevel rationalLevel standardBadLine := by
  rw [fixedPointLevel_standardBadLine]
  refine ⟨⟨⟨element.val, element.property.1⟩, rfl⟩, ?_⟩
  exact inLine_map (Int.castRingHom ℚ) element.val element.property.2

def integralBadLineRationalInclusion :
    integralBadLineStabilizer →* fixedPointLevel rationalLevel standardBadLine where
  toFun element :=
    ⟨integralRational element.val, integralBadLineStabilizer_rational_mem element⟩
  map_one' := Subtype.ext (integralRational.map_one)
  map_mul' first second := Subtype.ext (integralRational.map_mul first.val second.val)

theorem integralBadLineRationalInclusion_injective :
    Function.Injective integralBadLineRationalInclusion := by
  intro first second equality
  apply Subtype.ext
  apply Units.ext
  ext row column
  have entry := congrArg
    (fun element : fixedPointLevel rationalLevel standardBadLine =>
      element.val.val row column) equality
  change (first.val.val row column : ℚ) = (second.val.val row column : ℚ) at entry
  exact Int.cast_injective entry

theorem integralBadLineRationalInclusion_surjective :
    Function.Surjective integralBadLineRationalInclusion := by
  intro element
  have membership := element.property
  have membership : element.val ∈ rationalLevel ⊓ lineParabolic ℚ := by
    simpa only [fixedPointLevel_standardBadLine] using membership
  obtain ⟨integral, represented⟩ := membership.1
  have integralParabolic : integral.val ∈ lineParabolic ℤ := by
    have firstEntry := membership.2.1
    have secondEntry := membership.2.2
    change element.val.val 1 0 = 0 at firstEntry
    change element.val.val 2 0 = 0 at secondEntry
    rw [← represented] at firstEntry secondEntry
    constructor
    · apply Int.cast_injective (α := ℚ)
      exact firstEntry
    · apply Int.cast_injective (α := ℚ)
      exact secondEntry
  refine ⟨⟨integral.val, integral.property, integralParabolic⟩, ?_⟩
  apply Subtype.ext
  exact represented

def integralBadLineStabilizerEquiv :
    integralBadLineStabilizer ≃* fixedPointLevel rationalLevel standardBadLine :=
  MulEquiv.ofBijective integralBadLineRationalInclusion
    ⟨integralBadLineRationalInclusion_injective,
      integralBadLineRationalInclusion_surjective⟩

def standardBadLineSemidirectEquiv :
    SemidirectProduct (Multiplicative (ℤ × ℤ)) (ℤˣ × binaryArithmeticLevel)
        integralBadLineSplitting.conjAct ≃*
      fixedPointLevel rationalLevel standardBadLine :=
  integralBadLineSemidirectEquiv.trans integralBadLineStabilizerEquiv

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
