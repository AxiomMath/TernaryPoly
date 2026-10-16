module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.PathCoordinatePackage
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Action

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

def badLineFlag : Flags .line := QuotientGroup.mk (1 : RationalGL3)

theorem badLineFlag_fixed (matrix : badLineSubgroup) : matrix.val • badLineFlag = badLineFlag := by
  change (QuotientGroup.mk (matrix.val * 1) : Flags .line) = QuotientGroup.mk 1
  rw [mul_one]
  apply QuotientGroup.eq.mpr
  change Adelic.InLineParabolic (matrix.val⁻¹ * 1)
  rw [mul_one]
  exact Adelic.inLine_inv matrix.property.2

theorem stratumClass_zero_exists_cochain (degree : ℕ) (side : Side)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (zero_class : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side)
        (restrictionCocycle degree trivialCharacter side cocycle) = 0) :
    ∃ cochain : MaximalCochains degree trivialCharacter side 1,
      differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side) cochain =
          (restrictionCocycle degree trivialCharacter side cocycle).val := by
  have member := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) side)))).mp zero_class
  obtain ⟨cochain, equality⟩ := member
  exact ⟨cochain, congrArg Subtype.val equality⟩

def badLinePrimitive (degree : ℕ)
    (cochain : MaximalCochains degree trivialCharacter .line 1)
    (matrix : badLineSubgroup) : HomogeneousPoly degree :=
  cochain.val ![1, matrix.val] badLineFlag

theorem badLineCochain_equivariance (degree : ℕ)
    (cochain : MaximalCochains degree trivialCharacter .line 1)
    (first second : badLineSubgroup) :
    cochain.val ![first.val, (first * second).val] badLineFlag =
      rationalCoefficientComponent degree trivialCharacter first.val
        (badLinePrimitive degree cochain second) := by
  have translated := cochain.property (⟨first.val, first.property.1⟩ : rationalLevel)
    (![1, second.val] : Fin 2 → RationalGL3)
  have vertices : (fun index => first.val * (![1, second.val] : Fin 2 → RationalGL3) index) =
      ![first.val, (first * second).val] := by
    funext index
    fin_cases index <;> simp
  rw [vertices] at translated
  have inverse_fixed := badLineFlag_fixed first⁻¹
  change first.val⁻¹ • badLineFlag = badLineFlag at inverse_fixed
  have value := congrFun translated badLineFlag
  change cochain.val ![first.val, (first * second).val] badLineFlag =
    rationalCoefficientComponent degree trivialCharacter first.val
      (cochain.val ![1, second.val] (first.val⁻¹ • badLineFlag)) at value
  rw [inverse_fixed] at value
  exact value

theorem lineClass_zero_exists_primitive (degree : ℕ)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (zero_class : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    ∃ primitive : badLineSubgroup → HomogeneousPoly degree,
      ∀ first second : badLineSubgroup,
        cocycle.val.val ![1, first.val, (first * second).val] =
          rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
            primitive (first * second) + primitive first := by
  obtain ⟨cochain, differential⟩ := stratumClass_zero_exists_cochain degree .line cocycle zero_class
  refine ⟨badLinePrimitive degree cochain, ?_⟩
  intro first second
  have value := congrArg (fun current => current.val ![1, first.val, (first * second).val] badLineFlag)
    differential
  change cochain.val ![first.val, (first * second).val] badLineFlag -
    cochain.val ![1, (first * second).val] badLineFlag + cochain.val ![1, first.val] badLineFlag =
      cocycle.val.val ![1, first.val, (first * second).val] at value
  rw [badLineCochain_equivariance] at value
  exact value.symm

theorem mixedBarEdge_of_linePrimitive {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : badLineSubgroup → HomogeneousPoly degree)
    (differential : ∀ first second : badLineSubgroup,
      cocycle.val.val ![1, first.val, (first * second).val] =
        rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
          primitive (first * second) + primitive first)
    (levi radical : badLineSubgroup) :
    mixedBarEdge cocycle levi.val radical.val =
      (rationalCoefficientComponent degree trivialCharacter levi.val
        (primitive (levi⁻¹ * radical * levi))).val - (primitive radical).val -
      ((rationalCoefficientComponent degree trivialCharacter radical.val
        (primitive levi)).val - (primitive levi).val) := by
  have first := differential levi (levi⁻¹ * radical * levi)
  have second := differential radical levi
  have product : levi * (levi⁻¹ * radical * levi) = radical * levi := by simp [mul_assoc]
  rw [product] at first
  unfold mixedBarEdge
  change (cocycle.val.val ![1, levi.val, (radical * levi).val]).val -
    (cocycle.val.val ![1, radical.val, (radical * levi).val]).val = _
  rw [first, second]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

theorem lineClass_zero_radicalCocycle {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (pure : PureMixedBadLine cocycle)
    (zero_class : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    ∃ primitive : badLineSubgroup → HomogeneousPoly degree,
      (∀ first second : badLineSubgroup,
        cocycle.val.val ![1, first.val, (first * second).val] =
          rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
            primitive (first * second) + primitive first) ∧
      ∀ first second third fourth : ℤ,
        let first_radical : badLineSubgroup :=
          ⟨(integralRadical first second).val,
            (integralRadical first second).property, ⟨rfl, rfl⟩⟩
        let second_radical : badLineSubgroup :=
          ⟨(integralRadical third fourth).val,
            (integralRadical third fourth).property, ⟨rfl, rfl⟩⟩
        primitive (first_radical * second_radical) =
          rationalCoefficientComponent degree trivialCharacter first_radical.val
            (primitive second_radical) + primitive first_radical := by
  obtain ⟨primitive, differential⟩ := lineClass_zero_exists_primitive degree cocycle zero_class
  refine ⟨primitive, differential, ?_⟩
  intro first second third fourth
  let first_radical : badLineSubgroup :=
    ⟨(integralRadical first second).val, (integralRadical first second).property, ⟨rfl, rfl⟩⟩
  let second_radical : badLineSubgroup :=
    ⟨(integralRadical third fourth).val, (integralRadical third fourth).property, ⟨rfl, rfl⟩⟩
  have relation := differential first_radical second_radical
  have zero_value := pure.1 first second third fourth
  have first_val : first_radical.val = Adelic.lineUnipotent (first : ℚ) (second : ℚ) :=
    integralRadical_val first second
  have second_val : second_radical.val = Adelic.lineUnipotent (third : ℚ) (fourth : ℚ) :=
    integralRadical_val third fourth
  simp only [Subgroup.coe_mul, first_val, second_val] at relation
  rw [zero_value] at relation
  change primitive (first_radical * second_radical) = _
  have rearranged := congrArg
    (fun value : HomogeneousPoly degree => value + primitive (first_radical * second_radical))
    relation
  rw [zero_add] at rearranged
  have target : primitive (first_radical * second_radical) =
      rationalCoefficientComponent degree trivialCharacter first_radical.val
        (primitive second_radical) + primitive first_radical := by
    rw [first_val]
    exact rearranged.trans (by abel)
  exact target

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
