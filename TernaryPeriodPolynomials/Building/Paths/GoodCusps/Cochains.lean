module

public import TernaryPeriodPolynomials.Building.Paths.GoodCusps.Geometry
public import Mathlib.GroupTheory.Complement

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers

theorem tuple_three_eta {Source : Type} (tuple : Fin 3 → Source) :
    ![tuple 0, tuple 1, tuple 2] = tuple := by
  funext index
  fin_cases index <;> rfl

def arithmeticTransversal : rationalLevel.RightTransversal := default

def arithmeticProjection (matrix : RationalGL3) : rationalLevel :=
  (arithmeticTransversal.property.equiv matrix).1

theorem arithmeticProjection_mul (group_element : rationalLevel) (matrix : RationalGL3) :
    arithmeticProjection (group_element.val * matrix) =
      group_element * arithmeticProjection matrix := by
  exact congrArg Prod.fst (arithmeticTransversal.property.equiv_mul_left group_element matrix)

theorem arithmeticProjection_tuple (first second third : RationalGL3) :
    (fun index => (arithmeticProjection (![first, second, third] index)).val) =
      ![(arithmeticProjection first).val, (arithmeticProjection second).val,
        (arithmeticProjection third).val] := by
  funext index
  fin_cases index <;> rfl

def projectedCocycle {n : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  ⟨⟨fun tuple => cocycle.val.val (fun index => (arithmeticProjection (tuple index)).val), by
    intro group_element tuple
    have tuple_eq : (fun index =>
        (arithmeticProjection (group_element.val * tuple index)).val) =
        fun index => group_element.val * (arithmeticProjection (tuple index)).val := by
      funext index
      rw [arithmeticProjection_mul]
      rfl
    change cocycle.val.val (fun index =>
      (arithmeticProjection (group_element.val * tuple index)).val) = _
    rw [tuple_eq]
    exact cocycle.val.property group_element _⟩, by
    change differentialTwo rationalLevel (rationalCoefficientComponent n trivialCharacter)
      ⟨_, _⟩ = 0
    funext tuple
    have closed := congrFun cocycle.property
      (fun index => (arithmeticProjection (tuple index)).val)
    simpa only [cocycles, LinearMap.mem_ker, differentialTwo, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.zero_apply, arithmeticProjection_tuple] using closed⟩

def projectionHomotopy {n : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    cochains rationalLevel (rationalCoefficientComponent n trivialCharacter) 1 :=
  ⟨fun tuple => cocycle.val.val ![tuple 0,
      (arithmeticProjection (tuple 0)).val, (arithmeticProjection (tuple 1)).val] -
    cocycle.val.val ![tuple 0, tuple 1, (arithmeticProjection (tuple 1)).val], by
    intro group_element tuple
    change cocycle.val.val ![group_element.val * tuple 0,
        (arithmeticProjection (group_element.val * tuple 0)).val,
        (arithmeticProjection (group_element.val * tuple 1)).val] -
      cocycle.val.val ![group_element.val * tuple 0, group_element.val * tuple 1,
        (arithmeticProjection (group_element.val * tuple 1)).val] = _
    simp only [arithmeticProjection_mul, Subgroup.coe_mul]
    have equivariant (first second third : RationalGL3) :
        cocycle.val.val ![group_element.val * first, group_element.val * second,
          group_element.val * third] =
        rationalCoefficientComponent n trivialCharacter group_element.val
          (cocycle.val.val ![first, second, third]) := by
      have tuple_eq : (fun index => group_element.val * ![first, second, third] index) =
          ![group_element.val * first, group_element.val * second, group_element.val * third] := by
        funext index
        fin_cases index <;> rfl
      simpa only [tuple_eq] using cocycle.val.property group_element ![first, second, third]
    rw [equivariant, equivariant, map_sub]⟩

theorem projectionHomotopy_boundary {n : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    boundaryMap rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (projectionHomotopy cocycle) = projectedCocycle cocycle - cocycle := by
  apply Subtype.ext
  apply Subtype.ext
  funext tuple
  have closed (first second third fourth : RationalGL3) :
      cocycle.val.val ![second, third, fourth] - cocycle.val.val ![first, third, fourth] +
        cocycle.val.val ![first, second, fourth] - cocycle.val.val ![first, second, third] = 0 :=
    congrFun cocycle.property ![first, second, third, fourth]
  have first_closed := closed (tuple 0) (tuple 1) (tuple 2)
    (arithmeticProjection (tuple 2)).val
  have second_closed := closed (tuple 0) (tuple 1) (arithmeticProjection (tuple 1)).val
    (arithmeticProjection (tuple 2)).val
  have third_closed := closed (tuple 0) (arithmeticProjection (tuple 0)).val
    (arithmeticProjection (tuple 1)).val (arithmeticProjection (tuple 2)).val
  change
    (cocycle.val.val ![tuple 1, (arithmeticProjection (tuple 1)).val,
      (arithmeticProjection (tuple 2)).val] -
      cocycle.val.val ![tuple 1, tuple 2, (arithmeticProjection (tuple 2)).val]) -
    (cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 0)).val,
      (arithmeticProjection (tuple 2)).val] -
      cocycle.val.val ![tuple 0, tuple 2, (arithmeticProjection (tuple 2)).val]) +
    (cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 0)).val,
      (arithmeticProjection (tuple 1)).val] -
      cocycle.val.val ![tuple 0, tuple 1, (arithmeticProjection (tuple 1)).val]) =
    cocycle.val.val (fun index => (arithmeticProjection (tuple index)).val) -
      cocycle.val.val tuple
  have projection_eq : (fun index => (arithmeticProjection (tuple index)).val) =
      ![(arithmeticProjection (tuple 0)).val, (arithmeticProjection (tuple 1)).val,
        (arithmeticProjection (tuple 2)).val] := (tuple_three_eta _).symm
  rw [projection_eq]
  apply sub_eq_zero.mp
  calc
    _ = -(cocycle.val.val ![tuple 1, tuple 2, (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, tuple 2, (arithmeticProjection (tuple 2)).val] +
          cocycle.val.val ![tuple 0, tuple 1, (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, tuple 1, tuple 2]) +
        (cocycle.val.val ![tuple 1, (arithmeticProjection (tuple 1)).val,
            (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 1)).val,
            (arithmeticProjection (tuple 2)).val] +
          cocycle.val.val ![tuple 0, tuple 1, (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, tuple 1, (arithmeticProjection (tuple 1)).val]) -
        (cocycle.val.val ![(arithmeticProjection (tuple 0)).val,
            (arithmeticProjection (tuple 1)).val, (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 1)).val,
            (arithmeticProjection (tuple 2)).val] +
          cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 0)).val,
            (arithmeticProjection (tuple 2)).val] -
          cocycle.val.val ![tuple 0, (arithmeticProjection (tuple 0)).val,
            (arithmeticProjection (tuple 1)).val]) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_neg]
      rw [tuple_three_eta]
      ring
    _ = 0 := by rw [first_closed, second_closed, third_closed]; simp

end TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers
