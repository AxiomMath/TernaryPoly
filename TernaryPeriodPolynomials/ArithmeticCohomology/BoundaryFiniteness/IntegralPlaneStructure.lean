module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ArithmeticStabilizers
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.PresentedSemidirect
public import Mathlib.GroupTheory.GroupExtension.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.BoundaryFiniteness.IntegralPlaneStructure

noncomputable section

abbrev Plane := ArithmeticStabilizers.integralParabolic .plane
abbrev Levi := GeneralLinearGroup (Fin 2) ℤ × ℤˣ
abbrev Radical := Multiplicative ℤ × Multiplicative ℤ

theorem plane_entries (matrix : Plane) : matrix.val.val 2 0 = 0 ∧ matrix.val.val 2 1 = 0 := by
  have membership : ((matrix.val.val 2 0 : ℤ) : ℚ) = 0 ∧ ((matrix.val.val 2 1 : ℤ) : ℚ) = 0 := matrix.property
  exact ⟨Int.cast_eq_zero.mp membership.1, Int.cast_eq_zero.mp membership.2⟩

def topBlock (matrix : IntegralGL3) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![matrix.val 0 0, matrix.val 0 1; matrix.val 1 0, matrix.val 1 1]

theorem topBlock_mul (left right : Plane) :
    topBlock (left.val * right.val) = topBlock left.val * topBlock right.val := by
  have entries := plane_entries right
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [topBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, entries.1, entries.2]

theorem topBlock_one : topBlock 1 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

def binaryBlock (matrix : Plane) : GeneralLinearGroup (Fin 2) ℤ where
  val := topBlock matrix.val
  inv := topBlock matrix⁻¹.val
  val_inv := by
    rw [← topBlock_mul matrix matrix⁻¹]
    change topBlock (matrix * matrix⁻¹).val = 1
    rw [mul_inv_cancel]
    exact topBlock_one
  inv_val := by
    rw [← topBlock_mul matrix⁻¹ matrix]
    change topBlock (matrix⁻¹ * matrix).val = 1
    rw [inv_mul_cancel]
    exact topBlock_one

def binaryProjection : Plane →* GeneralLinearGroup (Fin 2) ℤ where
  toFun := binaryBlock
  map_one' := Units.ext topBlock_one
  map_mul' left right := Units.ext (topBlock_mul left right)

def cornerUnit (matrix : Plane) : ℤˣ where
  val := matrix.val.val 2 2
  inv := matrix⁻¹.val.val 2 2
  val_inv := by
    have equality := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 2) (matrix.val.mul_inv)
    have entries := plane_entries matrix
    simpa [Matrix.mul_apply, Fin.sum_univ_three, entries.1, entries.2] using equality
  inv_val := by
    have equality := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 2) (matrix.val.mul_inv)
    have entries := plane_entries matrix
    simpa [Matrix.mul_apply, Fin.sum_univ_three, entries.1, entries.2, mul_comm] using equality

def cornerProjection : Plane →* ℤˣ where
  toFun := cornerUnit
  map_one' := rfl
  map_mul' left right := by
    apply Units.ext
    have entries := plane_entries left
    change (left.val.val * right.val.val) 2 2 = left.val.val 2 2 * right.val.val 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, entries.1, entries.2]

def leviProjection : Plane →* Levi := binaryProjection.prod cornerProjection

def leviEmbedding : Levi →* Plane where
  toFun blocks := ⟨planeLevi blocks.1 blocks.2, by
    change IntegralFlags.rational (planeLevi blocks.1 blocks.2) ∈ parabolic .plane
    exact inPlane_map _ _ (planeLevi_mem blocks.1 blocks.2)⟩
  map_one' := by
    apply Subtype.ext
    exact (planeLeviHom ℤ).map_one
  map_mul' left right := by
    apply Subtype.ext
    exact (planeLeviHom ℤ).map_mul left right

theorem leviProjection_embedding (blocks : Levi) : leviProjection (leviEmbedding blocks) = blocks := by
  apply Prod.ext
  · apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  · apply Units.ext
    rfl

def radicalEmbedding : Radical →* Plane where
  toFun vector := ⟨planeUnipotent vector.1.toAdd vector.2.toAdd, by
    change IntegralFlags.rational (planeUnipotent vector.1.toAdd vector.2.toAdd) ∈ parabolic .plane
    constructor <;> rfl⟩
  map_one' := by
    apply Subtype.ext
    exact (planeUnipotentHom ℤ).map_one
  map_mul' left right := by
    apply Subtype.ext
    exact planeUnipotent_add _ _ _ _

theorem radicalEmbedding_injective : Function.Injective radicalEmbedding := by
  intro left right equality
  have first := congrArg (fun matrix : Plane => matrix.val.val 0 2) equality
  have second := congrArg (fun matrix : Plane => matrix.val.val 1 2) equality
  exact Prod.ext first second

theorem radical_range : radicalEmbedding.range = leviProjection.ker := by
  apply le_antisymm
  · rintro _ ⟨vector, rfl⟩
    change leviProjection (radicalEmbedding vector) = 1
    apply Prod.ext
    · apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;> rfl
    · apply Units.ext
      rfl
  · intro matrix membership
    have equality : leviProjection matrix = 1 := membership
    have binary : topBlock matrix.val = 1 := congrArg (fun blocks : Levi => blocks.1.val) equality
    have corner : matrix.val.val 2 2 = 1 := congrArg (fun blocks : Levi => blocks.2.val) equality
    have entries := plane_entries matrix
    refine ⟨(Multiplicative.ofAdd (matrix.val.val 0 2), Multiplicative.ofAdd (matrix.val.val 1 2)), ?_⟩
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro row column
    have b00 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix 0 0) binary
    have b01 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix 0 1) binary
    have b10 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix 1 0) binary
    have b11 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix 1 1) binary
    fin_cases row <;> fin_cases column <;>
      first | exact b00.symm | exact b01.symm | exact b10.symm | exact b11.symm |
        exact entries.1.symm | exact entries.2.symm | exact corner.symm | rfl

def extension : GroupExtension Radical Plane Levi :=
  ⟨radicalEmbedding, leviProjection, radicalEmbedding_injective, radical_range,
    fun blocks => ⟨leviEmbedding blocks, leviProjection_embedding blocks⟩⟩

def splitting : extension.Splitting := ⟨leviEmbedding, leviProjection_embedding⟩

theorem plane_finitelyPresented [Group.IsFinitelyPresented (GeneralLinearGroup (Fin 2) ℤ)] :
    Group.IsFinitelyPresented Plane := by
  let : Group.IsFinitelyPresented Radical := PresentedSemidirect.product_finitelyPresented
  let : Group.IsFinitelyPresented Levi := PresentedSemidirect.product_finitelyPresented
  let := PresentedSemidirect.finitelyPresented splitting.conjAct
  exact Group.IsFinitelyPresented.equiv splitting.semidirectProductMulEquiv

end

end TernaryPeriodPolynomials.BoundaryFiniteness.IntegralPlaneStructure
