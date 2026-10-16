module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalEisenstein

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BruhatCells

theorem lineUnipotent_inv {R : Type} [CommRing R] (first second : R) :
    (lineUnipotent first second)⁻¹ = lineUnipotent (-first) (-second) := by
  apply Units.ext
  rfl

def openRepresentative (coordinates : ℚ × ℚ) : RationalGL3 :=
  lineUnipotent (-coordinates.1) (-coordinates.2) * weyl

def openFlag (coordinates : ℚ × ℚ) : Flags .plane :=
  QuotientGroup.mk (openRepresentative coordinates)

theorem openRepresentative_inv (coordinates : ℚ × ℚ) :
    (openRepresentative coordinates)⁻¹ =
      weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 := by
  rw [openRepresentative, _root_.mul_inv_rev, lineUnipotent_inv, neg_neg, neg_neg]

theorem openRepresentative_product_corner (representative : RationalGL3)
    (coordinates : ℚ × ℚ) :
    (representative⁻¹ * openRepresentative coordinates).val 2 2 =
      (representative⁻¹).val 2 0 := by
  simp [openRepresentative, upperUnipotent, weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem openFlag_injective : Function.Injective openFlag := by
  rintro ⟨first₁, first₂⟩ ⟨second₁, second₂⟩ equality
  have related := QuotientGroup.eq.mp equality
  change (openRepresentative (first₁, first₂))⁻¹ * openRepresentative (second₁, second₂) ∈
    planeParabolic ℚ at related
  rw [openRepresentative_inv] at related
  have first := related.1
  have second := related.2
  simp [openRepresentative, upperUnipotent, weyl, Matrix.mul_apply,
    Fin.sum_univ_three] at first second
  exact Prod.ext (by linarith) (by linarith)

theorem openFlag_of_corner_ne_zero (representative : RationalGL3)
    (nonzero : (representative⁻¹).val 2 0 ≠ 0) :
    (QuotientGroup.mk representative : Flags .plane) =
      openFlag ((representative⁻¹).val 2 1 / (representative⁻¹).val 2 0,
        (representative⁻¹).val 2 2 / (representative⁻¹).val 2 0) := by
  apply QuotientGroup.eq.mpr
  simp only [GeneralLinearGroup.coe_inv] at nonzero
  constructor <;>
    simp [openRepresentative, upperUnipotent, weyl, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp [nonzero] <;> ring

theorem corner_ne_zero_of_openFlag (representative : RationalGL3) (coordinates : ℚ × ℚ)
    (equality : (QuotientGroup.mk representative : Flags .plane) = openFlag coordinates) :
    (representative⁻¹).val 2 0 ≠ 0 := by
  have related : representative⁻¹ * openRepresentative coordinates ∈ planeParabolic ℚ :=
    QuotientGroup.eq.mp equality
  have corner := PlaneDecomposition.plane_corner_ne_zero
    (representative⁻¹ * openRepresentative coordinates) related
  rwa [openRepresentative_product_corner] at corner

theorem mem_openFlag_range (representative : RationalGL3) :
    (QuotientGroup.mk representative : Flags .plane) ∈ Set.range openFlag ↔
      (representative⁻¹).val 2 0 ≠ 0 := by
  constructor
  · rintro ⟨coordinates, equality⟩
    exact corner_ne_zero_of_openFlag representative coordinates equality.symm
  · intro nonzero
    exact ⟨_, (openFlag_of_corner_ne_zero representative nonzero).symm⟩

theorem binaryRow_exists (first second : ℚ) (nonzero : first ≠ 0 ∨ second ≠ 0) :
    ∃ binary : BinaryRationalGL, binary.val 1 0 = first ∧ binary.val 1 1 = second := by
  rcases nonzero with firstNonzero | secondNonzero
  · have determinant : (!![0, 1; first, second] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
      simpa [Matrix.det_fin_two] using firstNonzero
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ determinant, rfl, rfl⟩
  · have determinant : (!![1, 0; first, second] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
      simpa [Matrix.det_fin_two] using secondNonzero
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ determinant, rfl, rfl⟩

theorem closed_representative (representative : RationalGL3)
    (closed : (representative⁻¹).val 2 0 = 0) :
    ∃ binary : BinaryRationalGL,
      (QuotientGroup.mk representative : Flags .plane) =
        QuotientGroup.mk (lineLevi 1 binary) := by
  simp only [GeneralLinearGroup.coe_inv] at closed
  have nonzero : (representative⁻¹).val 2 1 ≠ 0 ∨ (representative⁻¹).val 2 2 ≠ 0 := by
    by_contra vanishes
    push Not at vanishes
    simp only [GeneralLinearGroup.coe_inv] at vanishes
    have impossible := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix 2 2)
      (representative⁻¹).mul_inv
    simp [Matrix.mul_apply, Fin.sum_univ_three, closed, vanishes.1, vanishes.2] at impossible
  obtain ⟨binary, first, second⟩ := binaryRow_exists _ _ nonzero
  simp only [GeneralLinearGroup.coe_inv] at first second
  refine ⟨binary⁻¹, QuotientGroup.eq.mpr ?_⟩
  constructor
  · simp [lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three, closed]
  · have equation := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℚ => matrix 1 0)
      binary.mul_inv
    simpa [lineLevi_val, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, first, second] using equation

theorem lineLevi_not_open (binary : BinaryRationalGL) :
    (QuotientGroup.mk (lineLevi 1 binary) : Flags .plane) ∉ Set.range openFlag := by
  rw [mem_openFlag_range]
  change ¬ ((lineLevi 1 binary)⁻¹).val 2 0 ≠ 0
  have zero : ((lineLevi 1 binary)⁻¹).val 2 0 = 0 := by
    have inverse := (lineLeviHom ℚ).map_inv (1, binary)
    change lineLevi (1 : ℚˣ)⁻¹ binary⁻¹ = (lineLevi 1 binary)⁻¹ at inverse
    rw [← inverse, inv_one, lineLevi_val]
    rfl
  exact fun nonzero => nonzero zero

theorem flag_dichotomy (flag : Flags .plane) :
    (∃ coordinates, flag = openFlag coordinates) ∨
      ∃ binary : BinaryRationalGL, flag = QuotientGroup.mk (lineLevi 1 binary) := by
  induction flag using Quotient.inductionOn with
  | h representative =>
    by_cases nonzero : (representative⁻¹).val 2 0 ≠ 0
    · exact Or.inl ⟨_, openFlag_of_corner_ne_zero representative nonzero⟩
    · exact Or.inr (closed_representative representative (not_ne_iff.mp nonzero))

theorem closedFlag_representative (flag : Flags .plane)
    (closed : flag ∉ Set.range openFlag) :
    ∃ binary : BinaryRationalGL, flag = QuotientGroup.mk (lineLevi 1 binary) := by
  rcases flag_dichotomy flag with ⟨coordinates, equality⟩ | representative
  · exact False.elim (closed ⟨coordinates, equality.symm⟩)
  · exact representative

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BruhatCells
