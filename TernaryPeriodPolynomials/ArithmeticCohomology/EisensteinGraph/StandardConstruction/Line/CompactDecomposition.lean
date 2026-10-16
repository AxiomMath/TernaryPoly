module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MaximalCompact

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactDecomposition

variable {R : Type} [CommRing R]

/-- Transpose with both coordinates reversed. -/
def reverseTranspose (matrix : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun row column => matrix column.rev row.rev

theorem reverseTranspose_mul (first second : Matrix (Fin 3) (Fin 3) R) :
    reverseTranspose (first * second) = reverseTranspose second * reverseTranspose first := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [reverseTranspose, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem reverseTranspose_one : reverseTranspose (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext row column
  simp [reverseTranspose, Matrix.one_apply, eq_comm]

omit [CommRing R] in
theorem reverseTranspose_involutive (matrix : Matrix (Fin 3) (Fin 3) R) :
    reverseTranspose (reverseTranspose matrix) = matrix := by
  ext row column
  simp [reverseTranspose]

omit [CommRing R] in
theorem reverseTranspose_transpose (matrix : Matrix (Fin 3) (Fin 3) R) :
    reverseTranspose matrix.transpose = (reverseTranspose matrix).transpose := rfl

/-- The contragredient automorphism followed by reversal of the three coordinates. -/
def dual (element : GL3 R) : GL3 R where
  val := reverseTranspose element.inv
  inv := reverseTranspose element.val
  val_inv := by rw [← reverseTranspose_mul, element.val_inv, reverseTranspose_one]
  inv_val := by rw [← reverseTranspose_mul, element.inv_val, reverseTranspose_one]

theorem dual_involutive (element : GL3 R) : dual (dual element) = element := by
  apply Units.ext
  exact reverseTranspose_involutive element.val

theorem dual_mul (first second : GL3 R) : dual (first * second) = dual first * dual second := by
  apply Units.ext
  change reverseTranspose (second.inv * first.inv) = _
  exact reverseTranspose_mul second.inv first.inv

theorem dual_map {S : Type} [CommRing S] (hom : R →+* S) (element : GL3 R) :
    dual (GeneralLinearGroup.map hom element) = GeneralLinearGroup.map hom (dual element) := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem dual_plane (element : GL3 R) (membership : element ∈ planeParabolic R) :
    dual element ∈ lineParabolic R := by
  have inverseMembership := (planeParabolic R).inv_mem membership
  exact ⟨inverseMembership.2, inverseMembership.1⟩

theorem dual_orthogonal (element : RealGL3)
    (orthogonal : element.val.transpose * element.val = 1) :
    (dual element).val.transpose * (dual element).val = 1 := by
  change (reverseTranspose element.inv).transpose * reverseTranspose element.inv = 1
  rw [← reverseTranspose_transpose, ← reverseTranspose_mul,
    MaximalCompact.orthogonal_inverse element orthogonal, Matrix.transpose_transpose,
    orthogonal, reverseTranspose_one]

theorem dual_compact (element : AdelicGL) (compact : inMaximalCompact element) :
    inMaximalCompact (dual element) := by
  have realMap : realGroup (dual element) = dual (realGroup element) :=
    (dual_map (RingHom.fst ℝ FiniteAdeles) element).symm
  have finiteMap : finiteGroup (dual element) = dual (finiteGroup element) :=
    (dual_map (RingHom.snd ℝ FiniteAdeles) element).symm
  refine ⟨?_, ?_⟩
  · rw [realMap]
    exact dual_orthogonal (realGroup element) compact.1
  · obtain ⟨integral, equality⟩ := compact.2
    refine ⟨dual integral, ?_⟩
    rw [finiteMap, ← equality, dual_map]

theorem adelic_lineCompact (element : AdelicGL) :
    ∃ parabolic compact : AdelicGL, parabolic ∈ lineParabolic Adeles ∧
      inMaximalCompact compact ∧ element = parabolic * compact := by
  obtain ⟨parabolic, compact, membership, compactMembership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeCompact (dual element)
  refine ⟨dual parabolic, dual compact, dual_plane parabolic membership,
    dual_compact compact compactMembership, ?_⟩
  have equality := congrArg dual decomposition
  rw [dual_involutive, dual_mul] at equality
  exact equality

def lineBinaryBlock (element : GL3 R) : Matrix (Fin 2) (Fin 2) R :=
  !![element.val 1 1, element.val 1 2; element.val 2 1, element.val 2 2]

theorem lineBinaryBlock_mul_inv (element : GL3 R) (membership : element ∈ lineParabolic R) :
    lineBinaryBlock element * lineBinaryBlock element⁻¹ = 1 := by
  ext row column
  have equation := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R =>
    matrix row.succ column.succ) element.mul_inv
  fin_cases row <;> fin_cases column <;>
    simpa [lineBinaryBlock, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      membership.1, membership.2] using equation

def lineBinaryUnit (element : GL3 R) (membership : element ∈ lineParabolic R) :
    GeneralLinearGroup (Fin 2) R where
  val := lineBinaryBlock element
  inv := lineBinaryBlock element⁻¹
  val_inv := lineBinaryBlock_mul_inv element membership
  inv_val := by
    simpa only [inv_inv] using
      lineBinaryBlock_mul_inv element⁻¹ ((lineParabolic R).inv_mem membership)

def lineRankOneUnit (element : GL3 R) (membership : element ∈ lineParabolic R) : Rˣ where
  val := element.val 0 0
  inv := element.inv 0 0
  val_inv := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, membership.1, membership.2, mul_comm] using
      congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 0 0) element.inv_mul
  inv_val := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, membership.1, membership.2] using
      congrArg (fun matrix : Matrix (Fin 3) (Fin 3) R => matrix 0 0) element.inv_mul

theorem line_decomposition (element : GL3 R) (membership : element ∈ lineParabolic R) :
    element = lineLevi (lineRankOneUnit element membership) (lineBinaryUnit element membership) *
      lineUnipotent ((lineRankOneUnit element membership).inv * element.val 0 1)
        ((lineRankOneUnit element membership).inv * element.val 0 2) := by
  have corner : element.val 0 0 * (element.val)⁻¹ 0 0 = 1 := by
    simpa [lineRankOneUnit] using (lineRankOneUnit element membership).val_inv
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi_val, lineUnipotent, upperUnipotent, lineBinaryUnit, lineBinaryBlock,
      lineRankOneUnit, Matrix.mul_apply, Fin.sum_univ_three, membership.1, membership.2,
      ← mul_assoc, corner]

theorem adelic_lineDecomposition (element : AdelicGL) :
    ∃ unit : Adelesˣ, ∃ binary : BinaryAdelicGL, ∃ first second : Adeles,
      ∃ compact : AdelicGL, inMaximalCompact compact ∧
        element = lineLevi unit binary * lineUnipotent first second * compact := by
  obtain ⟨parabolic, compact, membership, compactMembership, decomposition⟩ :=
    adelic_lineCompact element
  exact ⟨_, _, _, _, compact, compactMembership,
    decomposition.trans (congrArg (fun value => value * compact) (line_decomposition parabolic membership))⟩

theorem lineUnipotent_inverse (first second : R) :
    (lineUnipotent first second)⁻¹ = lineUnipotent (-first) (-second) := by
  apply Units.ext
  rfl

theorem lineLevi_inverse (unit : Rˣ) (binary : GeneralLinearGroup (Fin 2) R) :
    (lineLevi unit binary)⁻¹ = lineLevi unit⁻¹ binary⁻¹ :=
  ((lineLeviHom R).map_inv (unit, binary)).symm

theorem adelic_radical_lineCompact (element : AdelicGL) :
    ∃ first second : Adeles, ∃ unit : Adelesˣ, ∃ binary : BinaryAdelicGL,
      ∃ compact : AdelicGL, inMaximalCompact compact ∧
        element = lineUnipotent first second * lineLevi unit binary * compact := by
  obtain ⟨parabolic, compact, membership, compactMembership, decomposition⟩ :=
    adelic_lineCompact element
  have inverseDecomposition := line_decomposition parabolic⁻¹ ((lineParabolic Adeles).inv_mem membership)
  have direct := congrArg Inv.inv inverseDecomposition
  rw [inv_inv, _root_.mul_inv_rev, lineUnipotent_inverse, lineLevi_inverse] at direct
  exact ⟨_, _, _, _, compact, compactMembership,
    decomposition.trans (congrArg (fun value => value * compact) direct)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactDecomposition
