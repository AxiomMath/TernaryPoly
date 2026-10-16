module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliers
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedHeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Norms

@[expose] public section


/-!
# The plane height `Ξ`: algebraic part of `HeightLaw`

`logXi y = (1/3) log |det y|_𝔸 - log ‖e₃ y‖_𝔸`, where `‖e₃ y‖_𝔸` is the adelic norm of the last-row
scalar `u` in any decomposition `y = n(a, b) · planeLevi(B, u) · k`, `k` in the maximal compact.
That the norm `|u|_𝔸` does not depend on the decomposition is `corner_norm_unique`: the corner
unit of an element of `P ∩ K` has adelic norm `1` (real part: an orthogonal matrix with last row
`(0, 0, w)` has `w² = 1`; finite part: `w` and `w⁻¹` are integral).

From the decomposition formula `logXi (n planeLevi(B, u) k) = (1/3) log |det B| - (2/3) log |u|` we
derive the left transformation law under the radical and the Levi, right invariance under the
maximal compact, and `logXi 1 = 0`. Real smoothness is in `SectionMultipliersXiSmooth`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXi

theorem planeUnipotent_mem {R : Type} [CommRing R] (first second : R) :
    planeUnipotent first second ∈ planeParabolic R := ⟨rfl, rfl⟩

theorem planeUnipotent_zero {R : Type} [CommRing R] : planeUnipotent (0 : R) 0 = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem planeLevi_mul {R : Type} [CommRing R] (first second : GeneralLinearGroup (Fin 2) R)
    (firstUnit secondUnit : Rˣ) :
    planeLevi (first * second) (firstUnit * secondUnit) =
      planeLevi first firstUnit * planeLevi second secondUnit :=
  Units.ext (planeBlock_mul first.val second.val firstUnit.val secondUnit.val)

/-- Conjugating the radical by a Levi element rescales its coordinates. -/
theorem planeLevi_mul_planeUnipotent {R : Type} [CommRing R]
    (binary : GeneralLinearGroup (Fin 2) R) (unit : Rˣ) (first second : R) :
    planeLevi binary unit * planeUnipotent first second =
      planeUnipotent (unit.inv * (binary.val 0 0 * first + binary.val 0 1 * second))
          (unit.inv * (binary.val 1 0 * first + binary.val 1 1 * second)) *
        planeLevi binary unit := by
  have corner : unit.inv * unit.val = 1 := unit.inv_val
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination (binary.val 0 0 * first + binary.val 0 1 * second) * corner
    | linear_combination (-(binary.val 0 0 * first + binary.val 0 1 * second)) * corner
    | linear_combination (binary.val 1 0 * first + binary.val 1 1 * second) * corner
    | linear_combination (-(binary.val 1 0 * first + binary.val 1 1 * second)) * corner

/-! ### The corner unit of `P ∩ K` has norm one -/

theorem compact_inv (element : AdelicGL) (compact : inMaximalCompact element) :
    inMaximalCompact element⁻¹ := by
  refine ⟨?_, ?_⟩
  · have inverse : (realGroup element⁻¹).val = (realGroup element).val.transpose := by
      rw [map_inv]
      exact MaximalCompact.orthogonal_inverse (realGroup element) compact.1
    rw [inverse, Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp compact.1
  · obtain ⟨integral, equality⟩ := compact.2
    exact ⟨integral⁻¹, by rw [map_inv, map_inv, equality]⟩

theorem corner_norm_one_of_compact (element : AdelicGL)
    (membership : element ∈ planeParabolic Adeles) (compact : inMaximalCompact element) :
    adeleNorm (ParabolicDecomposition.planeRankOneUnit element membership) = 1 := by
  -- real part: the last row of an orthogonal matrix is a unit vector
  have realSquare : (element.val 2 2).1 * (element.val 2 2).1 = 1 := by
    have orthogonal : (realGroup element).val * (realGroup element).val.transpose = 1 :=
      mul_eq_one_comm.mp compact.1
    have entry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2) orthogonal
    have zeroFirst : (element.val 2 0).1 = 0 := by simp [membership.1]
    have zeroSecond : (element.val 2 1).1 = 0 := by simp [membership.2]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
      Fin.sum_univ_three] at entry
    change (element.val 2 0).1 * (element.val 2 0).1 + (element.val 2 1).1 * (element.val 2 1).1 +
      (element.val 2 2).1 * (element.val 2 2).1 = 1 at entry
    simpa [zeroFirst, zeroSecond] using entry
  -- finite part: the corner is integral
  obtain ⟨integral, integralEquality⟩ := compact.2
  have finiteEntry : ∀ row column, integralEmbedding (integral.val row column) =
      (element.val row column).2 := by
    intro row column
    exact congrArg (fun matrix : GL3 FiniteAdeles => matrix.val row column) integralEquality
  have injective := integralEmbedding_isOpenEmbedding.toIsEmbedding.injective
  have integralZeroFirst : integral.val 2 0 = 0 := by
    have entry := finiteEntry 2 0
    rw [membership.1] at entry
    exact injective (entry.trans (by simp))
  have integralZeroSecond : integral.val 2 1 = 0 := by
    have entry := finiteEntry 2 1
    rw [membership.2] at entry
    exact injective (entry.trans (by simp))
  have integralMembership : integral ∈ planeParabolic IntegralAdeles :=
    ⟨integralZeroFirst, integralZeroSecond⟩
  have unitEquality : Units.map (RingHom.snd ℝ FiniteAdeles)
      (ParabolicDecomposition.planeRankOneUnit element membership) =
        Units.map integralEmbedding.toMonoidHom
          (ParabolicDecomposition.planeRankOneUnit integral integralMembership) := by
    apply Units.ext
    exact (finiteEntry 2 2).symm
  rw [InducedHeight.unit_split _ _ unitEquality, map_mul, Norms.integralUnit_norm, mul_one]
  apply NNReal.coe_injective
  rw [Norms.realUnit_norm]
  have squareOne : ((Units.map (RingHom.fst ℝ FiniteAdeles : Adeles →* ℝ)
      (ParabolicDecomposition.planeRankOneUnit element membership)).val) *
      ((Units.map (RingHom.fst ℝ FiniteAdeles : Adeles →* ℝ)
        (ParabolicDecomposition.planeRankOneUnit element membership)).val) = (1 : ℝ) :=
    realSquare
  rcases mul_self_eq_one_iff.mp squareOne with positive | negative
  · rw [positive]; simp
  · rw [negative]; simp

theorem rankOne_mul_value (first second : AdelicGL) (firstMembership : first ∈ planeParabolic Adeles) :
    (first * second).val 2 2 = first.val 2 2 * second.val 2 2 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, firstMembership.1, firstMembership.2]

theorem corner_norm_unique {firstA firstB secondA secondB : Adeles}
    {firstBinary secondBinary : BinaryAdelicGL} {firstUnit secondUnit : Adelesˣ}
    {firstCompact secondCompact : AdelicGL}
    (firstMembership : inMaximalCompact firstCompact)
    (secondMembership : inMaximalCompact secondCompact)
    (equal : planeUnipotent firstA firstB * planeLevi firstBinary firstUnit * firstCompact =
      planeUnipotent secondA secondB * planeLevi secondBinary secondUnit * secondCompact) :
    adeleNorm firstUnit = adeleNorm secondUnit := by
  set firstParabolic := planeUnipotent firstA firstB * planeLevi firstBinary firstUnit with hFirst
  set secondParabolic := planeUnipotent secondA secondB * planeLevi secondBinary secondUnit
    with hSecond
  have firstIn : firstParabolic ∈ planeParabolic Adeles :=
    (planeParabolic Adeles).mul_mem (planeUnipotent_mem _ _) (planeLevi_mem _ _)
  have secondIn : secondParabolic ∈ planeParabolic Adeles :=
    (planeParabolic Adeles).mul_mem (planeUnipotent_mem _ _) (planeLevi_mem _ _)
  have quotient : secondParabolic⁻¹ * firstParabolic = secondCompact * firstCompact⁻¹ := by
    have expand : firstParabolic = secondParabolic * secondCompact * firstCompact⁻¹ := by
      rw [← equal]
      simp
    rw [expand]
    simp [mul_assoc]
  have quotientIn : secondParabolic⁻¹ * firstParabolic ∈ planeParabolic Adeles :=
    (planeParabolic Adeles).mul_mem ((planeParabolic Adeles).inv_mem secondIn) firstIn
  have quotientCompact : inMaximalCompact (secondParabolic⁻¹ * firstParabolic) := by
    rw [quotient]
    exact RealTranslations.compact_mul _ _ secondMembership (compact_inv _ firstMembership)
  have quotientNorm := corner_norm_one_of_compact _ quotientIn quotientCompact
  have firstCorner : firstUnit.val = firstParabolic.val 2 2 := by
    simp [hFirst, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have secondCorner : secondUnit.val = secondParabolic.val 2 2 := by
    simp [hSecond, planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have product := rankOne_mul_value secondParabolic (secondParabolic⁻¹ * firstParabolic) secondIn
  rw [mul_inv_cancel_left] at product
  have unitProduct : firstUnit = secondUnit *
      ParabolicDecomposition.planeRankOneUnit _ quotientIn := by
    apply Units.ext
    rw [Units.val_mul, firstCorner, secondCorner, product]
    rfl
  rw [unitProduct, map_mul, quotientNorm, mul_one]

/-! ### The corner norm and `logXi` -/

/-- `v` is the adelic norm of the corner unit of some Iwasawa decomposition of `y`. -/
abbrev IsCornerNorm (y : AdelicGL) (value : ℝ) : Prop :=
  ∃ (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL),
    inMaximalCompact compact ∧
      y = planeUnipotent first second * planeLevi binary unit * compact ∧
      value = (adeleNorm unit : ℝ)

theorem exists_cornerNorm (y : AdelicGL) : ∃ value, IsCornerNorm y value := by
  obtain ⟨first, second, binary, unit, compact, membership, decomposition⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  exact ⟨_, first, second, binary, unit, compact, membership, decomposition, rfl⟩

theorem cornerNorm_unique {y : AdelicGL} {first second : ℝ}
    (firstCorner : IsCornerNorm y first) (secondCorner : IsCornerNorm y second) :
    first = second := by
  obtain ⟨a₁, b₁, B₁, u₁, k₁, hk₁, e₁, rfl⟩ := firstCorner
  obtain ⟨a₂, b₂, B₂, u₂, k₂, hk₂, e₂, rfl⟩ := secondCorner
  rw [corner_norm_unique hk₁ hk₂ (e₁.symm.trans e₂)]

/-- The adelic norm of the last-row scalar `‖e₃ y‖_𝔸` of an adelic element. -/
def cornerNorm (y : AdelicGL) : ℝ := Classical.choose (exists_cornerNorm y)

theorem cornerNorm_spec (y : AdelicGL) : IsCornerNorm y (cornerNorm y) :=
  Classical.choose_spec (exists_cornerNorm y)

theorem cornerNorm_decomposition (first second : Adeles) (binary : BinaryAdelicGL)
    (unit : Adelesˣ) (compact : AdelicGL) (membership : inMaximalCompact compact) :
    cornerNorm (planeUnipotent first second * planeLevi binary unit * compact) =
      (adeleNorm unit : ℝ) :=
  cornerNorm_unique (cornerNorm_spec _) ⟨first, second, binary, unit, compact, membership, rfl, rfl⟩

/-- `log Ξ(y) = (1/3) log |det y| - log ‖e₃ y‖`, with the adelic norms. -/
def logXi (y : AdelicGL) : ℝ :=
  (1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det y) : ℝ) - Real.log (cornerNorm y)

theorem norm_real_pos (unit : Adelesˣ) : (0 : ℝ) < (adeleNorm unit : ℝ) :=
  NNReal.coe_pos.mpr (adeleNorm_pos unit)

theorem logXi_decomposition (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    logXi (planeUnipotent first second * planeLevi binary unit * compact) =
      (1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
        (2 / 3) * Real.log (adeleNorm unit : ℝ) := by
  unfold logXi
  rw [cornerNorm_decomposition first second binary unit compact membership,
    InducedHeight.decomposition_det_norm first second binary unit compact membership,
    NNReal.coe_mul, Real.log_mul (norm_real_pos _).ne' (norm_real_pos _).ne']
  ring

theorem logXi_radical (first second : Adeles) (y : AdelicGL) :
    logXi (planeUnipotent first second * y) = logXi y := by
  obtain ⟨a, b, binary, unit, compact, membership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  have regroup : planeUnipotent first second * (planeUnipotent a b * planeLevi binary unit * compact) =
      planeUnipotent (first + a) (second + b) * planeLevi binary unit * compact := by
    rw [planeUnipotent_add]
    simp only [mul_assoc]
  rw [regroup, logXi_decomposition _ _ _ _ _ membership, logXi_decomposition _ _ _ _ _ membership]

theorem logXi_levi (binary : BinaryAdelicGL) (unit : Adelesˣ) (y : AdelicGL) :
    logXi (planeLevi binary unit * y) = logXi y +
      (1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
        (2 / 3) * Real.log (adeleNorm unit : ℝ) := by
  obtain ⟨a, b, otherBinary, otherUnit, compact, membership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  have regroup : planeLevi binary unit * (planeUnipotent a b * planeLevi otherBinary otherUnit * compact) =
      planeUnipotent (unit.inv * (binary.val 0 0 * a + binary.val 0 1 * b))
          (unit.inv * (binary.val 1 0 * a + binary.val 1 1 * b)) *
        planeLevi (binary * otherBinary) (unit * otherUnit) * compact := by
    have conjugate := planeLevi_mul_planeUnipotent binary unit a b
    calc planeLevi binary unit * (planeUnipotent a b * planeLevi otherBinary otherUnit * compact)
        = (planeLevi binary unit * planeUnipotent a b) * planeLevi otherBinary otherUnit * compact := by
          simp only [mul_assoc]
      _ = (planeUnipotent (unit.inv * (binary.val 0 0 * a + binary.val 0 1 * b))
            (unit.inv * (binary.val 1 0 * a + binary.val 1 1 * b)) * planeLevi binary unit) *
            planeLevi otherBinary otherUnit * compact := by rw [conjugate]
      _ = planeUnipotent (unit.inv * (binary.val 0 0 * a + binary.val 0 1 * b))
            (unit.inv * (binary.val 1 0 * a + binary.val 1 1 * b)) *
            planeLevi (binary * otherBinary) (unit * otherUnit) * compact := by
          rw [planeLevi_mul]
          simp only [mul_assoc]
  rw [regroup, logXi_decomposition _ _ _ _ _ membership, logXi_decomposition _ _ _ _ _ membership]
  simp only [map_mul, NNReal.coe_mul]
  rw [Real.log_mul (norm_real_pos _).ne' (norm_real_pos _).ne',
    Real.log_mul (norm_real_pos _).ne' (norm_real_pos _).ne']
  ring

theorem logXi_rightCompact (y compact : AdelicGL) (membership : inMaximalCompact compact) :
    logXi (y * compact) = logXi y := by
  obtain ⟨a, b, binary, unit, other, otherMembership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  have regroup : planeUnipotent a b * planeLevi binary unit * other * compact =
      planeUnipotent a b * planeLevi binary unit * (other * compact) := mul_assoc _ _ _
  rw [regroup, logXi_decomposition _ _ _ _ _ (RealTranslations.compact_mul _ _ otherMembership membership),
    logXi_decomposition _ _ _ _ _ otherMembership]

theorem one_mem_compact : inMaximalCompact (1 : AdelicGL) := by
  refine ⟨?_, ⟨1, ?_⟩⟩
  · simp
  · simp

theorem logXi_one : logXi 1 = 0 := by
  have decomposition : (1 : AdelicGL) =
      planeUnipotent (0 : Adeles) 0 * planeLevi (1 : BinaryAdelicGL) (1 : Adelesˣ) * 1 := by
    simp [planeUnipotent_zero, ParabolicInvariance.planeLevi_one]
  rw [decomposition, logXi_decomposition _ _ _ _ _ one_mem_compact]
  simp

/-- All of `HeightLaw` except real smoothness. -/
theorem heightLaw_of_smooth
    (smooth : ∀ g : AdelicGL,
      Smooth (fun x : Fin 1 → RealGL3 => logXi (g * atInfinity (x 0)))) :
    HeightLaw logXi where
  radical := logXi_radical
  levi := logXi_levi
  rightCompact := logXi_rightCompact
  one := logXi_one
  smooth := smooth

end TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXi
