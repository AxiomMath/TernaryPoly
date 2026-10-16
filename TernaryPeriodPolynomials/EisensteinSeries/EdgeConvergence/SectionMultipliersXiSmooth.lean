module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXi
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealDecomposition

@[expose] public section


/-!
# Real smoothness of `log Ξ`, and the `HeightLaw` instance

For `X ∈ GL₃(ℝ)` with `X = n(a, b) · planeLevi(B, t) · κ`, `κ` orthogonal (real Iwasawa),
`log Ξ (atInfinity X) = (1/3) log |det X| - (1/2) log (Σ_j X₂ⱼ²)` (`logXi_atInfinity`): the second
term is `log ‖e₃ X‖` since `X₂ⱼ = t κ₂ⱼ` and `κ` has unit rows. For a general adelic `g`, translating
by `atInfinity X` only changes this to `X ↦ κ_g X` up to an additive constant (`logXi_translate`),
so `x ↦ log Ξ (g · atInfinity (x 0))` is smooth (`logXi_smooth`). Hence `logXi` satisfies
`SectionMultipliers.HeightLaw` (`heightLaw`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXi

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXiSmooth

theorem atInfinity_planeLevi (binary : BinaryRealGL) (scalar : ℝˣ) :
    atInfinity (planeLevi binary scalar) =
      planeLevi (atInfinity binary) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeLevi, planeBlock, realAdeleUnit]

theorem atInfinity_planeUnipotent (first second : ℝ) :
    atInfinity (planeUnipotent first second) = planeUnipotent (first, 0) (second, 0) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, planeUnipotent]

theorem planeUnipotent_det_real (first second : ℝ) : (planeUnipotent first second).val.det = 1 := by
  simp [planeUnipotent, Matrix.det_fin_three]

theorem planeLevi_det_real (binary : BinaryRealGL) (scalar : ℝˣ) :
    (planeLevi binary scalar).val.det = binary.val.det * scalar.val := by
  change (planeBlock binary.val scalar.val).det = _
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem atFinite_compact_of_range (finite : FiniteGL)
    (membership : finite ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    inMaximalCompact (atFinite finite) := by
  constructor
  · rw [InducedContinuity.realGroup_atFinite]
    simp
  · rw [InducedContinuity.finiteGroup_atFinite]
    exact membership

theorem logXi_atInfinity (X : RealGL3) :
    logXi (atInfinity X) =
      (1 / 3) * Real.log |X.val.det| - (1 / 2) * Real.log (∑ j : Fin 3, (X.val 2 j) ^ 2) := by
  obtain ⟨parabolic, compact, membership, orthogonal, decomposition⟩ :=
    RealDecomposition.real_planeCompact X
  obtain ⟨a, b, binary, scalar, parabolicEquality⟩ :=
    ParabolicDecomposition.plane_decomposition_exists parabolic membership
  have equality : X = planeUnipotent a b * planeLevi binary scalar * compact := by
    rw [decomposition, parabolicEquality]
  have adelic : atInfinity X = planeUnipotent (a, 0) (b, 0) *
      planeLevi (atInfinity binary) (realAdeleUnit scalar) * atInfinity compact := by
    rw [equality, RealTranslations.atInfinity_mul, RealTranslations.atInfinity_mul,
      atInfinity_planeUnipotent, atInfinity_planeLevi]
  -- determinant and last row of `X`
  have compactDet : |compact.val.det| = 1 := by
    have square : compact.val.det * compact.val.det = 1 := by
      simpa [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det orthogonal
    rcases mul_self_eq_one_iff.mp square with positive | negative
    · simp [positive]
    · simp [negative]
  have detX : |X.val.det| = |binary.val.det| * |scalar.val| := by
    rw [equality]
    simp [Units.val_mul, Matrix.det_mul, planeUnipotent_det_real, planeLevi_det_real, abs_mul,
      compactDet]
  have unitRows : ∑ j : Fin 3, (compact.val 2 j) ^ 2 = 1 := by
    have entry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2)
      (mul_eq_one_comm.mp orthogonal)
    simpa [Matrix.mul_apply, Fin.sum_univ_three, sq] using entry
  have rowZero : (planeUnipotent a b * planeLevi binary scalar).val 2 0 = 0 := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have rowOne : (planeUnipotent a b * planeLevi binary scalar).val 2 1 = 0 := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have rowTwo : (planeUnipotent a b * planeLevi binary scalar).val 2 2 = scalar.val := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have lastRow : ∀ j, X.val 2 j = scalar.val * compact.val 2 j := by
    intro j
    rw [equality, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, rowZero, rowOne, rowTwo]
    ring
  have rowSum : ∑ j : Fin 3, (X.val 2 j) ^ 2 = |scalar.val| ^ 2 := by
    simp only [lastRow, mul_pow, ← Finset.mul_sum, unitRows, mul_one, sq_abs]
  rw [adelic, logXi_decomposition _ _ _ _ _ (RealTranslations.compact_atInfinity compact orthogonal),
    SmoothNormPower.det_atInfinity, Norms.realUnit_norm, Norms.realUnit_norm, detX, rowSum]
  have binaryNonzero : |binary.val.det| ≠ 0 :=
    abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero binary)
  have scalarNonzero : |scalar.val| ≠ 0 := abs_ne_zero.mpr scalar.ne_zero
  rw [Real.log_mul binaryNonzero scalarNonzero, Real.log_pow]
  change (1 / 3) * Real.log |binary.val.det| - (2 / 3) * Real.log |scalar.val| = _
  push_cast
  ring

/-- Translating by a real element changes `log Ξ` only through the real part of the compact factor. -/
theorem logXi_translate (g : AdelicGL) :
    ∃ (constant : ℝ) (rotation : RealGL3), ∀ X : RealGL3,
      logXi (g * atInfinity X) = logXi (atInfinity (rotation * X)) + constant := by
  obtain ⟨a, b, binary, unit, compact, membership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition g
  refine ⟨(1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
    (2 / 3) * Real.log (adeleNorm unit : ℝ), realGroup compact, ?_⟩
  intro X
  have split : compact = atInfinity (realGroup compact) * atFinite (finiteGroup compact) := by
    apply InducedContinuity.adelic_ext
    · simp only [map_mul, InducedContinuity.realGroup_atInfinity,
        InducedContinuity.realGroup_atFinite, mul_one]
    · simp only [map_mul, InducedContinuity.finiteGroup_atInfinity,
        InducedContinuity.finiteGroup_atFinite, one_mul]
  have finiteCompact : inMaximalCompact (atFinite (finiteGroup compact)) :=
    atFinite_compact_of_range _ membership.2
  have key : compact * atInfinity X =
      atInfinity (realGroup compact * X) * atFinite (finiteGroup compact) := by
    calc compact * atInfinity X
        = (atInfinity (realGroup compact) * atFinite (finiteGroup compact)) * atInfinity X := by
          rw [← split]
      _ = atInfinity (realGroup compact) * (atFinite (finiteGroup compact) * atInfinity X) :=
          mul_assoc _ _ _
      _ = atInfinity (realGroup compact) * (atInfinity X * atFinite (finiteGroup compact)) := by
          rw [RealTranslations.atFinite_atInfinity_commute]
      _ = atInfinity (realGroup compact * X) * atFinite (finiteGroup compact) := by
          rw [RealTranslations.atInfinity_mul, mul_assoc]
  have regroup : planeUnipotent a b * planeLevi binary unit * compact * atInfinity X =
      planeUnipotent a b * (planeLevi binary unit *
        (atInfinity (realGroup compact * X) * atFinite (finiteGroup compact))) := by
    calc planeUnipotent a b * planeLevi binary unit * compact * atInfinity X
        = planeUnipotent a b * planeLevi binary unit * (compact * atInfinity X) := mul_assoc _ _ _
      _ = planeUnipotent a b * planeLevi binary unit *
            (atInfinity (realGroup compact * X) * atFinite (finiteGroup compact)) := by rw [key]
      _ = _ := mul_assoc _ _ _
  rw [regroup, logXi_radical, logXi_levi, logXi_rightCompact _ _ finiteCompact]
  ring

theorem invertibleMatrix_val {size : ℕ} (matrix : Matrix (Fin size) (Fin size) ℝ)
    (nonzero : matrix.det ≠ 0) : (invertibleMatrix matrix).val = matrix := by
  unfold invertibleMatrix
  rw [dite_eq_left nonzero]
  rfl

theorem logXi_smooth (g : AdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 => logXi (g * atInfinity (x 0))) := by
  obtain ⟨constant, rotation, translate⟩ := logXi_translate g
  have rewrite : (fun x : Fin 1 → RealGL3 => logXi (g * atInfinity (x 0))) = fun x =>
      ((1 / 3) * Real.log |(rotation * x 0).val.det| -
        (1 / 2) * Real.log (∑ j : Fin 3, ((rotation * x 0).val 2 j) ^ 2)) + constant := by
    funext x
    rw [translate, logXi_atInfinity]
  rw [rewrite]
  unfold Smooth
  have rotationDet : rotation.val.det ≠ 0 := GeneralLinearGroup.det_ne_zero rotation
  have domainDet : ∀ matrices ∈ SmoothJets.domain 3 1, (matrices 0).det ≠ 0 :=
    fun matrices membership => membership 0
  have rowSmooth : ContDiff ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
      ∑ j : Fin 3, (∑ i : Fin 3, rotation.val 2 i * matrices 0 i j) ^ 2) := by
    have entry : ∀ i j : Fin 3, ContDiff ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
        matrices 0 i j) := fun i j =>
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ 0))
    fun_prop
  have rowNonzero : ∀ matrices ∈ SmoothJets.domain 3 1,
      ∑ j : Fin 3, (∑ i : Fin 3, rotation.val 2 i * matrices 0 i j) ^ 2 ≠ 0 := by
    intro matrices membership zero
    have terms := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp zero
    have rowZero : ∀ j, (rotation.val * matrices 0) 2 j = 0 := by
      intro j
      have term := terms j (Finset.mem_univ j)
      rw [pow_eq_zero_iff (by norm_num)] at term
      simpa [Matrix.mul_apply] using term
    have detZero : (rotation.val * matrices 0).det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 rowZero
    rw [Matrix.det_mul] at detZero
    exact mul_ne_zero rotationDet (domainDet matrices membership) detZero
  have logDet : ContDiffOn ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
      Real.log (rotation.val.det * (matrices 0).det)) (SmoothJets.domain 3 1) :=
    (contDiff_const.mul (SmoothNormPower.determinant_smooth (size := 3) (arity := 1) 0)).contDiffOn.log
      (fun matrices membership => mul_ne_zero rotationDet (domainDet matrices membership))
  have logRow : ContDiffOn ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
      Real.log (∑ j : Fin 3, (∑ i : Fin 3, rotation.val 2 i * matrices 0 i j) ^ 2))
      (SmoothJets.domain 3 1) :=
    rowSmooth.contDiffOn.log rowNonzero
  have combined : ContDiffOn ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples 3 1 =>
      ((1 / 3) * Real.log (rotation.val.det * (matrices 0).det) -
        (1 / 2) * Real.log (∑ j : Fin 3, (∑ i : Fin 3, rotation.val 2 i * matrices 0 i j) ^ 2)) +
          constant) (SmoothJets.domain 3 1) :=
    (((contDiffOn_const.mul logDet).sub (contDiffOn_const.mul logRow)).add contDiffOn_const)
  apply combined.congr
  intro matrices membership
  have nonzero : (matrices 0).det ≠ 0 := domainDet matrices membership
  have valueEquality : (invertibleMatrix (matrices 0)).val = matrices 0 :=
    invertibleMatrix_val _ nonzero
  dsimp only
  simp only [Units.val_mul, valueEquality, Matrix.det_mul, Real.log_abs, Matrix.mul_apply]

/-- The plane height `Ξ`: `log Ξ` satisfies the `HeightLaw`. -/
theorem heightLaw : HeightLaw logXi := heightLaw_of_smooth logXi_smooth

end TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXiSmooth
