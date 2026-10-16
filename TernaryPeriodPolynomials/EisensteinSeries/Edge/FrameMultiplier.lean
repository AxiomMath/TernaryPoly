module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXiSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameProfile
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Transport

@[expose] public section


/-!
# The height multiplier read off the archimedean frame

The Godement machinery of `PlaneEisensteinContinuation` works with the frame
`point⁻¹ · standard ∈ Rectangular 𝔸` of an adelic point and its real coordinates
`RectangularTransport.archimedean`; the edge-convergence multiplier
`ρ_h(y)^z = (Ξ(y h) / Ξ(y))^z` (`SectionMultipliers.heightMultiplier`) is stated through the
plane height `Ξ`. This file identifies the two.

For a real matrix `h`, `frameLog h v = (1/3) log |det h| + (1/2) log ‖e‖² - (1/2) log ‖hᵀ e‖²`,
where `e` is the exterior (cross) product of the two columns of the real frame with coordinates
`v`. It is homogeneous of degree `0` in `e`, smooth on the open set of full rank frames
(`fullRank_isOpen`, `frameLog_contDiffOn`), and, evaluated on the archimedean coordinates of
`frame y · b` (always of full rank, `frame_fullRank`), it equals
`log Ξ(y h) - log Ξ(y)` (`heightMultiplier_eq_frameLog`). The convention of the statement is
`(hᵀ e)_j = ∑ i, e i * h i j`, with `e` proportional to the last row of the real part of `y`:
no change of convention was needed.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXi
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersXiSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
  (Rectangular columns exterior FullRank)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
  (coordinateEquiv archimedean)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz (RealSpace)

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.FrameMultiplier

/-- `log (Ξ(y h)/Ξ(y))` read off the real frame: with `e` the exterior (cross) product of the two
columns of the frame, `(1/3) log |det h| + (1/2) log ‖e‖² - (1/2) log ‖hᵀ e‖²`. -/
def frameLog (real : RealGL3) (value : RealSpace) : ℝ :=
  let e := exterior (coordinateEquiv.symm value)
  (1 / 3) * Real.log |real.val.det| + (1 / 2) * Real.log (∑ i, e i ^ 2) -
    (1 / 2) * Real.log (∑ j, (∑ i, e i * real.val i j) ^ 2)

/-- The same expression for a vector `e` in place of the exterior product of a frame. -/
def dvec (real : RealGL3) (e : Fin 3 → ℝ) : ℝ :=
  (1 / 3) * Real.log |real.val.det| + (1 / 2) * Real.log (∑ i, e i ^ 2) -
    (1 / 2) * Real.log (∑ j, (∑ i, e i * real.val i j) ^ 2)

theorem frameLog_eq_dvec (real : RealGL3) (value : RealSpace) :
    frameLog real value = dvec real (exterior (coordinateEquiv.symm value)) := rfl

/-! ### Elementary lemmas on `dvec` -/

theorem sumSq_pos {w : Fin 3 → ℝ} (hw : w ≠ 0) : 0 < ∑ i, w i ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (w i)) fun hzero => hw ?_
  funext i
  have term := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp hzero.symm i
    (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).mp term

theorem vecMul_ne_zero (h : RealGL3) {e : Fin 3 → ℝ} (he : e ≠ 0) :
    (fun j => ∑ i, e i * h.val i j) ≠ 0 := by
  intro hzero
  apply he
  have back : Matrix.vecMul (Matrix.vecMul e h.val) (h⁻¹).val = e := by
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have vanish : Matrix.vecMul e h.val = 0 := hzero
  rw [vanish, Matrix.zero_vecMul] at back
  exact back.symm

theorem row_ne_zero (A : RealGL3) : (fun j => A.val 2 j) ≠ 0 := by
  intro hzero
  exact GeneralLinearGroup.det_ne_zero A
    (Matrix.det_eq_zero_of_row_eq_zero 2 fun j => congrFun hzero j)

theorem dvec_smul (h : RealGL3) {e : Fin 3 → ℝ} (he : e ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    dvec h (fun i => c * e i) = dvec h e := by
  have first : ∑ i, (c * e i) ^ 2 = c ^ 2 * ∑ i, e i ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum]
  have inner : ∀ j, ∑ i, c * e i * h.val i j = c * ∑ i, e i * h.val i j := by
    intro j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  have second : ∑ j, (∑ i, c * e i * h.val i j) ^ 2 =
      c ^ 2 * ∑ j, (∑ i, e i * h.val i j) ^ 2 := by
    simp only [inner, mul_pow, ← Finset.mul_sum]
  have positive : 0 < ∑ i, e i ^ 2 := sumSq_pos he
  have positive' : 0 < ∑ j, (∑ i, e i * h.val i j) ^ 2 :=
    sumSq_pos (w := fun j => ∑ i, e i * h.val i j) (vecMul_ne_zero h he)
  have c2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  show (1 / 3) * Real.log |h.val.det| + (1 / 2) * Real.log (∑ i, (c * e i) ^ 2) -
      (1 / 2) * Real.log (∑ j, (∑ i, c * e i * h.val i j) ^ 2) = dvec h e
  rw [first, second, Real.log_mul c2 positive.ne', Real.log_mul c2 positive'.ne']
  simp only [dvec]
  ring

/-! ### The exterior product of a real frame -/

theorem fin3_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem exterior_zero {R : Type*} [CommRing R] (F : Rectangular R) :
    exterior F 0 = F 1 0 * F 2 1 - F 2 0 * F 1 1 := rfl

theorem exterior_one {R : Type*} [CommRing R] (F : Rectangular R) :
    exterior F 1 = F 2 0 * F 0 1 - F 0 0 * F 2 1 := rfl

theorem exterior_two {R : Type*} [CommRing R] (F : Rectangular R) :
    exterior F 2 = F 0 0 * F 1 1 - F 1 0 * F 0 1 := rfl

theorem exterior_mul_apply (X : Rectangular ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 3) :
    exterior (X * B) i = B.det * exterior X i := by
  refine fin3_forall (P := fun j => exterior (X * B) j = B.det * exterior X j) ?_ ?_ ?_ i
  · rw [exterior_zero, exterior_zero]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  · rw [exterior_one, exterior_one]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  · rw [exterior_two, exterior_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring

theorem exterior_columns_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    exterior (columns M) i = M.adjugate 2 i := by
  refine fin3_forall (P := fun j => exterior (columns M) j = M.adjugate 2 j) ?_ ?_ ?_ i
  · rw [exterior_zero, Matrix.adjugate_fin_three]
    show M 1 0 * M 2 1 - M 2 0 * M 1 1 = M 1 0 * M 2 1 - M 1 1 * M 2 0
    ring
  · rw [exterior_one, Matrix.adjugate_fin_three]
    show M 2 0 * M 0 1 - M 0 0 * M 2 1 = -(M 0 0 * M 2 1) + M 0 1 * M 2 0
    ring
  · rw [exterior_two, Matrix.adjugate_fin_three]
    show M 0 0 * M 1 1 - M 1 0 * M 0 1 = M 0 0 * M 1 1 - M 0 1 * M 1 0
    ring

theorem exterior_frame_apply (Y : RealGL3) (B : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 3) :
    exterior (columns (Y⁻¹).val * B) i = (B.det * (Y⁻¹).val.det) * Y.val 2 i := by
  have adj : (Y⁻¹).val.adjugate = (Y⁻¹).val.det • Y.val := by
    calc (Y⁻¹).val.adjugate = (Y⁻¹).val.adjugate * 1 := (Matrix.mul_one _).symm
      _ = (Y⁻¹).val.adjugate * ((Y⁻¹).val * Y.val) := by rw [Units.inv_mul]
      _ = ((Y⁻¹).val.adjugate * (Y⁻¹).val) * Y.val := (Matrix.mul_assoc _ _ _).symm
      _ = (Y⁻¹).val.det • Y.val := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [exterior_mul_apply, exterior_columns_apply, adj, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### The real part of the frame of an adelic point -/

theorem symm_archimedean (y : AdelicGL) (binary : BinaryAdelicGL) :
    coordinateEquiv.symm (archimedean
        (PlaneEisensteinContinuation.FrameProfile.frame y * binary.val)) =
      columns ((realGroup y)⁻¹).val * binary.val.map (RingHom.fst ℝ FiniteAdeles) := by
  have standardMul : (y⁻¹).val.map (RingHom.fst ℝ FiniteAdeles) *
      (PlaneEisensteinContinuation.RectangularKernel.standard : Rectangular ℝ) =
        columns ((realGroup y)⁻¹).val :=
    PlaneEisensteinContinuation.RectangularFrames.mul_standard _
  unfold archimedean
  rw [LinearEquiv.symm_apply_apply]
  unfold PlaneEisensteinContinuation.FrameProfile.frame
  rw [Matrix.map_mul, Matrix.map_mul, PlaneEisensteinContinuation.RectangularKernel.standard_map,
    standardMul]

theorem exists_exterior_frame (y : AdelicGL) (binary : BinaryAdelicGL) :
    ∃ c : ℝ, c ≠ 0 ∧ exterior (coordinateEquiv.symm (archimedean
        (PlaneEisensteinContinuation.FrameProfile.frame y * binary.val))) =
      fun i => c * (realGroup y).val 2 i := by
  have binaryDet : (binary.val.map (RingHom.fst ℝ FiniteAdeles)).det ≠ 0 :=
    GeneralLinearGroup.det_ne_zero (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) binary)
  have inverseDet : ((realGroup y)⁻¹).val.det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  refine ⟨(binary.val.map (RingHom.fst ℝ FiniteAdeles)).det * ((realGroup y)⁻¹).val.det,
    mul_ne_zero binaryDet inverseDet, ?_⟩
  funext i
  rw [symm_archimedean]
  exact exterior_frame_apply (realGroup y) _ i

theorem frame_fullRank (y : AdelicGL) (binary : BinaryAdelicGL) :
    FullRank (coordinateEquiv.symm
      (archimedean (PlaneEisensteinContinuation.FrameProfile.frame y * binary.val))) := by
  obtain ⟨c, hc, equality⟩ := exists_exterior_frame y binary
  intro vanishing
  apply row_ne_zero (realGroup y)
  funext j
  have entry : c * (realGroup y).val 2 j = 0 := congrFun (equality.symm.trans vanishing) j
  exact (mul_eq_zero.mp entry).resolve_left hc

theorem frameLog_frame (real : RealGL3) (y : AdelicGL) (binary : BinaryAdelicGL) :
    frameLog real (archimedean (PlaneEisensteinContinuation.FrameProfile.frame y * binary.val)) =
      dvec real (fun j => (realGroup y).val 2 j) := by
  obtain ⟨c, hc, equality⟩ := exists_exterior_frame y binary
  rw [frameLog_eq_dvec, equality]
  exact dvec_smul real (row_ne_zero (realGroup y)) hc

/-! ### Openness and smoothness of `frameLog` -/

/-- The exterior product of the real frame with coordinates `value`. -/
def extE (value : RealSpace) : Fin 3 → ℝ := exterior (coordinateEquiv.symm value)

theorem extE_zero (value : RealSpace) :
    extE value 0 = value (1, 0) * value (2, 1) - value (2, 0) * value (1, 1) := rfl

theorem extE_one (value : RealSpace) :
    extE value 1 = value (2, 0) * value (0, 1) - value (0, 0) * value (2, 1) := rfl

theorem extE_two (value : RealSpace) :
    extE value 2 = value (0, 0) * value (1, 1) - value (1, 0) * value (0, 1) := rfl

theorem contDiff_coordinate {n : WithTop ℕ∞} (p : Fin 3 × Fin 2) :
    ContDiff ℝ n (fun value : RealSpace => value p) := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) p :
    EuclideanSpace ℝ (Fin 3 × Fin 2) →L[ℝ] ℝ).contDiff

theorem contDiff_extE {n : WithTop ℕ∞} (i : Fin 3) :
    ContDiff ℝ n (fun value : RealSpace => extE value i) := by
  have c : ∀ p : Fin 3 × Fin 2, ContDiff ℝ n (fun value : RealSpace => value p) :=
    fun p => contDiff_coordinate p
  refine fin3_forall
    (P := fun j => ContDiff ℝ n (fun value : RealSpace => extE value j)) ?_ ?_ ?_ i
  · have equality : (fun value : RealSpace => extE value 0) =
        fun value => value (1, 0) * value (2, 1) - value (2, 0) * value (1, 1) :=
      funext extE_zero
    rw [equality]
    exact ((c (1, 0)).mul (c (2, 1))).sub ((c (2, 0)).mul (c (1, 1)))
  · have equality : (fun value : RealSpace => extE value 1) =
        fun value => value (2, 0) * value (0, 1) - value (0, 0) * value (2, 1) :=
      funext extE_one
    rw [equality]
    exact ((c (2, 0)).mul (c (0, 1))).sub ((c (0, 0)).mul (c (2, 1)))
  · have equality : (fun value : RealSpace => extE value 2) =
        fun value => value (0, 0) * value (1, 1) - value (1, 0) * value (0, 1) :=
      funext extE_two
    rw [equality]
    exact ((c (0, 0)).mul (c (1, 1))).sub ((c (1, 0)).mul (c (0, 1)))

theorem fullRank_isOpen :
    IsOpen {value : RealSpace | FullRank (coordinateEquiv.symm value)} := by
  have continuous : Continuous (fun value : RealSpace => extE value) :=
    continuous_pi fun i => (contDiff_extE (n := 0) i).continuous
  exact (isOpen_ne : IsOpen {y : Fin 3 → ℝ | y ≠ 0}).preimage continuous

theorem frameLog_contDiffOn_aux {n : WithTop ℕ∞} (real : RealGL3) :
    ContDiffOn ℝ n (frameLog real)
      {value : RealSpace | FullRank (coordinateEquiv.symm value)} := by
  have coordinates : ∀ i, ContDiff ℝ n (fun value : RealSpace => extE value i) :=
    fun i => contDiff_extE i
  have first : ContDiff ℝ n (fun value : RealSpace => ∑ i, extE value i ^ 2) :=
    ContDiff.sum fun i _ => (coordinates i).pow 2
  have second : ContDiff ℝ n
      (fun value : RealSpace => ∑ j, (∑ i, extE value i * real.val i j) ^ 2) :=
    ContDiff.sum fun j _ => (ContDiff.sum fun i _ => (coordinates i).mul contDiff_const).pow 2
  have upper : ContDiffOn ℝ n (fun value : RealSpace => Real.log (∑ i, extE value i ^ 2))
      {value : RealSpace | FullRank (coordinateEquiv.symm value)} :=
    first.contDiffOn.log fun value hvalue => (sumSq_pos (w := extE value) hvalue).ne'
  have lower : ContDiffOn ℝ n
      (fun value : RealSpace => Real.log (∑ j, (∑ i, extE value i * real.val i j) ^ 2))
      {value : RealSpace | FullRank (coordinateEquiv.symm value)} :=
    second.contDiffOn.log fun value hvalue =>
      (sumSq_pos (w := fun j => ∑ i, extE value i * real.val i j)
        (vecMul_ne_zero real (e := extE value) hvalue)).ne'
  have combined : ContDiffOn ℝ n (fun value : RealSpace =>
      (1 / 3) * Real.log |real.val.det| + (1 / 2) * Real.log (∑ i, extE value i ^ 2) -
        (1 / 2) * Real.log (∑ j, (∑ i, extE value i * real.val i j) ^ 2))
      {value : RealSpace | FullRank (coordinateEquiv.symm value)} :=
    (contDiffOn_const.add (contDiffOn_const.mul upper)).sub (contDiffOn_const.mul lower)
  exact combined

theorem frameLog_contDiffOn (real : RealGL3) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (frameLog real)
      {value : RealSpace | FullRank (coordinateEquiv.symm value)} :=
  frameLog_contDiffOn_aux real

/-! ### `log Ξ(y h) - log Ξ(y)` through the real part of `y` -/

theorem atInfinity_one_eq : atInfinity (1 : RealGL3) = 1 := by
  apply InducedContinuity.adelic_ext
  · simp [InducedContinuity.realGroup_atInfinity]
  · simp [InducedContinuity.finiteGroup_atInfinity]

theorem lastRow_decomposition {R : Type} [CommRing R] (first second : R)
    (binary : GeneralLinearGroup (Fin 2) R) (unit : Rˣ) (k : GeneralLinearGroup (Fin 3) R)
    (j : Fin 3) :
    (planeUnipotent first second * planeLevi binary unit * k).val 2 j = unit.val * k.val 2 j := by
  have rowZero : (planeUnipotent first second * planeLevi binary unit).val 2 0 = 0 := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have rowOne : (planeUnipotent first second * planeLevi binary unit).val 2 1 = 0 := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  have rowTwo : (planeUnipotent first second * planeLevi binary unit).val 2 2 = unit.val := by
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, rowZero, rowOne, rowTwo]
  ring

/-- `logXi_translate` with the rotation made explicit. -/
theorem translate_explicit (a b : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) (X : RealGL3) :
    logXi (planeUnipotent a b * planeLevi binary unit * compact * atInfinity X) =
      logXi (atInfinity (realGroup compact * X)) +
        ((1 / 3) * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) -
          (2 / 3) * Real.log (adeleNorm unit : ℝ)) := by
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

theorem logXi_diff (y : AdelicGL) (h : RealGL3) :
    logXi (y * atInfinity h) - logXi y = dvec h (fun j => (realGroup y).val 2 j) := by
  obtain ⟨a, b, binary, unit, k, membership, rfl⟩ :=
    AdelicDecomposition.adelic_planeDecomposition y
  have viaOne := translate_explicit a b binary unit k membership 1
  have viaH := translate_explicit a b binary unit k membership h
  simp only [atInfinity_one_eq, mul_one] at viaOne
  have unitNonzero : unit.val.1 ≠ 0 :=
    (Units.map (RingHom.fst ℝ FiniteAdeles : Adeles →* ℝ) unit).ne_zero
  have rows : (fun j => (realGroup (planeUnipotent a b * planeLevi binary unit * k)).val 2 j) =
      fun j => unit.val.1 * (realGroup k).val 2 j := by
    funext j
    change ((planeUnipotent a b * planeLevi binary unit * k).val 2 j).1 =
      unit.val.1 * (k.val 2 j).1
    rw [lastRow_decomposition]
    rfl
  have kDet : |(realGroup k).val.det| ≠ 0 :=
    abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero (realGroup k))
  have hDet : |h.val.det| ≠ 0 := abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero h)
  have detMul : |((realGroup k) * h).val.det| = |(realGroup k).val.det| * |h.val.det| := by
    rw [Units.val_mul, Matrix.det_mul, abs_mul]
  have rowMul : ∑ j : Fin 3, (((realGroup k) * h).val 2 j) ^ 2 =
      ∑ j : Fin 3, (∑ i : Fin 3, (realGroup k).val 2 i * h.val i j) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Units.val_mul, Matrix.mul_apply]
  rw [viaH, viaOne, rows, dvec_smul h (row_ne_zero (realGroup k)) unitNonzero,
    logXi_atInfinity, logXi_atInfinity, detMul, rowMul, Real.log_mul kDet hDet]
  simp only [dvec]
  ring

theorem heightMultiplier_eq_frameLog (real : RealGL3) (z : ℂ) (y : AdelicGL)
    (binary : BinaryAdelicGL) :
    SectionMultipliers.heightMultiplier SectionMultipliersXi.logXi real z y =
      Complex.exp (z * (frameLog real
        (archimedean (PlaneEisensteinContinuation.FrameProfile.frame y * binary.val)) : ℂ)) := by
  unfold SectionMultipliers.heightMultiplier
  rw [logXi_diff, frameLog_frame]

end TernaryPeriodPolynomials.EdgeEisenstein.FrameMultiplier
