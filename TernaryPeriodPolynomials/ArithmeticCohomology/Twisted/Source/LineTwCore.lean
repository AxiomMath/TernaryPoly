module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.CellLine

@[expose] public section


/-!
# The core of the line source for the odd character

For the odd quadratic character of conductor three the line source is assembled like the plane
source, with three differences.  The spherical finite line vector is replaced by
the cell function `lineCell` of the good-line cusp (`cFinL`, `bFinL`), the radical is the radical
cocycle `lineRadical` of the real line parabolic, whose Levi module `lineStar` carries the scalar
`sgn(d) d² / |det A|` (`lineStar_binaryCoefficient`), and the Levi cocycle is the *untwisted*
`LeviCocycleData`: for odd `χ` the sign `χ(p) sgn(det A)` of `lineStar` is the sign of the corner `d`
of the parabolic element alone.  The transformation law of the real part therefore acquires the
factor `sgn(d) |d|² |det A|^{(n+1)/2}` (`lineCoreTw`), which combines with the finite factor with
exponents `2` and `(n+1)/2` into the induction law of the line.

This file gives the definitions of the line source, the finite cell laws, the real law along the
Iwasawa factor, the cup product form, the cocycle condition, the real equivariance, the general
translation law and the value at the good-line cusp.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (ConductorThree)
open TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit (referenceIntegral)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

namespace TernaryPeriodPolynomials.TwistedSource

section Defs

variable {n : ℕ}

open Classical in
/-- The `GL₂` block attached to a finite adele matrix on the cell `P_line(𝔸_f) · r⁻¹ · K₁`: the block
of a chosen parabolic factor of `f`, and `1` at the cusp point and off the cell. -/
def bFinGL (f : FiniteGL) : GeneralLinearGroup (Fin 2) FiniteAdeles :=
  if f = goodLineCusp then 1 else
    if h : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f then
      lineBlockGL (Classical.choose h).1 (Classical.choose h).2
    else 1

open Classical in
/-- The finite scalar factor attached to a finite adele matrix on the cell: the line factor, with
corner exponent `2` and block exponent `(n+1)/2`, of a chosen parabolic factor of `f`, `1` at the
cusp point and `0` off the cell. -/
def cFinL (D : InducingData n) (f : FiniteGL) : ℂ :=
  if f = goodLineCusp then 1 else
    if h : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f then
      finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) (Classical.choose h).1 (Classical.choose h).2
    else 0

/-- The finite `GL₂` translation attached to a finite adele matrix on the cell. -/
def bFinL (f : FiniteGL) : BinaryAdelicGL := atFinite (bFinGL f)

/-- The finite scalar factor attached to an adelic matrix. -/
def cFL (D : InducingData n) (g : AdelicGL) : ℂ := cFinL D (finiteGroup g)

/-- The finite `GL₂` translation attached to an adelic matrix. -/
def bFL (g : AdelicGL) : BinaryAdelicGL := bFinL (finiteGroup g)

theorem iwasawaB_mem_line (y : RealGL3) : iwasawaB y ∈ lineParabolic ℝ :=
  ⟨(iwasawaB_upper y).1, (iwasawaB_upper y).2.1⟩

/-- The parabolic Iwasawa factor `b(y)` as an element of the real line parabolic. -/
def iwL (y : RealGL3) : lineParabolic ℝ := ⟨iwasawaB y, iwasawaB_mem_line y⟩

/-- The `GL₂` block of the Iwasawa factor in the line parabolic. -/
def iwAL (y : RealGL3) : BinaryRealGL := lineLeviBlock (iwL y)

/-- **The line source cochain for the odd character**, at the `GL₂` adele `x`. -/
def lineSourceAtTw (D : InducingData n) (E : LeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((lineRadical n D.chi (iwL (realGroup g * y 2)) - lineRadical n D.chi (iwL (realGroup g * y 1)))
      (cFL D g • (E.α (iwAL (realGroup g * y 1)) (x * bFL g) -
        E.α (iwAL (realGroup g * y 0)) (x * bFL g))))

/-- **The line source cocycle for the odd character.** -/
def lineSourceTw (D : InducingData n) (E : LeviCocycleData D.cusp n) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  lineSourceAtTw D E y g 1

/-- The sign of the corner entry of a real line-parabolic element. -/
def epsL (p : lineParabolic ℝ) : ℂ := if 0 < p.1.val 0 0 then 1 else -1

/-- The positive real weight `d² / |det A|` of a real line-parabolic element with corner `d` and
lower block `A`. -/
def lineLeviWeight (p : lineParabolic ℝ) : ℝ := p.1.val 0 0 ^ 2 / |lrDet p|

end Defs

/-! ## The finite part on the cell -/

section Finite

variable {n : ℕ}

theorem cFinL_cusp (D : InducingData n) : cFinL D goodLineCusp = 1 := by
  unfold cFinL
  exact ite_eq_left rfl

theorem bFinGL_cusp : bFinGL goodLineCusp = 1 := by
  unfold bFinGL
  exact ite_eq_left rfl

theorem bFinL_cusp : bFinL goodLineCusp = 1 := by
  unfold bFinL
  rw [bFinGL_cusp]
  exact ps_atFinite_one

theorem cFinL_of_cell (D : InducingData n) {f : FiniteGL} (hf : f ≠ goodLineCusp)
    (h : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f) :
    cFinL D f = finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) (Classical.choose h).1
      (Classical.choose h).2 := by
  unfold cFinL
  rw [ite_eq_right hf, dite_eq_left h]

theorem cFinL_of_not_cell (D : InducingData n) {f : FiniteGL} (hf : f ≠ goodLineCusp)
    (h : ¬ InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f) : cFinL D f = 0 := by
  unfold cFinL
  rw [ite_eq_right hf, dite_eq_right h]

theorem bFinGL_of_cell {f : FiniteGL} (hf : f ≠ goodLineCusp)
    (h : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f) :
    bFinGL f = lineBlockGL (Classical.choose h).1 (Classical.choose h).2 := by
  unfold bFinGL
  rw [ite_eq_right hf, dite_eq_left h]

/-- The cell function is the scalar `cFinL` times the translation by `bFinL`, on spherical vectors. -/
theorem lineCell_eq_cFinL (D : InducingData n) (h3 : ConductorThree D.chi) (f : FiniteGL)
    {w : D.cusp.H} (hw : w ∈ sphericalSubspace D.cusp) :
    lineCell D.cusp D.chi 2 (((n : ℂ) + 1) / 2) f w = cFinL D f • D.cusp.π (bFinL f) w := by
  by_cases hf1 : f = goodLineCusp
  · subst hf1
    rw [cFinL_cusp D, bFinL_cusp, map_one, one_smul, Module.End.one_apply]
    exact lineCell_cusp D.cusp D.chi 2 (((n : ℂ) + 1) / 2) h3 hw
  · by_cases hcell : InCell (lineParabolic FiniteAdeles) finiteLevel goodLineCusp f
    · rw [cFinL_of_cell D hf1 hcell]
      unfold bFinL
      rw [bFinGL_of_cell hf1 hcell]
      obtain ⟨k, hk, hg⟩ := Classical.choose_spec hcell
      unfold lineCell
      rw [cellMap_apply_of_eq (lineCellFixes D.cusp D.chi 2 (((n : ℂ) + 1) / 2) h3)
        (Classical.choose hcell) hk hg hw, lineFactorHom_apply]
    · rw [cFinL_of_not_cell D hf1 hcell, zero_smul]
      unfold lineCell
      rw [cellMap_eq_zero hcell, LinearMap.zero_apply]

theorem rz_cFinL (D : InducingData n) (h3 : ConductorThree D.chi) (f : FiniteGL)
    {v : D.cusp.H} (hv : v ∈ sphericalSubspace D.cusp) (hs : v ∈ D.cusp.smooth)
    (x : BinaryAdelicGL) :
    rz D.cusp (lineCell D.cusp D.chi 2 (((n : ℂ) + 1) / 2) f v) x =
      cFinL D f * rz D.cusp v (x * bFinL f) := by
  rw [lineCell_eq_cFinL D h3 f hv, rz_smul (D.cusp.smooth_stable _ _ hs), rz_pi hs]

theorem cFL_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    cFL D (g * atInfinity z) = cFL D g := by
  unfold cFL
  rw [finiteGroup_mul_atInfinity]

theorem bFL_mul_atInfinity (g : AdelicGL) (z : RealGL3) :
    bFL (g * atInfinity z) = bFL g := by
  unfold bFL
  rw [finiteGroup_mul_atInfinity]

theorem bFinL_comm_atInfinity (f : FiniteGL) (z : BinaryRealGL) :
    bFinL f * atInfinity z = atInfinity z * bFinL f :=
  atFinite_mul_atInfinity_comm _ _

theorem twist_coeff_cellL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (f : FiniteGL) (h : BinaryRealGL) (x : BinaryAdelicGL)
    (ν : Fin 2 →₀ ℕ) :
    cFinL D f * (E.α h (x * bFinL f)).val.coeff ν =
      rz D.cusp (lineCell D.cusp D.chi 2 (((n : ℂ) + 1) / 2) f (E.lift ν h).val) x := by
  rw [rz_cFinL D h3 f (E.spherical ν h) (E.lift ν h).property, rz_lift]

/-- **Left equivariance of the finite twist** under the finite line parabolic. -/
theorem twist_left_cellL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (f f' fp : FiniteGL) (hfp : fp ∈ lineParabolic FiniteAdeles)
    (hf' : f' = fp * f) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinL D f' • E.α h (x * bFinL f') =
      finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) fp hfp •
        (cFinL D f • E.α h (x * atFinite (lineBlockGL fp hfp) * bFinL f)) := by
  subst hf'
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hsph := E.spherical ν h
  have hvf := lineCell_smooth D.cusp D.chi 2 (((n : ℂ) + 1) / 2) hv h3 hsph f
  have e1 := twist_coeff_cellL D E h3 (fp * f) h x ν
  have e2 := twist_coeff_cellL D E h3 f h (x * atFinite (lineBlockGL fp hfp)) ν
  have e3 : rz D.cusp (lineCell D.cusp D.chi 2 (((n : ℂ) + 1) / 2) (fp * f) (E.lift ν h).val) x =
      finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) fp hfp *
        rz D.cusp (lineCell D.cusp D.chi 2 (((n : ℂ) + 1) / 2) f (E.lift ν h).val)
          (x * atFinite (lineBlockGL fp hfp)) := by
    rw [lineCell_mul D.cusp D.chi 2 (((n : ℂ) + 1) / 2) h3 hsph hfp f,
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem twist_level_cellL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (f : FiniteGL) (k : finiteLevel) (h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    cFinL D (f * k.val) • E.α h (x * bFinL (f * k.val)) = cFinL D f • E.α h (x * bFinL f) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist_coeff_cellL D E h3 (f * k.val) h x ν, twist_coeff_cellL D E h3 f h x ν,
    lineCell_level D.cusp D.chi 2 (((n : ℂ) + 1) / 2) h3 (E.spherical ν h) f k]

end Finite

/-! ## Signs and weights -/

section Sign

theorem chi_real_signL (χ : RankOneCharacter) (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (t : ℝˣ) :
    χ.toMonoidHom (realAdeleUnit t) = if 0 < t.val then 1 else -1 := by
  by_cases hpos : 0 < t.val
  · rw [ite_eq_left hpos]
    exact χ.positiveReal t hpos
  · have hneg : t.val < 0 := lt_of_le_of_ne (not_lt.mp hpos) t.ne_zero
    have hdec : t = (-1) * (-t) := by rw [neg_mul, one_mul, neg_neg]
    have hpos' : 0 < (-t).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr hneg
    have hmul := map_mul realUnitHom (-1 : ℝˣ) (-t)
    rw [← hdec] at hmul
    have hmul' : realAdeleUnit t = realAdeleUnit (-1) * realAdeleUnit (-t) := hmul
    rw [ite_eq_right hpos, hmul', map_mul, hodd, χ.positiveReal _ hpos', mul_one]

/-- For an odd character the component character is the sign of the determinant. -/
theorem componentCharacter_eq_signL {n : ℕ} (D : InducingData n)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (g : RealGL3) :
    componentCharacter D.chi g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1 :=
  chi_real_signL D.chi hodd (GeneralLinearGroup.det g)

theorem sign_ite_mulL (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (if 0 < x * y then (1 : ℂ) else -1) =
      (if 0 < x then (1 : ℂ) else -1) * (if 0 < y then (1 : ℂ) else -1) := by
  rcases lt_or_gt_of_ne hx with a | a <;> rcases lt_or_gt_of_ne hy with b | b
  · rw [ite_eq_left (mul_pos_of_neg_of_neg a b), ite_eq_right (not_lt.2 a.le), ite_eq_right (not_lt.2 b.le)]
    norm_num
  · rw [ite_eq_right (not_lt.2 (mul_neg_of_neg_of_pos a b).le), ite_eq_right (not_lt.2 a.le), ite_eq_left b]
    norm_num
  · rw [ite_eq_right (not_lt.2 (mul_neg_of_pos_of_neg a b).le), ite_eq_left a, ite_eq_right (not_lt.2 b.le)]
    norm_num
  · rw [ite_eq_left (mul_pos a b), ite_eq_left a, ite_eq_left b]
    norm_num

theorem sign_det_invL (g : RealGL3) :
    (if 0 < (GeneralLinearGroup.det g⁻¹).val then (1 : ℂ) else -1) =
      if 0 < (GeneralLinearGroup.det g).val then 1 else -1 := by
  have hiff : 0 < (GeneralLinearGroup.det g⁻¹).val ↔ 0 < (GeneralLinearGroup.det g).val := by
    rw [_root_.map_inv, Units.val_inv_eq_inv_val, inv_pos]
  by_cases h : 0 < (GeneralLinearGroup.det g).val
  · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mp h'))]

/-- The sign of `x` divided by `x` is the inverse of `|x|`. -/
theorem sign_mul_inv_absL (x : ℝ) (hx : x ≠ 0) :
    (if 0 < x then (1 : ℂ) else -1) * ((x : ℝ) : ℂ)⁻¹ = ((|x| : ℝ) : ℂ)⁻¹ := by
  by_cases h : 0 < x
  · rw [ite_eq_left h, abs_of_pos h, one_mul]
  · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp h) hx
    rw [ite_eq_right h, abs_of_neg hneg, Complex.ofReal_neg, inv_neg, neg_one_mul]

theorem lineInv_val (p : lineParabolic ℝ) : (p⁻¹).1 = p.1⁻¹ := rfl

theorem lineCornerUnit_val (p : lineParabolic ℝ) :
    (lineCornerUnit p.1 p.2).val = p.1.val 0 0 := rfl

/-- The determinant of the lower block of a line-parabolic element. -/
theorem lineLeviBlock_det_val (p : lineParabolic ℝ) : (lineLeviBlock p).val.det = lrDet p :=
  (Matrix.det_fin_two _).trans rfl

theorem lineLeviBlock_det (p : lineParabolic ℝ) :
    (GeneralLinearGroup.det (lineLeviBlock p)).val = lrDet p := by
  rw [GeneralLinearGroup.val_det_apply]
  exact lineLeviBlock_det_val p

/-- The determinant of a line-parabolic element is the corner times the determinant of its block. -/
theorem det_line_mul_corner (p : lineParabolic ℝ) :
    (GeneralLinearGroup.det p.1).val = p.1.val 0 0 * lrDet p := by
  have hp : InLineParabolic p.1 := p.2
  have h10 : p.1.val 1 0 = 0 := hp.1
  have h20 : p.1.val 2 0 = 0 := hp.2
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, h10, h20]
  unfold lrDet
  ring

/-- The sign of the determinant of `p` is the sign of its corner times the sign of the determinant
of its block. -/
theorem sign_det_lineL (p : lineParabolic ℝ) :
    (if 0 < (GeneralLinearGroup.det p.1).val then (1 : ℂ) else -1) =
      epsL p * (if 0 < lrDet p then (1 : ℂ) else -1) := by
  have hp : InLineParabolic p.1 := p.2
  have hd : p.1.val 0 0 ≠ 0 := lr_corner_ne_zero hp
  have h := sign_ite_mulL _ _ hd (lrDet_ne_zero p)
  rw [← det_line_mul_corner p] at h
  exact h

theorem normPower_det_atInfinity_succ (A : BinaryRealGL) (z : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity A)) (z + 1) =
      normPower (GeneralLinearGroup.det (atInfinity A)) z *
        ((|(GeneralLinearGroup.det A).val| : ℝ) : ℂ) := by
  have hpos : 0 < |(GeneralLinearGroup.det A).val| :=
    abs_pos.mpr (GeneralLinearGroup.det A).ne_zero
  rw [normPower_det_atInfinity, normPower_det_atInfinity,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    add_mul, one_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]

theorem normPower_real_two (s : ℝˣ) : normPower (realAdeleUnit s) 2 = ((s.val : ℝ) : ℂ) ^ 2 := by
  have hpos : 0 < |s.val| := abs_pos.mpr s.ne_zero
  have h2 : (2 : ℂ) * ((Real.log |s.val| : ℝ) : ℂ) =
      ((Real.log |s.val| : ℝ) : ℂ) + ((Real.log |s.val| : ℝ) : ℂ) := by ring
  rw [TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    h2, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos, ← Complex.ofReal_mul,
    abs_mul_abs_self, Complex.ofReal_mul, sq]

theorem scalar_auxL (c e M D B : ℂ) (hB : B ≠ 0) :
    c * (M * B) * (e * (D / B)) = e * c * D * M := by
  have hinv : B * B⁻¹ = 1 := mul_inv_cancel₀ hB
  linear_combination (c * M * e * D) * hinv

end Sign

/-! ## The real law -/

section Real

variable {n : ℕ}

theorem iwL_mul_left (p : lineParabolic ℝ) (y : RealGL3) :
    ∃ m : lineParabolic ℝ, IsOrthogonalReal m.1 ∧ iwL (p.1 * y) * m = p * iwL y := by
  obtain ⟨m, hm, ho, -, hB⟩ := iwasawa_lineParabolic p.2 y
  refine ⟨⟨m, hm⟩, ho, ?_⟩
  apply Subtype.ext
  show iwasawaB (p.1 * y) * m = p.1 * iwasawaB y
  rw [hB, _root_.inv_mul_cancel_right]

/-- The radical vanishes on the orthogonal elements of the line parabolic. -/
theorem lineRadical_orth (χ : RankOneCharacter) {m : lineParabolic ℝ}
    (ho : IsOrthogonalReal m.1) : lineRadical n χ m = 0 := by
  obtain ⟨h01, h02⟩ := orth_lineParabolic_block m.2 ho
  exact lineRadical_eq_zero_of_row_zero n χ m h01 h02

/-- The block of an orthogonal element of the line parabolic is orthogonal. -/
theorem lineLeviBlock_orth (m : lineParabolic ℝ) (hm : IsOrthogonalReal m.1) :
    (lineLeviBlock m).val.transpose * (lineLeviBlock m).val = 1 := by
  obtain ⟨h01, h02⟩ := orth_lineParabolic_block m.2 hm
  have hc : m.1.val.transpose * m.1.val = 1 := hm
  have c11 := congrFun (congrFun hc 1) 1
  have c12 := congrFun (congrFun hc 1) 2
  have c21 := congrFun (congrFun hc 2) 1
  have c22 := congrFun (congrFun hc 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02] at c11 c12 c21 c22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLeviBlock, lrBlockP, lrLowerBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

theorem lineLeviBlock_iwL_mul (p : lineParabolic ℝ) (y : RealGL3) :
    ∃ k : BinaryRealGL, k.val.transpose * k.val = 1 ∧
      iwAL (p.1 * y) * k = lineLeviBlock p * iwAL y := by
  obtain ⟨m, ho, hm⟩ := iwL_mul_left p y
  refine ⟨lineLeviBlock m, lineLeviBlock_orth m ho, ?_⟩
  have h1 : lineLeviBlock (iwL (p.1 * y) * m) = lineLeviBlock (iwL (p.1 * y)) * lineLeviBlock m :=
    lineLeviBlockHom.map_mul _ _
  have h2 : lineLeviBlock (p * iwL y) = lineLeviBlock p * lineLeviBlock (iwL y) :=
    lineLeviBlockHom.map_mul _ _
  show lineLeviBlock (iwL (p.1 * y)) * lineLeviBlock m = lineLeviBlock p * lineLeviBlock (iwL y)
  rw [← h1, hm, h2]

/-- **The radical law along the Iwasawa factor.** -/
theorem lineRadical_iwL_mul (χ : RankOneCharacter) (p : lineParabolic ℝ) (y : RealGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    lineRadical n χ (iwL (p.1 * y)) Q =
      lineRadical n χ p Q +
        realCoefficientComponent n χ p.1
          (lineRadical n χ (iwL y) (lineStar χ (n + 1) p⁻¹ Q)) := by
  obtain ⟨m, ho, hm⟩ := iwL_mul_left p y
  have h0 : lineRadical n χ m = 0 := lineRadical_orth χ ho
  have e := lineRadical_mul n χ (iwL (p.1 * y)) m Q
  rw [hm, h0, lineRadical_mul n χ p (iwL y) Q, LinearMap.zero_apply, _root_.map_zero,
    add_zero] at e
  exact e.symm

/-- **The Levi cocycle along the Iwasawa factor** (untwisted). -/
theorem alpha_iwAL_mul {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (p : lineParabolic ℝ) (y : RealGL3) (x : BinaryAdelicGL) :
    E.α (iwAL (p.1 * y)) x =
      E.α (lineLeviBlock p) x +
        binaryCohomologicalAction n (lineLeviBlock p) (E.α (iwAL y)) x := by
  obtain ⟨k, hk, he⟩ := lineLeviBlock_iwL_mul p y
  have h1 : E.α (iwAL (p.1 * y) * k) x = E.α (iwAL (p.1 * y)) x := by
    rw [E.cocycle]
    have h0 : E.α k = fun _ => 0 := funext (E.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, E.cocycle]

/-- The scalar by which `lineStar` of the inverse acts on the inverse block: it is `sgn(d) d² /
|det A|`. -/
theorem lineTheta_inv (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (p : lineParabolic ℝ) :
    lineTheta χ p⁻¹ = epsL p * ((lineLeviWeight p : ℝ) : ℂ) := by
  have hp : InLineParabolic p.1 := p.2
  have hδ : lrDet p ≠ 0 := lrDet_ne_zero p
  have hcorner : (p⁻¹).1.val 0 0 = (p.1.val 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right (lr_corner_mul_inv hp)
  have e : lineLeviBlock p⁻¹ = (lineLeviBlock p)⁻¹ := lineLeviBlockHom.map_inv p
  have hdet0 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (lineLeviBlock p)) : ℂˣ) : ℂ) = ((lrDet p : ℝ) : ℂ) := by
    rw [GeneralLinearGroup.val_det_apply, ← lineLeviBlock_det_val p]
    exact (RingHom.map_det (algebraMap ℝ ℂ) (lineLeviBlock p).val).symm
  have hdet : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (lineLeviBlock p⁻¹)) : ℂˣ) : ℂ) = ((lrDet p : ℝ) : ℂ)⁻¹ := by
    rw [e, _root_.map_inv, _root_.map_inv, Units.val_inv_eq_inv_val, hdet0]
  have hs : componentCharacter χ (p⁻¹).1 = epsL p * (if 0 < lrDet p then (1 : ℂ) else -1) := by
    rw [lineInv_val, hc, sign_det_invL, sign_det_lineL]
  have hA : algebraMap ℝ ℂ (p.1.val 0 0) = ((p.1.val 0 0 : ℝ) : ℂ) := rfl
  have h := lineTheta_apply χ p⁻¹
  rw [hs, hcorner, hdet, inv_inv, hA] at h
  rw [h, lineLeviWeight, Complex.ofReal_div, Complex.ofReal_pow]
  have key := sign_mul_inv_absL (lrDet p) hδ
  linear_combination (epsL p * ((p.1.val 0 0 : ℝ) : ℂ) ^ 2) * key

/-- **The Levi part of `lineStar`**, the line analogue of `leviStar_binaryCoefficientTw`:
`lineStar χ (n+1) p⁻¹` composed with the binary coefficient of the block is the scalar
`sgn(d) d² / |det A|`. -/
theorem lineStar_binaryCoefficient (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (p : lineParabolic ℝ) (v : Binary.HomogeneousPoly (n + 1)) :
    lineStar χ (n + 1) p⁻¹ (binaryCoefficient n (lineLeviBlock p) v) =
      (epsL p * ((lineLeviWeight p : ℝ) : ℂ)) • v := by
  have e : lineLeviBlock p⁻¹ = (lineLeviBlock p)⁻¹ := lineLeviBlockHom.map_inv p
  show lineTheta χ p⁻¹ •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p⁻¹))
        (Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) v) =
      (epsL p * ((lineLeviWeight p : ℝ) : ℂ)) • v
  rw [lineTheta_inv χ hc p, e, _root_.map_inv, ← Module.End.mul_apply, ← map_mul,
    _root_.inv_mul_cancel, map_one, Module.End.one_apply]

/-- **The transformation law of the differenced radical potentials**, with the factor
`epsL p · |d|² · |det A|^{(n+1)/2}`. -/
theorem lineCoreTw {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (E : LeviCocycleData σ n) (p : lineParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL)
    (c : ℂ) :
    (lineRadical n χ (iwL (p.1 * u 2)) - lineRadical n χ (iwL (p.1 * u 1)))
        (c • (E.α (iwAL (p.1 * u 1)) t - E.α (iwAL (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((epsL p * c * normPower (realAdeleUnit (lineCornerUnit p.1 p.2)) 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p)))
              (((n : ℂ) + 1) / 2)) •
          (lineRadical n χ (iwL (u 2)) - lineRadical n χ (iwL (u 1)))
            (E.α (iwAL (u 1)) (t * atInfinity (lineLeviBlock p)) -
              E.α (iwAL (u 0)) (t * atInfinity (lineLeviBlock p)))) := by
  have hdiff : E.α (iwAL (p.1 * u 1)) t - E.α (iwAL (p.1 * u 0)) t =
      normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (lineLeviBlock p)
          (E.α (iwAL (u 1)) (t * atInfinity (lineLeviBlock p)) -
            E.α (iwAL (u 0)) (t * atInfinity (lineLeviBlock p))) := by
    rw [alpha_iwAL_mul E p (u 1) t, alpha_iwAL_mul E p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub]
    abel
  have hl : ((|lrDet p| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (lrDet_ne_zero p))
  have hS : c * normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p)))
        (((n : ℂ) + 3) / 2) * (epsL p * ((lineLeviWeight p : ℝ) : ℂ)) =
      epsL p * c * normPower (realAdeleUnit (lineCornerUnit p.1 p.2)) 2 *
        normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (((n : ℂ) + 1) / 2) := by
    have e3 : ((n : ℂ) + 3) / 2 = ((n : ℂ) + 1) / 2 + 1 := by ring
    rw [e3, normPower_det_atInfinity_succ, normPower_real_two, lineCornerUnit_val,
      lineLeviBlock_det, lineLeviWeight, Complex.ofReal_div, Complex.ofReal_pow]
    exact scalar_auxL c (epsL p) _ _ _ hl
  have hstar : lineStar χ (n + 1) p⁻¹
      (c • normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (lineLeviBlock p)
          (E.α (iwAL (u 1)) (t * atInfinity (lineLeviBlock p)) -
            E.α (iwAL (u 0)) (t * atInfinity (lineLeviBlock p)))) =
      (epsL p * c * normPower (realAdeleUnit (lineCornerUnit p.1 p.2)) 2 *
          normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p)))
            (((n : ℂ) + 1) / 2)) •
        (E.α (iwAL (u 1)) (t * atInfinity (lineLeviBlock p)) -
          E.α (iwAL (u 0)) (t * atInfinity (lineLeviBlock p))) := by
    rw [map_smul, map_smul, lineStar_binaryCoefficient χ hc, smul_smul, smul_smul, hS]
  rw [hdiff, LinearMap.sub_apply, lineRadical_iwL_mul χ p (u 2), lineRadical_iwL_mul χ p (u 1),
    hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-- `lineCoreTw` for the vertices `w * y i`. -/
theorem lineCoreTw_w {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = if 0 < (GeneralLinearGroup.det g).val then 1 else -1)
    (E : LeviCocycleData σ n) (p : lineParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3)
    (t : BinaryAdelicGL) (c : ℂ) :
    (lineRadical n χ (iwL (p.1 * (w * y 2))) - lineRadical n χ (iwL (p.1 * (w * y 1))))
        (c • (E.α (iwAL (p.1 * (w * y 1))) t - E.α (iwAL (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((epsL p * c * normPower (realAdeleUnit (lineCornerUnit p.1 p.2)) 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p)))
              (((n : ℂ) + 1) / 2)) •
          (lineRadical n χ (iwL (w * y 2)) - lineRadical n χ (iwL (w * y 1)))
            (E.α (iwAL (w * y 1)) (t * atInfinity (lineLeviBlock p)) -
              E.α (iwAL (w * y 0)) (t * atInfinity (lineLeviBlock p)))) :=
  lineCoreTw χ hc E p (fun i => w * y i) t c

end Real

/-! ## The cup product form and the laws of the line source -/

section Laws

variable {n : ℕ}

theorem lineSourceAtTw_eq_cup (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAtTw D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => cFL D g • E.α (iwAL (realGroup g * u)) (a * bFL g))
          (fun u : RealGL3 => lineRadical n D.chi (iwL (realGroup g * u))) y) := by
  unfold lineSourceAtTw psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the line source.** -/
theorem lineSourceAtTw_cocycle (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAtTw D E ![x 1, x 2, x 3] g a - lineSourceAtTw D E ![x 0, x 2, x 3] g a +
      lineSourceAtTw D E ![x 0, x 1, x 3] g a - lineSourceAtTw D E ![x 0, x 1, x 2] g a = 0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => cFL D g • E.α (iwAL (realGroup g * u)) (a * bFL g))
    (fun u : RealGL3 => lineRadical n D.chi (iwL (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [lineSourceAtTw_eq_cup]
  exact h2

/-- **Equivariance of the line source** for the real group. -/
theorem lineSourceAtTw_equivariant (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    lineSourceAtTw D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (lineSourceAtTw D E y (g * atInfinity h) a) := by
  unfold lineSourceAtTw
  rw [realGroup_mul_atInfinity, cFL_mul_atInfinity, bFL_mul_atInfinity]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

theorem twist_left_g_cellL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (g g' : AdelicGL) (f : FiniteGL)
    (hf : f ∈ lineParabolic FiniteAdeles) (hfin : finiteGroup g' = f * finiteGroup g)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFL D g' • E.α h (x * bFL g') =
      finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) f hf •
        (cFL D g • E.α h (x * atFinite (lineBlockGL f hf) * bFL g)) :=
  twist_left_cellL D E h3 (finiteGroup g) (finiteGroup g') f hf hfin h x

theorem sub_twist_cellL (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (g g' : AdelicGL) (f : FiniteGL)
    (hf : f ∈ lineParabolic FiniteAdeles) (hfin : finiteGroup g' = f * finiteGroup g)
    (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    cFL D g' • (E.α h1 (x * bFL g') - E.α h0 (x * bFL g')) =
      (finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) f hf * cFL D g) •
        (E.α h1 (x * atFinite (lineBlockGL f hf) * bFL g) -
          E.α h0 (x * atFinite (lineBlockGL f hf) * bFL g)) := by
  rw [smul_sub, twist_left_g_cellL D E h3 g g' f hf hfin h1 x,
    twist_left_g_cellL D E h3 g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the line source.** -/
theorem lineSourceAtTw_translate (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (g g' : AdelicGL) (p : lineParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ lineParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    lineSourceAtTw D E y g' x =
      (epsL p * normPower (realAdeleUnit (lineCornerUnit p.1 p.2)) 2 *
            normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p)))
              (((n : ℂ) + 1) / 2) *
          finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) f hf) •
        lineSourceAtTw D E y g (x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p))) := by
  have hc := componentCharacter_eq_signL D hodd
  have hcomm : bFL g * atInfinity (lineLeviBlock p) = atInfinity (lineLeviBlock p) * bFL g :=
    bFinL_comm_atInfinity _ _
  have ht : x * atFinite (lineBlockGL f hf) * bFL g * atInfinity (lineLeviBlock p) =
      x * (atFinite (lineBlockGL f hf) * atInfinity (lineLeviBlock p)) * bFL g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold lineSourceAtTw
  rw [hr, hu 2, hu 1, hu 0, sub_twist_cellL D E h3 g g' f hf hfin,
    lineCoreTw_w D.chi hc E p (realGroup g) y (x * atFinite (lineBlockGL f hf) * bFL g)
      (finiteLineFactor D.chi 2 (((n : ℂ) + 1) / 2) f hf * cFL D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  ring

end Laws

/-! ## The value at the good-line cusp -/

section Cusp

variable {n : ℕ}

/-- The value of the line source at an adele whose finite part is the good-line cusp: the finite
data is trivial, and only the real Iwasawa data remains. -/
theorem lineSourceTw_of_cusp (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (hg : finiteGroup g = goodLineCusp) :
    lineSourceTw D E y g =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        ((lineRadical n D.chi (iwL (realGroup g * y 2)) -
            lineRadical n D.chi (iwL (realGroup g * y 1)))
          (E.α (iwAL (realGroup g * y 1)) 1 - E.α (iwAL (realGroup g * y 0)) 1)) := by
  unfold lineSourceTw lineSourceAtTw cFL bFL
  rw [hg, cFinL_cusp D, bFinL_cusp, one_smul, mul_one]

theorem finiteGroup_cusp :
    finiteGroup (rationalGroup (rational referenceIntegral)⁻¹) = goodLineCusp :=
  (finiteGroup_rational _).trans goodLineCusp_eq.symm

/-- The real image of the good-line cusp frame is the rational matrix `(referenceIntegral)⁻¹`. -/
theorem realGroup_cuspL :
    realGroup (rationalGroup (rational referenceIntegral)⁻¹) =
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (rational referenceIntegral))⁻¹ := by
  rw [realGroup_rational, _root_.map_inv]

/-- **The value of the line source at the good-line cusp.** -/
theorem lineSourceTw_cusp (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) :
    lineSourceTw D E y (rationalGroup (rational referenceIntegral)⁻¹) =
      realCoefficientComponent n D.chi
          (realGroup (rationalGroup (rational referenceIntegral)⁻¹))⁻¹
        ((lineRadical n D.chi
              (iwL (realGroup (rationalGroup (rational referenceIntegral)⁻¹) * y 2)) -
            lineRadical n D.chi
              (iwL (realGroup (rationalGroup (rational referenceIntegral)⁻¹) * y 1)))
          (E.α (iwAL (realGroup (rationalGroup (rational referenceIntegral)⁻¹) * y 1)) 1 -
            E.α (iwAL (realGroup (rationalGroup (rational referenceIntegral)⁻¹) * y 0)) 1)) :=
  lineSourceTw_of_cusp D E y _ finiteGroup_cusp

end Cusp

end TernaryPeriodPolynomials.TwistedSource
