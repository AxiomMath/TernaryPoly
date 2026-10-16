module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.HeckeShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegralFlags
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.LocalSupport
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.BadPlaneOrbit
public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralBases

@[expose] public section


/-!
# The four cusps of the arithmetic level

For each side the good flags form one `Γ`-orbit and the bad flags form one `Γ`-orbit. Two of the
four statements were already in the project (bad planes: `badPlane_exists_transporter`, good
lines: `good_line_arithmetic_orbit`); the good-plane and bad-line orbits are proved here by the
mod-three last-row criterion. Consequently every away-from-three correspondence `t` transports each
of the four reference flags back into its own orbit (`Transports`), and the Shapiro–Hecke formula
of `HeckeShapiro` applies at all four cusps.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.Spectral.CuspOrbits

open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)
open TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.Helpers

theorem rationalInclusion_eq_rational (element : arithmeticLevel) :
    rationalInclusion element = rational element.val := rfl

theorem lastRow_vecMul (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    lastRow ᵥ* M = fun column => M 2 column := by
  funext column
  simp [lastRow, single_vecMul]

/-- Transport between two integral frames whose last rows agree modulo three after a parabolic
change of frame. -/
theorem exists_level_transport (side : Side) (k k₀ p : IntegralGL3)
    (hp : rational p ∈ parabolic side)
    (hrow : ∀ column, ((k * p).val 2 column : ZMod 3) = (k₀.val 2 column : ZMod 3)) :
    ∃ γ : rationalLevel,
      γ.val • (QuotientGroup.mk (rational k₀) : Flags side) = QuotientGroup.mk (rational k) := by
  have hlevel : k * p * k₀⁻¹ ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree (k * p * k₀⁻¹)).val = lastRow
    rw [map_mul, map_inv, GeneralLinearGroup.coe_mul, ← vecMul_vecMul]
    have h1 : lastRow ᵥ* (reductionThree (k * p)).val = lastRow ᵥ* (reductionThree k₀).val := by
      rw [lastRow_vecMul, lastRow_vecMul]
      funext column
      exact hrow column
    rw [h1, vecMul_vecMul, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
      GeneralLinearGroup.coe_one, vecMul_one]
  refine ⟨⟨rationalInclusion ⟨k * p * k₀⁻¹, hlevel⟩, ⟨_, rfl⟩⟩, ?_⟩
  change (QuotientGroup.mk (rational (k * p * k₀⁻¹) * rational k₀) : Flags side) = _
  rw [← map_mul, inv_mul_cancel_right, map_mul]
  exact QuotientGroup.mk_mul_of_mem _ hp

/-! ### Explicit integral matrices -/

/-- `[[1,0,0],[c,d,e],[0,0,1]]` with `d = ±1`. -/
def planeShearA (c d e : ℤ) (hd : d * d = 1) : IntegralGL3 :=
  ⟨!![1,0,0;c,d,e;0,0,1], !![1,0,0;-(d*c),d,-(d*e);0,0,1], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- `[[0,d,e],[1,0,0],[0,0,1]]` with `d = ±1`. -/
def planeShearB (d e : ℤ) (hd : d * d = 1) : IntegralGL3 :=
  ⟨!![0,d,e;1,0,0;0,0,1], !![0,1,0;d,0,-(d*e);0,0,1], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- `[[1,0,0],[0,1,0],[0,c,d]]` with `d = ±1`. -/
def lineShearA (c d : ℤ) (hd : d * d = 1) : IntegralGL3 :=
  ⟨!![1,0,0;0,1,0;0,c,d], !![1,0,0;0,1,0;0,-(d*c),d], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- `[[1,0,0],[0,0,d],[0,1,0]]` with `d = ±1`. -/
def lineShearB (d : ℤ) (hd : d * d = 1) : IntegralGL3 :=
  ⟨!![1,0,0;0,0,d;0,1,0], !![1,0,0;0,0,1;0,d,0], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with rfl | rfl <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The reference frame of the good plane `span(e₁, e₃)`. -/
def goodPlaneFrame : IntegralGL3 :=
  ⟨!![1,0,0;0,0,1;0,1,0], !![1,0,0;0,0,1;0,1,0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- A residue `y ≠ 0` modulo three has a sign `d = ±1` with `d ≡ y`. -/
theorem exists_sign (y : ZMod 3) (hy : y ≠ 0) : ∃ d : ℤ, d * d = 1 ∧ (d : ZMod 3) = y := by
  fin_cases y
  · exact (hy rfl).elim
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨-1, by norm_num, rfl⟩

theorem zmod3_sq (y : ZMod 3) (hy : y ≠ 0) : y * y = 1 := by
  fin_cases y
  · exact (hy rfl).elim
  · decide
  · decide

/-! ### The good-plane orbit -/

theorem plane_row_nonzero_of_good (k : IntegralGL3)
    (good : GoodFlag .plane (QuotientGroup.mk (rational k))) :
    (k.val 2 0 : ZMod 3) ≠ 0 ∨ (k.val 2 1 : ZMod 3) ≠ 0 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨v, hkernel, hlast⟩ :=
    (TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.Helpers.good_flag_kernel_iff
      (rational k)).mp good
  set u : Fin 3 → ℤ := (k⁻¹).val *ᵥ v with hu
  have hinv : (rational k).inv = (k⁻¹).val.map (Int.cast : ℤ → ℚ) := by
    change ((rational k)⁻¹).val = _
    rw [← map_inv]
    rfl
  have hcast : (rational k).inv *ᵥ (fun index => (v index : ℚ)) = fun index => (u index : ℚ) := by
    rw [hinv]
    funext index
    simp [hu, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hcast] at hkernel
  have hu2 : u 2 = 0 := by
    have h : ((u 2 : ℤ) : ℚ) = 0 := hkernel
    exact_mod_cast h
  have hv : v = k.val *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
      GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  apply hlast
  rw [hv]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hu2, mul_zero, add_zero]
  push_cast
  rw [hcontra.1, hcontra.2]
  ring

theorem goodPlaneFrame_good :
    GoodFlag .plane (QuotientGroup.mk (rational goodPlaneFrame)) := by
  refine ⟨![0,0,1], ⟨rational goodPlaneFrame, rfl, ![0,1,0], rfl, ?_⟩, by decide⟩
  funext i
  fin_cases i <;> simp [rational, goodPlaneFrame, GeneralLinearGroup.map_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **The good planes form one `Γ`-orbit**, that of `span(e₁, e₃)`. -/
theorem goodPlane_exists_transporter (flag : Flags .plane) (good : GoodFlag .plane flag) :
    ∃ γ : rationalLevel,
      γ.val • (QuotientGroup.mk (rational goodPlaneFrame) : Flags .plane) = flag := by
  obtain ⟨k, rfl⟩ := TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags.integral_representative
    .plane flag
  have hrow := plane_row_nonzero_of_good k good
  by_cases hy : (k.val 2 1 : ZMod 3) = 0
  · have hx : (k.val 2 0 : ZMod 3) ≠ 0 := hrow.resolve_right (not_not.mpr hy)
    obtain ⟨d, hd, hdx⟩ := exists_sign _ hx
    apply exists_level_transport .plane k goodPlaneFrame (planeShearB d (-(d * k.val 2 2)) hd)
    · exact ⟨by simp [rational, planeShearB, GeneralLinearGroup.map_apply],
        by simp [rational, planeShearB, GeneralLinearGroup.map_apply]⟩
    · intro column
      have hsq := zmod3_sq _ hx
      fin_cases column <;>
        simp [planeShearB, goodPlaneFrame, Matrix.mul_apply, Fin.sum_univ_three, hy, hdx] <;>
        first
          | linear_combination hsq
          | linear_combination (-(k.val 2 0 : ZMod 3)) * hsq
          | linear_combination (-(k.val 2 1 : ZMod 3)) * hsq
          | linear_combination (-(k.val 2 2 : ZMod 3)) * hsq
  · obtain ⟨d, hd, hdy⟩ := exists_sign _ hy
    apply exists_level_transport .plane k goodPlaneFrame
      (planeShearA (-(d * k.val 2 0)) d (-(d * k.val 2 2)) hd)
    · exact ⟨by simp [rational, planeShearA, GeneralLinearGroup.map_apply],
        by simp [rational, planeShearA, GeneralLinearGroup.map_apply]⟩
    · intro column
      have hsq := zmod3_sq _ hy
      fin_cases column <;>
        simp [planeShearA, goodPlaneFrame, Matrix.mul_apply, Fin.sum_univ_three, hdy] <;>
        first
          | linear_combination hsq
          | linear_combination (-(k.val 2 0 : ZMod 3)) * hsq
          | linear_combination (-(k.val 2 1 : ZMod 3)) * hsq
          | linear_combination (-(k.val 2 2 : ZMod 3)) * hsq

/-! ### The bad-line orbit -/

theorem line_row_zero_of_bad (k : IntegralGL3)
    (bad : ¬ GoodFlag .line (QuotientGroup.mk (rational k))) : (k.val 2 0 : ZMod 3) = 0 := by
  by_contra hne
  apply bad
  refine ⟨fun row => k.val row 0, ⟨rational k, rfl, ![1,0,0], ⟨rfl, rfl⟩, ?_⟩, hne⟩
  funext i
  simp [rational, GeneralLinearGroup.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem line_identity_not_good : ¬ GoodFlag .line (QuotientGroup.mk (1 : RationalGL3)) := by
  rintro ⟨v, ⟨g, hg, w, ⟨hw1, hw2⟩, hv⟩, hlast⟩
  have hmem : (1 : RationalGL3)⁻¹ * g ∈ parabolic .line := QuotientGroup.eq.mp hg.symm
  rw [inv_one, one_mul] at hmem
  have h2 : (v 2 : ℚ) = 0 := by
    have := congrFun hv 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw1, hw2, mul_zero,
      add_zero] at this
    rw [← this]
    change g.val 2 0 * w 0 = 0
    rw [hmem.2, zero_mul]
  apply hlast
  have : v 2 = 0 := by exact_mod_cast h2
  rw [this, Int.cast_zero]

theorem plane_identity_not_good : ¬ GoodFlag .plane (QuotientGroup.mk (1 : RationalGL3)) := by
  intro good
  have := plane_row_nonzero_of_good 1 (by simpa using good)
  simp at this

/-- **The bad lines form one `Γ`-orbit**, that of the standard line `ℤe₁`. -/
theorem badLine_exists_transporter (flag : Flags .line) (bad : ¬ GoodFlag .line flag) :
    ∃ γ : rationalLevel, γ.val • (QuotientGroup.mk (1 : RationalGL3) : Flags .line) = flag := by
  obtain ⟨k, rfl⟩ := TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags.integral_representative
    .line flag
  have hx := line_row_zero_of_bad k bad
  have hrow : (k.val 2 1 : ZMod 3) ≠ 0 ∨ (k.val 2 2 : ZMod 3) ≠ 0 := by
    by_contra hcontra
    push Not at hcontra
    have hdet := congrArg (fun M : IntegralGL3 => (M.val 2 2 : ZMod 3)) (mul_inv_cancel k)
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at hdet
    push_cast at hdet
    rw [hx, hcontra.1, hcontra.2] at hdet
    simp at hdet
  have hone : (QuotientGroup.mk (1 : RationalGL3) : Flags .line) =
      QuotientGroup.mk (rational 1) := by rw [map_one]
  rw [hone]
  by_cases hy : (k.val 2 2 : ZMod 3) = 0
  · have hx' : (k.val 2 1 : ZMod 3) ≠ 0 := hrow.resolve_right (not_not.mpr hy)
    obtain ⟨d, hd, hdx⟩ := exists_sign _ hx'
    apply exists_level_transport .line k 1 (lineShearB d hd)
    · exact ⟨by simp [rational, lineShearB, GeneralLinearGroup.map_apply],
        by simp [rational, lineShearB, GeneralLinearGroup.map_apply]⟩
    · intro column
      have hsq := zmod3_sq _ hx'
      fin_cases column <;>
        simp [lineShearB, Matrix.mul_apply, Fin.sum_univ_three, hx, hy, hdx, hsq]
  · obtain ⟨d, hd, hdy⟩ := exists_sign _ hy
    apply exists_level_transport .line k 1 (lineShearA (-(d * k.val 2 1)) d hd)
    · exact ⟨by simp [rational, lineShearA, GeneralLinearGroup.map_apply],
        by simp [rational, lineShearA, GeneralLinearGroup.map_apply]⟩
    · intro column
      have hsq := zmod3_sq _ hy
      fin_cases column <;>
        simp [lineShearA, Matrix.mul_apply, Fin.sum_univ_three, hx, hdy] <;>
        first
          | linear_combination hsq
          | linear_combination (-(k.val 2 1 : ZMod 3)) * hsq

/-! ### The four reference cusps and away-from-three transport -/

theorem goodLineFrame_good : GoodFlag .line (QuotientGroup.mk
    (rational TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral)) := by
  refine ⟨![1,0,1], ⟨_, rfl, ![1,0,0], ⟨rfl, rfl⟩, ?_⟩, by decide⟩
  funext i
  fin_cases i <;> simp [rational,
    TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral,
    GeneralLinearGroup.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The reference flag of the cusp of the given side and goodness. -/
def cuspFlag : (side : Side) → Bool → Flags side
  | .plane, true => QuotientGroup.mk (rational goodPlaneFrame)
  | .plane, false => QuotientGroup.mk 1
  | .line, true => QuotientGroup.mk
      (rational TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral)
  | .line, false => QuotientGroup.mk 1

theorem cuspFlag_good_iff (side : Side) (good : Bool) :
    GoodFlag side (cuspFlag side good) ↔ good = true := by
  cases side <;> cases good
  · simpa [cuspFlag] using plane_identity_not_good
  · simpa [cuspFlag] using goodPlaneFrame_good
  · simpa [cuspFlag] using line_identity_not_good
  · simpa [cuspFlag] using goodLineFrame_good

/-- Every flag of the same goodness is a `Γ`-translate of the reference flag. -/
theorem cuspFlag_transporter (side : Side) (good : Bool) (flag : Flags side)
    (hflag : GoodFlag side flag ↔ good = true) :
    ∃ γ : rationalLevel, γ.val • cuspFlag side good = flag := by
  cases side <;> cases good
  · exact TernaryPeriodPolynomials.SphericalDetection.Helpers.badPlane_exists_transporter
      flag (by simpa using hflag)
  · exact goodPlane_exists_transporter flag (by simpa using hflag)
  · exact badLine_exists_transporter flag (by simpa using hflag)
  · obtain ⟨γ, hγ⟩ := TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases.good_line_arithmetic_orbit
      flag (by simpa using hflag)
    exact ⟨⟨rationalInclusion γ, ⟨γ, rfl⟩⟩, hγ⟩

theorem level_matrix_of_representative (t : HeckeCorrespondence) (haway : AwayThree t)
    {r : RationalGL3} (hr : r ∈ t.representatives) : LevelMatrixAtThree r := by
  have hlevel := level_matrix_of_entries t.g (fun row column => (haway.1 row column).1) haway.2
  obtain ⟨left, right, hrepresentative⟩ := t.inDoubleCoset r hr
  rw [hrepresentative]
  exact level_matrix_mul (level_matrix_mul (level_matrix_of_rational_level left.property) hlevel)
    (level_matrix_of_rational_level right.property)

/-- Away-from-three representatives preserve goodness of flags. -/
theorem goodFlag_inv_smul_iff (t : HeckeCorrespondence) (haway : AwayThree t)
    {r : RationalGL3} (hr : r ∈ t.representatives) (side : Side) (flag : Flags side) :
    GoodFlag side (r⁻¹ • flag) ↔ GoodFlag side flag := by
  constructor
  · intro h
    have := good_flag_smul (level_matrix_of_representative t haway hr) h
    rwa [smul_inv_smul] at this
  · exact good_flag_smul (inverse_representative_level t haway hr)

/-- **Every away-from-three correspondence transports each reference cusp into its orbit.** -/
theorem transports_cuspFlag (t : HeckeCorrespondence) (haway : AwayThree t) (side : Side)
    (good : Bool) : HeckeShapiro.Transports t (cuspFlag side good) := by
  intro r hr
  apply cuspFlag_transporter
  rw [goodFlag_inv_smul_iff t haway hr, cuspFlag_good_iff]

end TernaryPeriodPolynomials.Spectral.CuspOrbits
