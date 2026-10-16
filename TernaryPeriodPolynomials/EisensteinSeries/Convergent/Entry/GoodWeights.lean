module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad1
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Weight
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.FlagProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line
public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralBases

@[expose] public section


/-!
# The good-line and bad-plane weights

The finite weights of the two sections of the boundary comparison: `badPlaneWeight` (the indicator of `P(ℚ₃) K₁` at the
prime `3`, supported on the bad-plane orbit) is a **plane weight** (`badPlaneWeight_planeWeight`, `Entry/REBadMain`) and `goodLineWeight` (the
indicator of `L(ℚ₃) g₀ K₁`, supported on the good-line orbit) is a **line weight** (`goodLineWeight_lineWeight`); their laws
are those of `Entry/REBad1`.

The local-global dictionary with the arithmetic flags: for a rational `q`,
`goodLineWeight(ρ(q⁻¹)) = [qP is a good line]` (`goodLineWeight_rational`, via the one-orbit theorem for good lines and the
local disjointness `g₀ ∉ L(ℚ₃) K₁`, `localGoodLine_ne_mul`) and
`badPlaneWeight(ρ(q⁻¹)) = 1 - [qP is a good plane]` (`badPlaneWeight_rational`).  Hence multiplication by the good-line
weight is the good-flag component projection `goodComponent` on the line stratum cohomology.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem localGoodLine_inv : (localGoodLine : LocalThreeGL)⁻¹ = localGoodLine := by
  apply Units.ext
  rfl

/-- **`g₀ ∉ L(ℚ₃) K₁`**: the good-line orbit and the bad-line orbit are disjoint locally at `3`. -/
theorem localGoodLine_ne_mul (p : GeneralEisenstein.Adelic.lineParabolic ℚ_[3]) (k : LocalThreeGL) (hk : InLocalThreeLevel k) :
    localGoodLine ≠ p.val * k := by
  intro h
  have hk' : k = p.val⁻¹ * localGoodLine := by rw [h, inv_mul_cancel_left]
  have hK : k⁻¹ = localGoodLine * p.val := by
    rw [hk', _root_.mul_inv_rev, inv_inv, localGoodLine_inv]
  obtain ⟨kz, hrow, hkz⟩ := inLocalThreeLevel_inv hk
  rw [hK] at hkz
  have e : ∀ i j, ((kz.val i j : ℤ_[3]) : ℚ_[3]) = (localGoodLine * p.val).val i j := by
    intro i j
    have := congrArg (fun m : LocalThreeGL => m.val i j) hkz
    simp only [GeneralLinearGroup.map_apply] at this
    exact this
  have p10 : p.val.val 1 0 = 0 := p.property.1
  have p20 : p.val.val 2 0 = 0 := p.property.2
  have z00 : kz.val 0 0 = 0 := by
    have := e 0 0
    simp [localGoodLine, Matrix.mul_apply, Fin.sum_univ_three, p20] at this
    exact_mod_cast this
  have z10 : kz.val 1 0 = 0 := by
    have := e 1 0
    simp [localGoodLine, Matrix.mul_apply, Fin.sum_univ_three, p10] at this
    exact_mod_cast this
  have hunit : IsUnit (kz.val.det) := by
    have := (Matrix.GeneralLinearGroup.det kz).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  rw [Matrix.det_fin_three, z00, z10] at hunit
  have ha : IsUnit (kz.val 2 0) := by
    have : kz.val 0 1 * kz.val 1 2 * kz.val 2 0 - kz.val 0 2 * kz.val 1 1 * kz.val 2 0 =
        kz.val 2 0 * (kz.val 0 1 * kz.val 1 2 - kz.val 0 2 * kz.val 1 1) := by ring
    simp only [zero_mul, mul_zero, sub_zero, add_zero, zero_add] at hunit
    rw [this] at hunit
    exact (IsUnit.mul_iff.mp hunit).1
  have hz := congrFun hrow 0
  rw [TernaryPeriodPolynomials.Spectral.CuspOrbits.lastRow_vecMul] at hz
  have : (PadicInt.toZMod (kz.val 2 0)) = 0 := by
    simpa [GeneralLinearGroup.map_apply, lastRow] using hz
  exact (ha.map PadicInt.toZMod).ne_zero this


open TernaryPeriodPolynomials.Spectral.CuspOrbits (badLine_exists_transporter)
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases (good_line_arithmetic_orbit)

theorem map_rationalLevel_level (γ : rationalLevel) :
    InLocalThreeLevel (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val) := by
  obtain ⟨δ, hδ⟩ := γ.property
  rw [← hδ]
  exact arithmeticLevel_atThree δ

theorem mem_lineParabolic_of_flag_eq {a b : RationalGL3}
    (h : (QuotientGroup.mk a : Flags .line) = QuotientGroup.mk b) : a⁻¹ * b ∈ GeneralEisenstein.Adelic.lineParabolic ℚ :=
  QuotientGroup.eq.mp h

theorem goodLineSet_of_good (q : RationalGL3) (good : GoodFlag .line (QuotientGroup.mk q)) :
    goodLineSet (adelicThreeGroup (rationalGroup q⁻¹)) := by
  obtain ⟨δ0, h0⟩ := good_line_arithmetic_orbit _ good
  obtain ⟨δ1, h1⟩ := good_line_arithmetic_orbit _ (rationalGoodLine_good)
  set ref : Flags .line := QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ)
    TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral) with href
  have hr : ref = (rationalInclusion δ1)⁻¹ • (QuotientGroup.mk rationalGoodLine : Flags .line) := by
    rw [← h1, inv_smul_smul]
  set R : RationalGL3 := rationalInclusion δ0 * (rationalInclusion δ1)⁻¹ with hR
  have hq : (QuotientGroup.mk (R * rationalGoodLine) : Flags .line) = QuotientGroup.mk q := by
    rw [← h0, hr, smul_smul]
    rfl
  have hp0 := mem_lineParabolic_of_flag_eq hq
  set p0 : RationalGL3 := (R * rationalGoodLine)⁻¹ * q with hp0def
  have hqeq : q = R * rationalGoodLine * p0 := by rw [hp0def, mul_inv_cancel_left]
  have hRlevel : InLocalThreeLevel (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) R) := by
    have : R = rationalInclusion (δ0 * δ1⁻¹) := by rw [hR, map_mul, map_inv]
    rw [this]
    exact arithmeticLevel_atThree _
  refine ⟨⟨(GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹,
    ((GeneralEisenstein.Adelic.lineParabolic ℚ_[3]).inv_mem
      (generalLinearGroup_map_line (algebraMap ℚ ℚ_[3]) hp0))⟩,
    (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) R)⁻¹, inLocalThreeLevel_inv hRlevel, ?_⟩
  have e1 : GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) rationalGoodLine = localGoodLine :=
    rationalGoodLine_at_three
  show adelicThreeGroup (rationalGroup q⁻¹) = (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹ *
    localGoodLine * (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) R)⁻¹
  rw [adelicThreeGroup_rational, hqeq]
  simp only [_root_.mul_inv_rev, map_mul, map_inv, e1, localGoodLine_inv]
  simp only [mul_assoc]

theorem good_of_goodLineSet (q : RationalGL3) (hset : goodLineSet (adelicThreeGroup (rationalGroup q⁻¹))) :
    GoodFlag .line (QuotientGroup.mk q) := by
  by_contra hbad
  obtain ⟨γ, hγ⟩ := badLine_exists_transporter _ hbad
  have hq : (QuotientGroup.mk γ.val : Flags .line) = QuotientGroup.mk q := by
    rw [← hγ]
    change _ = (QuotientGroup.mk (γ.val * 1) : Flags .line)
    rw [mul_one]
  have hp0 := mem_lineParabolic_of_flag_eq hq
  set p0 : RationalGL3 := γ.val⁻¹ * q with hp0def
  have hqeq : q = γ.val * p0 := by rw [hp0def, mul_inv_cancel_left]
  obtain ⟨p, k, hk, hpk⟩ := hset
  rw [adelicThreeGroup_rational, hqeq] at hpk
  simp only [_root_.mul_inv_rev, map_mul, map_inv] at hpk
  -- hpk : (map p0)⁻¹ * (map γ)⁻¹ = p * g₀ * k
  apply localGoodLine_ne_mul
    (p⁻¹ * ⟨(GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹,
      (GeneralEisenstein.Adelic.lineParabolic ℚ_[3]).inv_mem
        (generalLinearGroup_map_line (algebraMap ℚ ℚ_[3]) hp0)⟩)
    ((GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)⁻¹ * k⁻¹)
    (InLocalThreeLevel_mul (inLocalThreeLevel_inv (map_rationalLevel_level γ)) (inLocalThreeLevel_inv hk))
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  show localGoodLine = (p.val⁻¹ * (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹) *
    ((GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)⁻¹ * k⁻¹)
  calc localGoodLine = p.val⁻¹ * (p.val * localGoodLine * k) * k⁻¹ := by group
    _ = _ := by rw [← hpk]; group


open Classical in
/-- **The good-line weight represents the good flags** (local-global): for a rational `q`,
`ι_L(ρ(q⁻¹)) = 1` exactly when the line `qP` is good (`GoodFlag`), and `0` otherwise. -/
theorem goodLineWeight_rational (q : RationalGL3) :
    goodLineWeight (rationalGroup q⁻¹) = goodWeight .line (QuotientGroup.mk q) := by
  unfold goodLineWeight goodWeight
  exact if_congr ⟨good_of_goodLineSet q, goodLineSet_of_good q⟩ rfl rfl


open TernaryPeriodPolynomials.Spectral.CuspOrbits (goodPlane_exists_transporter goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

/-- **`(good plane)⁻¹ ∉ P(ℚ₃) K₁`**: the good-plane orbit and the bad-plane orbit are disjoint locally at `3`. -/
theorem goodPlane_ne_mul (p : planeParabolic ℚ_[3]) (k : LocalThreeGL) (hk : InLocalThreeLevel k) :
    GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rational goodPlaneFrame) ≠ p.val * k := by
  intro h
  have hk' : k = p.val⁻¹ * GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rational goodPlaneFrame) := by
    rw [h, inv_mul_cancel_left]
  obtain ⟨kz, hrow, hkz⟩ := hk
  have q20 : ((p.val : Matrix (Fin 3) (Fin 3) ℚ_[3])⁻¹) 2 0 = 0 := by
    rw [← Matrix.coe_units_inv]; exact (p⁻¹).property.1
  have q21 : ((p.val : Matrix (Fin 3) (Fin 3) ℚ_[3])⁻¹) 2 1 = 0 := by
    rw [← Matrix.coe_units_inv]; exact (p⁻¹).property.2
  have e : ((kz.val 2 2 : ℤ_[3]) : ℚ_[3]) = 0 := by
    have := congrArg (fun m : LocalThreeGL => m.val 2 2) hkz
    simp only [GeneralLinearGroup.map_apply] at this
    rw [show ((kz.val 2 2 : ℤ_[3]) : ℚ_[3]) = PadicInt.Coe.ringHom (kz.val 2 2) from rfl, this, hk']
    simp [Matrix.mul_apply, Fin.sum_univ_three, q20, q21, rational, goodPlaneFrame]
  have z : kz.val 2 2 = 0 := PadicInt.coe_eq_zero.mp e
  have hz := congrFun hrow 2
  rw [TernaryPeriodPolynomials.Spectral.CuspOrbits.lastRow_vecMul] at hz
  simp [GeneralLinearGroup.map_apply, lastRow, z] at hz

open Classical in
/-- **The bad-plane weight represents the bad planes** (local-global): for a rational `q`,
`ι_P(ρ(q⁻¹)) = 1 - [qP good]`. -/
theorem badPlaneWeight_rational (q : RationalGL3) :
    badPlaneWeight (rationalGroup q⁻¹) = 1 - goodWeight .plane (QuotientGroup.mk q) := by
  unfold badPlaneWeight goodWeight
  by_cases hg : GoodFlag .plane (QuotientGroup.mk q)
  · rw [ite_eq_left hg, sub_self, ite_eq_right]
    rintro ⟨p, k, hk, hpk⟩
    obtain ⟨γ, hγ⟩ := goodPlane_exists_transporter _ hg
    have hq : (QuotientGroup.mk (γ.val * rational goodPlaneFrame) : Flags .plane) = QuotientGroup.mk q := by
      rw [← hγ]; rfl
    have hp0 : (γ.val * rational goodPlaneFrame)⁻¹ * q ∈ planeParabolic ℚ := QuotientGroup.eq.mp hq
    have hqeq : q = γ.val * rational goodPlaneFrame * ((γ.val * rational goodPlaneFrame)⁻¹ * q) := by
      rw [mul_inv_cancel_left]
    have hinv : (rational goodPlaneFrame)⁻¹ = rational goodPlaneFrame := by
      unfold rational
      rw [← map_inv]
      congr 1
    rw [adelicThreeGroup_rational] at hpk
    set p0 : RationalGL3 := (γ.val * rational goodPlaneFrame)⁻¹ * q with hp0def
    rw [hqeq] at hpk
    simp only [_root_.mul_inv_rev, map_mul, map_inv, hinv] at hpk
    apply goodPlane_ne_mul
      (⟨GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0,
        generalLinearGroup_map_plane (algebraMap ℚ ℚ_[3]) ⟨p0, hp0⟩⟩ * p)
      (k * GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)
      (InLocalThreeLevel_mul hk (map_rationalLevel_level γ))
    rw [Subgroup.coe_mul]
    show _ = (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0 * p.val) *
      (k * GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)
    calc GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rational goodPlaneFrame) =
        GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0 *
          ((GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹ *
            GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rational goodPlaneFrame) *
              (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)⁻¹) *
          GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val := by group
      _ = _ := by
        have hpk' : (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) p0)⁻¹ *
            GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) (rational goodPlaneFrame) *
              (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) γ.val)⁻¹ = p.val * k := by
          rw [mul_assoc]; exact hpk
        rw [hpk']; group
  · rw [ite_eq_right hg, sub_zero, ite_eq_left]
    obtain ⟨parabolic, compact, level, eq⟩ := rational_badPlane_local_support q hg
    exact ⟨parabolic, compact, level, by rw [adelicThreeGroup_rational]; exact eq⟩

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
