module

public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.Normalization

@[expose] public section


/-!
# The finite entry identity from the literal lattice calculation

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.

Paper: Appendix C entry computation
(about).

`paper_finite_entry`: `FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad` for the entry datum `S` with
a compatible Eichler input `I`.  The value clause is derived from
`LatticeCounts.GlobalLimitUncond.global_integral_euler` and the classical section comparisons
(`ModelComparison`, `ModelComparisonNeg`, both signs of `det g∞`), through `Bridge.entryPlaneIntegral_bad_literal`.

Accounting.
* Haar measure: `finiteMeasure` on `𝔸_f` splits as `normalizedLocalThreeMeasure ⊗ finiteAwayThreeMeasure`
  (`PlaceThree.integral_badRegion_split`).
* Place three: the bad-plane weight restricts to the box `‖s‖₃, ‖t‖₃ < 1` of measure `(1/3)² = 1/9`, on which the
  integrand is constant because the shifts are integral; this is the factor `1/9` of `S.rBad = S.value * (1/9)`.
* Integral base: the good-line orbit reduction `g ↦ perm·k` (copied equivariance of `REBad5`) leaves the base
  case at an arbitrary point `y = ι(q) · atInfinity r · atFinite κ`; `global_integral_euler` is applied at the
  base point `Z = 1` (integral at every place, including `3`), the rational factor is removed by left
  `GL₂(ℚ)`-invariance and `κ ∈ GL₂(Ẑ)` by `UnitAction.exists_T_unit`.
* Scalars: the normalized eigenform `S.form` realizes the Eichler vector only up to the nonzero scalar
  `c = a₁(classicalFormOfEichlerInput I)`; the rescaled Eichler input of `Normalization` has the exact
  realization, and both sides of the identity are linear in the vector, so `c` cancels and the scalar is the
  printed `S.rBad = S.value · (1/9)` with `S.value = L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` for `h = S.form`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.TwistedSource

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

variable {σ : CuspidalRepresentation}

theorem finitePlaneVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ) (v : σ.H) :
    finitePlaneVector σ χ a b g (c • v) = c • finitePlaneVector σ χ a b g v := by
  unfold finitePlaneVector
  rw [map_smul, smul_comm]

theorem finiteLineVector_smul (χ : RankOneCharacter) (a b : ℂ) (g : FiniteGL) (c : ℂ) (v : σ.H) :
    finiteLineVector σ χ a b g (c • v) = c • finiteLineVector σ χ a b g v := by
  unfold finiteLineVector
  rw [map_smul, smul_comm]

theorem entryPlaneIntegral_smul (χ : RankOneCharacter) (b : ℂ) (w : FiniteGL → ℂ) {v : σ.H}
    (hv : v ∈ σ.smooth) (c : ℂ) (f : FiniteGL) (y : BinaryAdelicGL) :
    entryPlaneIntegral σ χ b w (c • v) f y = c * entryPlaneIntegral σ χ b w v f y := by
  unfold entryPlaneIntegral
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [finitePlaneVector_smul, entryRz_smul (finitePlaneVector_smooth χ 0 b _ hv)]
  ring

/-- `lRatio` only depends on the underlying function of the form and the weight. -/
theorem lRatio_congr {k k' : ℤ} (hk : k = k') (h : CuspForm levelOne k) (h' : CuspForm levelOne k')
    (hf : (⇑h : UpperHalfPlane → ℂ) = ⇑h') : lRatio h = lRatio h' := by
  subst hk
  have : h = h' := DFunLike.coe_injective hf
  subst this
  rfl

/-- **The bad-plane entry integral at a good-line matrix, for the entry datum.** -/
theorem entryPlaneIntegral_bad_entry {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (f : FiniteGL) (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) (y : BinaryAdelicGL) :
    entryPlaneIntegral D.cusp D.chi (((n : ℂ) + 3) / 2) (fun g => badPlaneWeight (atFinite g)) S.vector.val f y =
      S.value * (1 / 9 : ℂ) *
        entryRz D.cusp (finiteLineVector D.cusp D.chi 2 (((n : ℂ) + 3) / 2 - 1) f S.vector.val) y := by
  obtain ⟨I', hIw, hIv, h, hh, hform, hformS⟩ := exists_normalized_eigenform_rescaled S I hw hv
  have hc := fourierCoeff_classicalFormOfEichlerInput_one_ne_zero S I hw hv
  set c := fourierCoeff (classicalFormOfEichlerInput I) 1 with hcdef
  have hk : 6 < -2 * I'.halfWeight := by
    rw [hIw]
    exact entry_weight_gt_six S I hw hv
  have lit := entryPlaneIntegral_bad_literal I' D.chi S.hχ h hh hform hk f hf y
  have hexpo : LatticeCounts.GlobalIntegrand.expo I' = ((n : ℂ) + 3) / 2 := by
    unfold LatticeCounts.GlobalIntegrand.expo
    rw [hIw, hw]
    have := S.weight
    have h2 : (-2 * S.halfWeight : ℤ) = (n : ℤ) + 3 := by omega
    rw [h2]
    push_cast
    ring
  have hvec : I'.vector.val = c⁻¹ • S.vector.val := by
    rw [hIv, hv, Submodule.coe_smul]
  have hvalue : lRatio h = S.value := by
    have hk2 : -2 * I'.halfWeight = -2 * S.halfWeight := by rw [hIw, hw]
    rw [lRatio_congr hk2 h S.form hformS]
    exact (value_eq_LRatio S).symm
  rw [hexpo, hvec, entryPlaneIntegral_smul D.chi _ _ S.vector.property, finiteLineVector_smul,
    entryRz_smul (finiteLineVector_smooth D.chi _ _ _ S.vector.property), hvalue] at lit
  refine mul_left_cancel₀ (inv_ne_zero hc) (lit.trans ?_)
  ring

open Classical in
/-- **The finite entry identity from the literal lattice calculation (R2).**
The value clause is derived from `global_integral_euler` and the classical section comparisons
(`Bridge.entryPlaneIntegral_bad_literal`); none of `badPlaneEntryIdentity`, `badPlaneEntryIdentity_of_support`,
`entryPlaneIntegral_bad_general`, `integral_planeOpposite_bad` is used. -/
theorem paper_finite_entry {n : ℕ} (D : InducingData n)
    (S : SphericalEntryData D) (I : EichlerInput D.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    FiniteEntryIdentity D badPlaneWeight goodLineWeight S.F S.rBad := by
  intro g hg x
  have hgood := goodLineWeight_goodLineSet hg
  have convergent := S.exponent_gt
  have integrand : ∀ (v : FiniteAdeles × FiniteAdeles) (z : ℂ),
      badPlaneWeight (finiteEntryElement v g) *
        (cF D (finiteEntryElement v g) * S.F (x * bF (finiteEntryElement v g)) z) =
      badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g)) *
        planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
          (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z := by
    intro v z
    have weight : badPlaneWeight (finiteEntryElement v g) =
        badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g)) := by
      apply badPlaneWeight_finite
      rw [finiteGroup_entryElement, finiteGroup_atFinite]
    rw [weight]
    congr 1
    exact (cF_mul_F_eq_planeCoeff D S.halfWeight S.vector x (finiteEntryElement v g) z).trans
      (by rw [finiteGroup_entryElement])
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [integrand]
    exact ((badPlaneWeight_radical_measurable (finiteGroup g) hgood).comp measurable_fst).mul
      (planeCoeff_measurable D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical x (finiteGroup g))
  · intro Z hZ hZ'
    obtain ⟨φ, hφ, bound⟩ := planeCoeff_majorant D.cusp D.chi _ S.halfWeight S.hχ S.vector S.spherical
      convergent x (finiteGroup g) Z hZ hZ'
    refine ⟨φ, hφ, fun v z hz => ?_⟩
    rw [integrand, norm_mul]
    calc ‖badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g))‖ *
          ‖planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
            (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z‖
        ≤ 1 * φ v := mul_le_mul (badPlaneWeight_norm_le _) (bound v z hz) (norm_nonneg _) zero_le_one
      _ = φ v := one_mul _
  · intro z _
    simp_rw [integrand]
    have lhs : (∫ v : FiniteAdeles × FiniteAdeles, badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 *
        finiteGroup g)) * planeCoeff D.cusp D.chi (((n : ℂ) + 3) / 2) S.halfWeight S.vector x
          (weyl⁻¹ * lineUnipotent v.1 v.2 * finiteGroup g) z ∂(finiteMeasure.prod finiteMeasure)) =
        ((z.im ^ S.halfWeight : ℝ) : ℂ) * entryPlaneIntegral D.cusp D.chi (((n : ℂ) + 3) / 2)
          (fun h => badPlaneWeight (atFinite h)) S.vector.val (finiteGroup g)
          (x * atInfinity (sectionMatrix z)) := by
      simp_rw [planeCoeff_eq]
      unfold entryPlaneIntegral
      rw [← integral_const_mul]
      congr 1
      funext v
      ring
    rw [lhs, entryPlaneIntegral_bad_entry S I hw hv (finiteGroup g) hgood]
    unfold SphericalEntryData.rBad SphericalEntryData.F
    rw [cFLine_mul_F_eq_lineCoeff]
    have : (((n : ℂ) + 3) / 2 - 1) = TernaryPeriodPolynomials.SourceConstruction.lineBeta n := by
      unfold TernaryPeriodPolynomials.SourceConstruction.lineBeta; ring
    rw [this, lineCoeff_eq]
    ring

end TernaryPeriodPolynomials.Argument.BoundaryComparison
