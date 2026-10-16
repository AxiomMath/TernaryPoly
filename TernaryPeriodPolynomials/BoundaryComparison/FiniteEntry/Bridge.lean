module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Limit
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBadMain
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.PlaceThree
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.UnitAction

@[expose] public section


/-!
# The literal bad-plane entry integral (lattice route)

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.

Paper: Appendix C entry computation
(about: the unramified factors as lattice sums, the global entry `(1/9) L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`).

The bad-plane finite entry integral at a good-line matrix is computed from the literal lattice calculation
`LatticeCounts.GlobalLimitUncond.global_integral_euler` and the classical section comparisons
`ModelComparison` / `ModelComparisonNeg`, without the representation-theoretic
`entryPlaneIntegral_bad_general` / `integral_planeOpposite_bad`.

* `integral_badRegion_literal`: the integral over the bad region `‖v₁‖₃, ‖v₂‖₃ < 1` at a real point `atInfinity r`.
  The Haar measure of the finite adeles is split as `ℚ₃ × FiniteAwayThree` (`PlaceThree.integral_badRegion_split`);
  the `3`-adic box has measure `1/9` and the integrand is constant on it (integral shifts);
  on `FiniteAwayThree²` the integrand is `globalIntegrand I 1 r`, whose integral is
  `vhValueFull(r, 1) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` for both signs of `det r`; and `vhValueFull(r, 1)` is
  the realization of the vector at `atInfinity r` (`vhModel_eq_full`).
* `integral_planeOpposite_bad_literal`: arbitrary `y = ι(q) · atInfinity r · atFinite κ`
  (`binaryAdelic_rational_real_integral`): the rational factor drops by left `GL₂(ℚ)`-invariance and the integral
  element `κ` is absorbed by the measure-preserving `UnitAction.exists_T_unit`.
* `entryPlaneIntegral_bad_literal`: the equivariance reduction of `REBad5.entryPlaneIntegral_bad_general`
  (Claude Sonnet 5.5), copied with the new base case.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG (blkGL)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.HeckeEigen

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

variable {σ : CuspidalRepresentation}

/-- `ModelComparison.smoothReal` is the realization `entryRz`. -/
theorem smoothReal_eq_entryRz (w : σ.H) (x : BinaryAdelicGL) :
    ModelComparison.smoothReal σ w x = entryRz σ w x := by
  unfold ModelComparison.smoothReal entryRz
  by_cases hw : w ∈ σ.smooth
  · rw [dite_eq_left hw, dite_eq_left hw]
  · rw [dite_eq_right hw, dite_eq_right hw]
    rfl

/-- The finite plane vector of a spherical vector does not depend on a character trivial on the integral units. -/
theorem finitePlaneVector_congr_character (χ : RankOneCharacter) (a b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {v : σ.H} (hv : v ∈ sphericalSubspace σ) (g : FiniteGL) :
    finitePlaneVector σ χ a b g v = finitePlaneVector σ trivialCharacter a b g v := by
  obtain ⟨k₀, hk₀⟩ := finitePlaneParabolic_spec g
  have hp₀ := finitePlaneParabolic_mem g
  have hT : ∀ u : IntegralAdelesˣ, trivialCharacter.toMonoidHom (integralAdeleUnit u) = 1 := fun u => rfl
  rw [finitePlaneVector_eq χ a b hχ hv hp₀ k₀ hk₀, finitePlaneVector_eq trivialCharacter a b hT hv hp₀ k₀ hk₀]
  unfold finitePlaneFactor
  rw [character_finite_eq_one χ hχ]
  rfl

/-- The matrix `L(s,t) = w₀⁻¹ u(s,t)`. -/
theorem LfinGLof_eq (s t : FiniteAdeles) : LfinGLof s t = weyl⁻¹ * lineUnipotent s t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LfinGLof_val, LstR, weyl, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The plane factor of the block embedding of an integral `GL₂` element is `1`. -/
theorem blkGL_integral_factor (χ : RankOneCharacter) (a b : ℂ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    finitePlaneFactor χ a b (blkGL (GeneralLinearGroup.map integralEmbedding k))
      (ShellLitBlockG.blkGL_mem_plane _) = 1 := by
  unfold finitePlaneFactor
  have hc : planeCornerUnit (blkGL (GeneralLinearGroup.map integralEmbedding k))
      (ShellLitBlockG.blkGL_mem_plane _) = 1 := Units.ext rfl
  rw [hc, ShellLitBlockG.planeBlockGL_blkGL, generalLinearGroup_det_map]
  have h1 : TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 :=
    Units.ext rfl
  rw [h1, map_one, finiteAdeleUnit_integral, TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_integralAdeleUnit]
  simp [normPower]

/-- The integral block action on the opposite plane vectors (matrix identity from `exists_T_unit`). -/
theorem translate_planeOpposite (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) (k : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (v v' : FiniteAdeles × FiniteAdeles) (k' : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hmat : blkGL (GeneralLinearGroup.map integralEmbedding k) * planeOppositeStandardMatrix v.1 v.2 =
      planeOppositeStandardMatrix v'.1 v'.2 * GeneralLinearGroup.map integralEmbedding k') :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (finitePlaneVector σ χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec) =
      finitePlaneVector σ χ 0 b (planeOppositeStandardMatrix v'.1 v'.2) vec := by
  have key := finitePlaneVector_mul χ 0 b hχ hsph
    (ShellLitBlockG.blkGL_mem_plane (GeneralLinearGroup.map integralEmbedding k))
    (planeOppositeStandardMatrix v.1 v.2)
  rw [hmat, finitePlaneVector_mul_integral χ 0 b hχ hsph, blkGL_integral_factor,
    ShellLitBlockG.planeBlockGL_blkGL, one_smul] at key
  exact key.symm


/-- The right-hand side `L^{(3)}(h, k-2) / L^{(3)}(h, k-1)` of the global Euler product. -/
def lRatio {k : ℤ} (h : CuspForm levelOne k) : ℂ :=
  LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 2) /
    LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) ((k : ℂ) - 1)

/-- **The literal bad-region integral at a real point**, from `global_integral_euler` at the base point `1`. -/
theorem integral_badRegion_literal {n : ℕ} (I : EichlerInput σ n) (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (r : BinaryRealGL) :
    (∫ v in badRegion, entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (planeOppositeStandardMatrix v.1 v.2) I.vector.val) (atInfinity r) ∂(finiteMeasure.prod finiteMeasure)) =
      (1 / 9 : ℂ) * (lRatio h * σ.realize I.vector (atInfinity r)) := by
  have hsph : I.vector.val ∈ sphericalSubspace σ := I.vector_spherical
  have hsmooth : ∀ (g : FiniteGL), finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I) g I.vector.val ∈ σ.smooth :=
    fun g => finitePlaneVector_smooth χ 0 _ g I.vector.property
  -- Step: planeOpposite -> weyl⁻¹ u(v), shift invariance, place three
  have hplane : ∀ v : FiniteAdeles × FiniteAdeles,
      finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I) (planeOppositeStandardMatrix v.1 v.2) I.vector.val =
      finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I) (weyl⁻¹ * lineUnipotent v.1 v.2) I.vector.val := by
    intro v
    have := finitePlaneVector_entry σ χ (LatticeCounts.GlobalIntegrand.expo I) hχ hsph v 1
    rw [map_one, mul_one] at this
    exact this.symm
  simp_rw [hplane]
  rw [integral_badRegion_split (fun v => entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
      (weyl⁻¹ * lineUnipotent v.1 v.2) I.vector.val) (atInfinity r))]
  · congr 1
    -- the global integral
    have hZ : ∀ w : FinitePlace, LocalAdelic.IntGL w
        (GeneralLinearGroup.map (finiteEvaluation w) (1 : BinaryFiniteGL)).val := fun w => by
      rw [map_one, Units.val_one]
      exact LocalAdelic.intGL_one w
    have hg : (Matrix.GeneralLinearGroup.det r).val ≠ 0 := (GeneralLinearGroup.det r).ne_zero
    have euler := (GlobalLimitUncond.global_integral_euler I h hh hform hk r hg 1 hZ).2
    have e1 : ∀ z : FiniteAwayThree × FiniteAwayThree,
        entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
          (weyl⁻¹ * lineUnipotent z.1.val z.2.val) I.vector.val) (atInfinity r) =
        LatticeCounts.GlobalIntegrand.globalIntegrand I 1 r z := by
      intro z
      unfold LatticeCounts.GlobalIntegrand.globalIntegrand
      rw [ShellLitBlockG.blkGL_one, mul_one, smoothReal_eq_entryRz,
        finitePlaneVector_congr_character χ _ _ hχ hsph]
      show _ = entryRz σ (finitePlaneVector σ trivialCharacter 0 _ (LfinGLof z.1.val z.2.val) I.vector.val) _
      rw [LfinGLof_eq]
    simp_rw [e1]
    rw [euler]
    have e2 : ModelComparisonNeg.vhValueFull (-2 * I.halfWeight) h r 1 =
        σ.realize I.vector (atInfinity r) := by
      have hι : RightTranslation.ιGL placeThree 1 = 1 := Units.ext (by
        show RightTranslation.ιMat placeThree (1 : GeneralLinearGroup (Fin 2) _).val = 1
        rw [Units.val_one]
        exact RightTranslation.ιMat_one placeThree)
      have := ModelComparisonNeg.vhModel_eq_full I h hform placeThree 1 r
      rw [hι] at this
      rw [← this, atFinite_one, map_one]
      show ModelComparison.smoothReal σ I.vector.val (atInfinity r) = _
      rw [ModelComparison.smoothReal_eq_realize σ _ I.vector.property]
    rw [e2]
    have e3 : normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
        (GeneralLinearGroup.det (1 : BinaryFiniteGL))) (LatticeCounts.GlobalIntegrand.expo I) = 1 := by
      rw [map_one]
      have h1 : TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 :=
        Units.ext rfl
      rw [h1]
      simp [normPower]
    rw [e3, one_mul]
    unfold lRatio
    ring
  · intro v u hu1 hu2
    obtain ⟨a1, ha1⟩ := hu1
    obtain ⟨a2, ha2⟩ := hu2
    have hmat : weyl⁻¹ * lineUnipotent (v + u).1 (v + u).2 = weyl⁻¹ * lineUnipotent v.1 v.2 *
        GeneralLinearGroup.map integralEmbedding (lineUnipotent a1 a2) := by
      rw [map_lineUnipotent', Prod.fst_add, Prod.snd_add, lineUnipotent_add, mul_assoc]
      congr 3
      · exact ha1.symm
      · exact ha2.symm
    show entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (weyl⁻¹ * lineUnipotent (v + u).1 (v + u).2) I.vector.val) (atInfinity r) =
      entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (weyl⁻¹ * lineUnipotent v.1 v.2) I.vector.val) (atInfinity r)
    rw [hmat, finitePlaneVector_mul_integral χ 0 _ hχ hsph]


/-- **The literal bad-plane base case.**  The analogue of the representation-theoretic base case
`integral_planeOpposite_bad`, derived from the literal lattice computation `global_integral_euler`
and the classical section comparison, at an arbitrary point `y`. -/
theorem integral_planeOpposite_bad_literal {n : ℕ} (I : EichlerInput σ n) (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (y : BinaryAdelicGL) :
    (∫ v in badRegion, entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (planeOppositeStandardMatrix v.1 v.2) I.vector.val) y ∂(finiteMeasure.prod finiteMeasure)) =
      lRatio h * (1 / 9 : ℂ) * σ.realize I.vector y := by
  obtain ⟨q, r, k, hy⟩ := binaryAdelic_rational_real_integral y
  subst hy
  obtain ⟨T, hTmp, hTbad, hTmat⟩ := exists_T_unit k
  have hsph : I.vector.val ∈ sphericalSubspace σ := I.vector_spherical
  set F : FiniteAdeles × FiniteAdeles → ℂ := fun w => entryRz σ (finitePlaneVector σ χ 0
    (LatticeCounts.GlobalIntegrand.expo I) (planeOppositeStandardMatrix w.1 w.2) I.vector.val) (atInfinity r) with hF
  have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
      entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (planeOppositeStandardMatrix v.1 v.2) I.vector.val)
        (GeneralLinearGroup.map rationalAdele q * atInfinity r *
          atFinite (GeneralLinearGroup.map integralEmbedding k)) = F (T v) := by
    intro v
    have hw := finitePlaneVector_smooth (σ := σ) χ 0 (LatticeCounts.GlobalIntegrand.expo I)
      (planeOppositeStandardMatrix v.1 v.2) I.vector.property
    obtain ⟨k', hk'⟩ := hTmat v
    have step := translate_planeOpposite χ (LatticeCounts.GlobalIntegrand.expo I) hχ hsph k v (T v) k' hk'
    rw [entryRz_of_mem hw, mul_assoc, σ.leftRational q ⟨_, hw⟩ (atInfinity r * atFinite (GeneralLinearGroup.map integralEmbedding k)),
      ← entryRz_of_mem hw, ← entryRz_pi hw, step]
  have shifted : (∫ v in badRegion, F (T v) ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ v in badRegion, F v ∂(finiteMeasure.prod finiteMeasure) := by
    rw [← integral_indicator badRegion_measurable, ← integral_indicator badRegion_measurable]
    have key : ∀ v, badRegion.indicator (fun v => F (T v)) v = (badRegion.indicator F) (T v) := by
      intro v
      by_cases hv : v ∈ badRegion
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((hTbad v).1 hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun hh' => hv ((hTbad v).2 hh'))]
    simp_rw [key]
    exact hTmp.integral_comp' (badRegion.indicator F)
  rw [setIntegral_congr_fun badRegion_measurable (fun v _ => pointwise v), shifted]
  have base := integral_badRegion_literal I χ hχ h hh hform hk r
  have rz : σ.realize I.vector (GeneralLinearGroup.map rationalAdele q * atInfinity r *
      atFinite (GeneralLinearGroup.map integralEmbedding k)) = σ.realize I.vector (atInfinity r) := by
    rw [mul_assoc, σ.leftRational q I.vector, ModelComparison.realize_mul_integral I]
  rw [rz]
  have : (∫ v in badRegion, F v ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ v in badRegion, entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
        (planeOppositeStandardMatrix v.1 v.2) I.vector.val) (atInfinity r) ∂(finiteMeasure.prod finiteMeasure) := rfl
  rw [this, base]
  ring


open Classical in
/-- **The bad-plane entry integral at a finite matrix of the good-line class**, with the base case supplied by
the literal lattice computation.  Copy of the equivariance reduction of `entryPlaneIntegral_bad_general`
(Claude Sonnet 5.5), with `integral_planeOpposite_bad` replaced by
`integral_planeOpposite_bad_literal`. -/
theorem entryPlaneIntegral_bad_literal {n : ℕ} (I : EichlerInput σ n) (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight)
    (f : FiniteGL) (hf : goodLineSet (GeneralLinearGroup.map finiteThree f)) (y : BinaryAdelicGL) :
    entryPlaneIntegral σ χ (LatticeCounts.GlobalIntegrand.expo I) (fun g => badPlaneWeight (atFinite g)) I.vector.val f y =
      lRatio h * (1 / 9 : ℂ) *
        entryRz σ (finiteLineVector σ χ 2 (LatticeCounts.GlobalIntegrand.expo I - 1) f I.vector.val) y := by
  have spherical : I.vector.val ∈ sphericalSubspace σ := I.vector_spherical
  obtain ⟨a, a', d, B, k, h01, hk, hf'⟩ := finite_goodLine_lowerTriangular f hf
  obtain ⟨u₀, u₁, h₀, h₁, hdet⟩ := unit_of_lower_triangular B h01
  have hk' := hk
  obtain ⟨κk, _, hκk⟩ := hk
  subst hf'
  have hw : ∀ p ∈ planeParabolic FiniteAdeles, ∀ g : FiniteGL,
      (fun h : FiniteGL => badPlaneWeight (atFinite h)) (p * g) = (fun h : FiniteGL => badPlaneWeight (atFinite h)) g := by
    intro p hp g
    show badPlaneWeight (atFinite (p * g)) = badPlaneWeight (atFinite g)
    rw [atFinite_mul]
    exact badPlaneWeight_parabolic (atFinite p) (atFinite_mem_plane hp) (atFinite g)
  have plane := entryPlaneIntegral_lineParabolic σ χ (LatticeCounts.GlobalIntegrand.expo I) hχ
    (fun h => badPlaneWeight (atFinite h)) hw
    I.vector.property spherical a a' d B h01 (d⁻¹ * u₀) (d⁻¹ * u₁) (by rw [Units.val_mul, h₀])
    (by rw [Units.val_mul, h₁]) (permMatrix FiniteAdeles * k) y
  have base : ∀ y' : BinaryAdelicGL,
      entryPlaneIntegral σ χ (LatticeCounts.GlobalIntegrand.expo I) (fun h => badPlaneWeight (atFinite h)) I.vector.val
          (permMatrix FiniteAdeles * k) y' =
        lRatio h * (1 / 9 : ℂ) * σ.realize I.vector y' := by
    intro y'
    have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
        badPlaneWeight (atFinite (weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k))) *
          entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
            (weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k)) I.vector.val) y' =
        badRegion.indicator (fun v => entryRz σ (finitePlaneVector σ χ 0 (LatticeCounts.GlobalIntegrand.expo I)
          (planeOppositeStandardMatrix v.1 v.2) I.vector.val) y') v := by
      intro v
      have e : weyl⁻¹ * lineUnipotent v.1 v.2 * (permMatrix FiniteAdeles * k) =
          planeOppositeStandardMatrix v.1 v.2 * k := by
        rw [← weyl_inv_lineUnipotent_perm]
        simp only [mul_assoc]
      rw [e, atFinite_mul, badPlaneWeight_level ⟨k, hk'⟩, badPlaneWeight_planeOpposite, ← hκk,
        finitePlaneVector_mul_integral χ 0 _ hχ spherical]
      by_cases member : v ∈ badRegion
      · have member' : ‖finiteThree v.1‖ < 1 ∧ ‖finiteThree v.2‖ < 1 := member
        rw [Set.indicator_of_mem member, ite_eq_left member']
        ring
      · have member' : ¬ (‖finiteThree v.1‖ < 1 ∧ ‖finiteThree v.2‖ < 1) := member
        rw [Set.indicator_of_notMem member, ite_eq_right member']
        ring
    unfold entryPlaneIntegral
    simp_rw [pointwise]
    rw [integral_indicator badRegion_measurable]
    exact integral_planeOpposite_bad_literal I χ hχ h hh hform hk y'
  have hp := lineUnip_levi_mem a a' d B
  have line : entryRz σ (finiteLineVector σ χ 2 (LatticeCounts.GlobalIntegrand.expo I - 1)
      (lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k) I.vector.val) y =
      finiteLineFactor χ 2 (LatticeCounts.GlobalIntegrand.expo I - 1) (lineUnipotent a a' * lineLevi d B) hp *
        σ.realize I.vector (y * atFinite B) := by
    have e : lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k =
        lineUnipotent a a' * lineLevi d B *
          GeneralLinearGroup.map integralEmbedding (permMatrix IntegralAdeles * κk) := by
      rw [map_mul, permMatrix_map, hκk, mul_assoc]
    rw [e, finiteLineVector_eq χ 2 (LatticeCounts.GlobalIntegrand.expo I - 1) hχ spherical hp
      (permMatrix IntegralAdeles * κk) rfl,
      entryRz_smul (σ.smooth_stable _ _ I.vector.property), entryRz_pi I.vector.property,
      entryRz_of_mem I.vector.property, lineBlockGL_unip_levi]
  have assoc : lineUnipotent a a' * lineLevi d B * permMatrix FiniteAdeles * k =
      lineUnipotent a a' * lineLevi d B * (permMatrix FiniteAdeles * k) := mul_assoc _ _ _
  rw [assoc] at line ⊢
  rw [plane, base, line]
  have factorL : finiteLineFactor χ 2 (LatticeCounts.GlobalIntegrand.expo I - 1) (lineUnipotent a a' * lineLevi d B) hp =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 2 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (LatticeCounts.GlobalIntegrand.expo I - 1) := by
    unfold finiteLineFactor
    rw [lineCornerUnit_unip_levi, lineBlockGL_unip_levi, hdet]
  have factorP : finitePlaneFactor χ 0 (LatticeCounts.GlobalIntegrand.expo I) (planeLevi B d) (planeLevi_mem B d) =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 0 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (LatticeCounts.GlobalIntegrand.expo I) := by
    rw [finitePlaneFactor_planeLevi', hdet]
  rw [factorL, factorP, Complex.real_smul]
  have scalar := scalar_identity χ (LatticeCounts.GlobalIntegrand.expo I) d u₀ u₁
  linear_combination (lRatio h * (1 / 9 : ℂ) * σ.realize I.vector (y * atFinite B)) * scalar

end TernaryPeriodPolynomials.Argument.BoundaryComparison
