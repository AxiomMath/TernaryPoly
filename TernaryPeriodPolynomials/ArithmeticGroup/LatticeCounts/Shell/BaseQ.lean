module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.PointwiseMulti
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotalG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SphericalRight
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermAdelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.OuterRatioProduct

@[expose] public section


/-!
# Local-base block and pointwise identities (route (a), positive determinant)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

`block_multi_loc` is `LfinBlockMulti.block_multi` with the base integrality restricted to `S`. Off `S` the plane factor is `1`, so
the `K`-part of the factorisation is `1` there and the conjugate `(blk g_f)⁻¹ K (blk g_f)` is `1`,
which is integral without any hypothesis on `g_f`. `pointwise_multi_loc` is the pointwise identity
at `atInfinity g∞` with the same restriction.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinFactor
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotalG
open TernaryPeriodPolynomials.Argument.LatticeCounts.SphericalRight
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermAdelic
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform globalOuterLocalRatio
  globalOuterEulerPolynomial)

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBaseQ

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- `ι_v(A)` is the identity at every place other than `v`. -/
theorem evM3_ιGL3_ne (v w : FinitePlace) (hw : w ≠ v)
    (A : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)) :
    evM3 w (ιGL3 v A).val = 1 := by
  rw [ιGL3_val]
  exact evM3_ιMat3_ne v w hw _

/-- `ι_v(A)` evaluates to `A` at `v`. -/
theorem evM3_ιGL3_self (v : FinitePlace) (A : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)) :
    evM3 v (ιGL3 v A).val = A.val := by
  rw [ιGL3_val]
  exact evM3_ιMat3_self v _

/-- **Block lemma, base integral on `S` only.** Same conclusion as `block_multi`; the base `g_f`
is integral at the places of `S`, and `L` is `1` off `S`. -/
theorem block_multi_loc (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (L : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL1 : ∀ w, w ∉ S → evM3 w L.val = 1)
    (gf : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hgf : ∀ w ∈ S, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) gf).val)
    {σ : CuspidalRepresentation} (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then blk2 (P w).val else 1) ∧
      finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (L * blkGL gf) vec =
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (X * gf))) b •
          σ.π (atFinite (X * gf)) vec := by
  have hL : ∀ w, w ∉ S → IntGL3 w (evM3 w L.val) := fun w hw => by
    rw [hL1 w hw]
    exact intGL3_one w
  obtain ⟨Pl, K, hLK, hPl, hPlev, hKev, kI, hkI⟩ := lfin_factor S P κ hP L hS hκ hL
  have hBmem : blkGL gf ∈ planeParabolic FiniteAdeles := blkGL_mem_plane gf
  have hIS : ∀ w, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) K) := by
    intro w
    apply IS3_of_intGL3 w
    have h : IntGL3 w (evM3 w K.val) := by
      rw [hKev w]
      split_ifs with hw
      · exact hκ w hw
      · exact hL w hw
    exact h
  have hIS2 : ∀ w ∈ S, IS3 w (GeneralLinearGroup.map (finiteEvaluation w) (blkGL gf)) := by
    intro w hw
    rw [ev_blkGL]
    exact IS3_blkLocGL w _ (hgf w hw)
  have hKw : ∀ w, w ∉ S → GeneralLinearGroup.map (finiteEvaluation w) K = 1 := by
    intro w hw
    apply Units.ext
    have h := hKev w
    rw [ite_eq_right hw, hL1 w hw] at h
    exact h
  have hK2 : ∀ w, IS3 w
      (GeneralLinearGroup.map (finiteEvaluation w) ((blkGL gf)⁻¹ * K * blkGL gf)) := by
    intro w
    rw [map_mul, map_mul, map_inv]
    by_cases hw : w ∈ S
    · exact IS3_mul w (IS3_mul w (IS3_inv_of w (hIS2 w hw)) (hIS w)) (hIS2 w hw)
    · rw [hKw w hw, mul_one, inv_mul_cancel]
      exact IS3_of_intGL3 w (intGL3_one w)
  obtain ⟨kI2, hkI2⟩ := lift_of_all_IS3 ((blkGL gf)⁻¹ * K * blkGL gf) hK2
  have hp : Pl * blkGL gf ∈ planeParabolic FiniteAdeles :=
    (planeParabolic FiniteAdeles).mul_mem hPl hBmem
  have hg : L * blkGL gf = (Pl * blkGL gf) * GeneralLinearGroup.map integralEmbedding kI2 := by
    rw [hkI2, hLK]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hfin := finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b (fun _ => rfl)
    hsph hp kI2 hg
  refine ⟨planeBlockGL Pl hPl, ?_, ?_⟩
  · intro w
    rw [ev_planeBlockGL w Pl hPl]
    show blk2 (evM3 w Pl.val) = _
    rw [hPlev w]
    simp only [LfinFactor.pick]
    split_ifs with hw
    · rfl
    · exact blk2_one
  · rw [hfin, planeBlockGL_mul hPl hBmem, planeBlockGL_blkGL gf (blkGL_mem_plane gf)]

/-- **Pointwise identity, base integral on `S` only.** Same as `pointwise_multi` with `hgf` on `S`
and `L = 1` off `S`. -/
theorem pointwise_multi_loc (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (L : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL1 : ∀ w, w ∉ S → evM3 w L.val = 1)
    (gf : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hgf : ∀ w ∈ S, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) gf).val)
    (b : ℂ) (gInf : BinaryRealGL) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then blk2 (P w).val else 1) ∧
      smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (L * blkGL gf)
          I.vector.val) (atInfinity gInf) =
        ((∏ w ∈ S, Complex.exp (b * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) *
          normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
            (GeneralLinearGroup.det gf)) b) *
          vhValueFull (-2 * I.halfWeight) h gInf (X * gf) := by
  obtain ⟨X, hX, heq⟩ := block_multi_loc S P κ hP L hS hκ hL1 gf hgf b
    (vec := I.vector.val) (fun kk => I.vector_spherical kk)
  refine ⟨X, hX, ?_⟩
  rw [heq, normPower_det_mul_split S X gf P hX b,
    smoothReal_smul_of_mem σ _ (σ.smooth_stable _ _ I.vector.property), smul_eq_mul,
    vhModel_eq_full_gen I h hform (X * gf) gInf]


/-! ### GL₂ integral lift and right invariance under `ι_q(gp⁻¹)` -/

/-- Evaluation of a finite-adelic `2 × 2` matrix at `w`. -/
def evM2 (w : FinitePlace) (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) :
    Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
  M.map (finiteEvaluation w)

theorem ext_of_evM2 {A B : Matrix (Fin 2) (Fin 2) FiniteAdeles}
    (h : ∀ w : FinitePlace, evM2 w A = evM2 w B) : A = B :=
  Matrix.ext fun i j => RestrictedProduct.ext _ _ fun w => congrFun (congrFun (h w) i) j

/-- An element of `GL₂(𝔸_f)` which is `GL₂(ℤ_w)` at every place lifts to `GL₂(𝔸_f^∞)`. -/
theorem lift_gl2_of_IntGL (g : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hX : ∀ w : FinitePlace, IntGL w (evM2 w g.val)) :
    ∃ gI : GeneralLinearGroup (Fin 2) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding gI = g := by
  let N : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j w => ⟨(evM2 w g.val) i j, (hX w).2.1 i j⟩
  let Ni : Matrix (Fin 2) (Fin 2) IntegralAdeles :=
    fun i j w => ⟨(evM2 w g.val)⁻¹ i j, (hX w).2.2 i j⟩
  have hevP : ∀ w, evM2 w (N.map integralEmbedding) = evM2 w g.val :=
    fun w => Matrix.ext fun _ _ => rfl
  have hevQ : ∀ w, evM2 w (Ni.map integralEmbedding) = (evM2 w g.val)⁻¹ :=
    fun w => Matrix.ext fun _ _ => rfl
  have hPQ : (N.map integralEmbedding) * (Ni.map integralEmbedding) = 1 := by
    apply ext_of_evM2
    intro w
    have hmul : evM2 w ((N.map integralEmbedding) * (Ni.map integralEmbedding)) =
        evM2 w (N.map integralEmbedding) * evM2 w (Ni.map integralEmbedding) := by
      unfold evM2
      exact Matrix.map_mul
    rw [hmul, hevP w, hevQ w, Matrix.mul_nonsing_inv _ (hX w).1]
    unfold evM2
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hQP : (Ni.map integralEmbedding) * (N.map integralEmbedding) = 1 := by
    apply ext_of_evM2
    intro w
    have hmul : evM2 w ((Ni.map integralEmbedding) * (N.map integralEmbedding)) =
        evM2 w (Ni.map integralEmbedding) * evM2 w (N.map integralEmbedding) := by
      unfold evM2
      exact Matrix.map_mul
    rw [hmul, hevP w, hevQ w, Matrix.nonsing_inv_mul _ (hX w).1]
    unfold evM2
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hNNi : N * Ni = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (N * Ni).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hNiN : Ni * N = 1 := by
    apply Matrix.map_injective integralEmbedding_injective
    show (Ni * N).map integralEmbedding = (1 : Matrix _ _ IntegralAdeles).map integralEmbedding
    rw [Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  let gI : GeneralLinearGroup (Fin 2) IntegralAdeles := ⟨N, Ni, hNNi, hNiN⟩
  exact ⟨gI, Units.ext (ext_of_evM2 fun w => hevP w)⟩

/-- **Right invariance under `ι_q(gp⁻¹)`.** For `gp ∈ GL₂(ℚ_q)` integral at `q`, the value at
`W · ι_q(gp⁻¹)` equals the value at `W`. -/
theorem vh_right_iota (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (W : BinaryFiniteGL) (q : FinitePlace)
    (gp : GeneralLinearGroup (Fin 2) (q.adicCompletion ℚ)) (hgI : IntGL q gp.val) :
    vhValueFull (-2 * I.halfWeight) h gInf (W * ιGL q gp⁻¹) = vhValueFull (-2 * I.halfWeight) h gInf W := by
  have hX : ∀ w : FinitePlace, IntGL w (evM2 w (ιGL q gp⁻¹).val) := by
    intro w
    by_cases hw : w = q
    · subst hw
      have hev : evM2 w (ιGL w gp⁻¹).val = (gp⁻¹).val := by
        unfold evM2
        exact evM_ιGL_self w gp⁻¹
      have hinv : (gp⁻¹).val = gp.val⁻¹ := Matrix.coe_units_inv gp
      rw [hev]
      refine ⟨(Matrix.isUnit_iff_isUnit_det _).mp (gp⁻¹).isUnit, ?_, ?_⟩
      · rw [hinv]
        exact hgI.2.2
      · rw [hinv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp gp.isUnit)]
        exact hgI.2.1
    · have hev : evM2 w (ιGL q gp⁻¹).val = 1 := by
        unfold evM2
        exact evM_ιGL_ne q w hw gp⁻¹
      rw [hev]
      exact intGL_one w
  obtain ⟨κ, hκ⟩ := lift_gl2_of_IntGL (ιGL q gp⁻¹) hX
  rw [← hκ]
  exact vhValueFull_mul_integral_right I h hform gInf W κ

/-- The literal local ratio `c_p` (written with `zpow` in the literal) is `globalOuterLocalRatio`. -/
theorem literal_ratio_eq (k : ℤ) (a : ℂ) (p : Nat.Primes) :
    (1 - a * ((p : ℕ) : ℂ) ^ (1 - k) + ((p : ℕ) : ℂ) ^ (1 - k)) /
        (1 - a * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k)) =
      globalOuterLocalRatio k a p := by
  unfold globalOuterLocalRatio globalOuterEulerPolynomial
  have e1 : ((p.val : ℕ) : ℂ) ^ (-(((k : ℤ) : ℂ) - 1)) = ((p : ℕ) : ℂ) ^ (1 - k) := by
    rw [← Complex.cpow_intCast]
    congr 1
    push_cast
    ring
  have e2 : ((p.val : ℕ) : ℂ) ^ (((k : ℤ) : ℂ) - 1 - 2 * (((k : ℤ) : ℂ) - 1)) =
      ((p : ℕ) : ℂ) ^ (1 - k) := by
    rw [← Complex.cpow_intCast]
    congr 1
    push_cast
    ring
  have e3 : ((p.val : ℕ) : ℂ) ^ (-(((k : ℤ) : ℂ) - 2)) = ((p : ℕ) : ℂ) ^ (2 - k) := by
    rw [← Complex.cpow_intCast]
    congr 1
    push_cast
    ring
  have e4 : ((p.val : ℕ) : ℂ) ^ (((k : ℤ) : ℂ) - 1 - 2 * (((k : ℤ) : ℂ) - 2)) =
      ((p : ℕ) : ℂ) ^ (3 - k) := by
    rw [← Complex.cpow_intCast]
    congr 1
    push_cast
    ring
  rw [e1, e2, e3, e4]

/-- **Lemma Q (literal form, `0 < det g∞`).** The integral of the literal local shell integrand
over `ℚ_p²` against the Haar measure is `normPower(det W) (k/2) · vh(g∞, W) · c_p`, for a base point
`W` integral at `v`. This is `local_integral_literal_uncondG` with `gp = ev_v W`, the right
invariance under `ι_v(gp⁻¹)`, and `literal_ratio_eq`. -/
theorem lemmaQ_literal (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (W : BinaryFiniteGL)
    (hW : IntGL v (GeneralLinearGroup.map (finiteEvaluation v) W).val) :
    ∫ z, shellIntegrandG v I W gInf z ∂((finitePadicMeasure v).prod (finitePadicMeasure v)) =
      normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
          (GeneralLinearGroup.det W)) (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf W *
        globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h (p : ℕ)) p := by
  obtain ⟨-, heq⟩ := local_integral_literal_uncondG I (-2 * I.halfWeight) rfl hk h hh hform p v hv
    gInf hgInf W (GeneralLinearGroup.map (finiteEvaluation v) W) rfl hW
  rw [heq, vh_right_iota I h hform gInf W v _ hW, literal_ratio_eq]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBaseQ

end
