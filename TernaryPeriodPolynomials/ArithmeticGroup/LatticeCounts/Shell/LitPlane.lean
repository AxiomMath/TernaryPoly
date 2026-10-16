module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitGL
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.PlaneSpecialize
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.ModelComparisonNeg

@[expose] public section


/-!
# The literal shell integrand at the plane section (part 3b)

For `z = (s,t)` with `max(‖s‖,‖t‖) = p^r` and a `K0Spec` datum `(k, A)`, the element `ι_v(L(z))`
factors as `ι_v(P) · ι_v(k⁻¹)` with `P` in the plane parabolic and `ι_v(k⁻¹)` integral
(`ShellLitGL`). Both `finitePlaneVector` values at `ι_v(L(z))` and `ι_v(P)` reduce to the same
block expression (`finitePlaneVector_eq_block`), so the plane section at `ι_v(L(z))` equals the
`p^{-r}`-scaled `σ.π(ι_v A)`-vector (`finitePlaneVector_K0_explicit`).
The real-valued integrand `smoothReal σ (...) (atInfinity g∞)` is then `p^{-r k/2}` times the
model value `vhValueFull (-2·halfWeight)` at `ι_v(A)` (`vhModel_eq_full`), with `b = k/2`.

Formalized by Claude Haiku 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers (cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (Lst toQ K0Spec)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlane

section Plane

variable {σ : CuspidalRepresentation} (v : FinitePlace)
  [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- Integral-factor form: `ι_v(L(z)) = ι_v(P(z,k)) · map integralEmbedding kI` for the given `k`. -/
theorem iota_LstV_eq (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) (hk : k.det = 1) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      ιGL3 v (LstV v z) = ιGL3 v (PV v z k hk) * GeneralLinearGroup.map integralEmbedding kI := by
  obtain ⟨kI, hkI⟩ := kInv_lift v k hk
  refine ⟨kI, ?_⟩
  rw [hkI, LstV, LstGL_eq_PGL_mul_inv z.1 z.2 k hk, map_mul, ιGL3_mul]
  rfl

/-- The plane element `P(z,k)` lies in the plane parabolic, given the `K0Spec` datum. -/
theorem PV_mem_plane {r : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A) :
    PV v z k hK.1 ∈ planeParabolic (v.adicCompletion ℚ) :=
  mem_plane_of_K0 v hK (PV v z k hK.1) (fun _ _ => rfl)

/-- **The plane section at `ι_v(L(z))`.** The value is the `p^{-r}`-normalised section at the
block `Ablk` of `ι_v(P(z,k))`, with `b` arbitrary. -/
theorem finitePlaneVector_iota_LstV {r : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])))
    (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) :
    finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (ιGL3 v (LstV v z)) vec =
      Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) •
        σ.π (atFinite (ιGL v Ablk)) vec := by
  obtain ⟨kI, hg⟩ := iota_LstV_eq v z k hK.1
  have hmem := PV_mem_plane v hK
  have hp : ιGL3 v (PV v z k hK.1) ∈ planeParabolic FiniteAdeles := ιGL3_mem_plane v hmem
  have hχ : ∀ u : IntegralAdelesˣ,
      GeneralEisenstein.trivialCharacter.toMonoidHom (integralAdeleUnit u) = 1 :=
    fun _ => rfl
  have e1 := finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b hχ hsph hp kI hg
  have hg1 : ιGL3 v (PV v z k hK.1) =
      ιGL3 v (PV v z k hK.1) * GeneralLinearGroup.map integralEmbedding 1 := by simp
  have e2 := finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b hχ hsph hp 1 hg1
  have e3 := finitePlaneVector_K0_explicit v hK (PV v z k hK.1) (fun _ _ => rfl) Ablk hA b hsph
  exact e1.trans (e2.symm.trans e3)

end Plane

section Scalars

/-- `smoothReal` is linear on smooth vectors. -/
theorem smoothReal_smul_of_mem (σ : CuspidalRepresentation) (c : ℂ) {w : σ.H}
    (hw : w ∈ σ.smooth) (g : BinaryAdelicGL) :
    smoothReal σ (c • w) g = c • smoothReal σ w g := by
  have hcw : c • w ∈ σ.smooth := σ.smooth.smul_mem c hw
  unfold smoothReal
  rw [dite_eq_left hcw, dite_eq_left hw]
  have e : (⟨c • w, hcw⟩ : σ.smooth) = c • (⟨w, hw⟩ : σ.smooth) := Subtype.ext rfl
  rw [e, map_smul]
  rfl

/-- The scalar `exp(b · log((p^r)⁻¹))` with `b = k/2` is the real power `p^{-r k/2}`. -/
theorem exp_shell_eq_rpow (p : ℕ) [Fact p.Prime] (r : ℕ) (k : ℤ) :
    Complex.exp (((k : ℂ) / 2) * (Real.log (((p : ℝ) ^ r)⁻¹) : ℂ)) =
      (((p : ℝ) ^ (-(r : ℝ) * ((k : ℝ) / 2)) : ℝ) : ℂ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  rw [Real.rpow_def_of_pos hp0, Complex.ofReal_exp]
  congr 1
  rw [Real.log_inv, Real.log_pow]
  push_cast
  ring

end Scalars

section Integrand

variable {σ : CuspidalRepresentation} {n : ℕ} (v : FinitePlace)
  [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- **The literal shell integrand at `z`.** With `b = k/2`, `k = -2·halfWeight` the weight of `h`,
the real value `smoothReal` of the plane section at `ι_v(L(z))` is `p^{-r k/2}` times the model
value `vhValueFull k h g∞ (ι_v A)`, for any `K0Spec` datum `(k, A)` of `z` and any block `Ablk`
of `A`. -/
theorem integrand_eq_vhValueFull (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) {r : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))) :
    smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0
        (((-2 * I.halfWeight : ℤ) : ℂ) / 2) (ιGL3 v (LstV v z)) I.vector.val) (atInfinity gInf) =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(r : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        vhValueFull (-2 * I.halfWeight) h gInf (ιGL v Ablk) := by
  have hsph : I.vector.val ∈ sphericalSubspace σ := fun kk => I.vector_spherical kk
  rw [finitePlaneVector_iota_LstV v hK Ablk hA _ hsph,
    smoothReal_smul_of_mem σ _ (σ.smooth_stable _ _ I.vector.property),
    exp_shell_eq_rpow (Rat.HeightOneSpectrum.primesEquiv v).val r (-2 * I.halfWeight),
    vhModel_eq_full I h hform v Ablk gInf, smul_eq_mul]

end Integrand

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlane

end
