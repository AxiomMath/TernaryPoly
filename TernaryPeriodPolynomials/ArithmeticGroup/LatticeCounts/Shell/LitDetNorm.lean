module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlaneG

@[expose] public section


/-!
# Unit-norm transport for integral `GL₂` determinants (generalised local integral)

For `gp ∈ GL₂(K_v)` with `gp` and `gp⁻¹` integral at `v`, the determinant is a unit of `O_v`
whose inverse is also in `O_v`, so its finite-adelic norm is `1`. This removes the discrepancy
between `det(g_f · ι_v(gp)⁻¹)` and `det g_f` in `ShellLitPlaneG.finitePlaneVector_blk_iota_LstV`.

Formalized by Claude Haiku 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (Lst toQ K0Spec)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finiteCompletionPadicEquiv finiteAtPlaceUnit finiteAtPadicUnit)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitDetNorm

section DetNorm

variable (v : FinitePlace)

/-- The two copies of `finiteAdeleUnit` (`Norm` and `SphericalDetection.Helpers`) agree. -/
theorem norm_finiteAdeleUnit_eq (u : FiniteAdelesˣ) :
    Norm.finiteAdeleUnit u = TernaryPeriodPolynomials.SphericalDetection.Helpers.finiteAdeleUnit u :=
  rfl

/-- The place-`v` unit embedding factors through the `ℚ_p`-unit embedding. -/
theorem finiteAtPlaceUnit_eq_padic (u : (v.adicCompletion ℚ)ˣ)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] :
    finiteAtPlaceUnit v u = finiteAtPadicUnit v
      (Units.map (finiteCompletionPadicEquiv v).toMonoidHom u) := by
  unfold finiteAtPadicUnit
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  simp

/-- Norm of the place-`v` embedding of an integral unit with integral inverse is `1`. -/
theorem adeleNorm_finiteAtPlaceUnit_of_integral (u : (v.adicCompletion ℚ)ˣ)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (h1 : ‖pe v u.val‖ ≤ 1) (h2 : ‖pe v (u⁻¹).val‖ ≤ 1) :
    (adeleNorm (Norm.finiteAdeleUnit (finiteAtPlaceUnit v u)) : ℝ) = 1 := by
  rw [norm_finiteAdeleUnit_eq, finiteAtPlaceUnit_eq_padic v u,
    TernaryPeriodPolynomials.SphericalDetection.Helpers.adeleNorm_finiteAtPadicUnit]
  have hA : ‖(Units.map (finiteCompletionPadicEquiv v).toMonoidHom u).val‖ ≤ 1 := h1
  have hB : ‖(Units.map (finiteCompletionPadicEquiv v).toMonoidHom u)⁻¹.val‖ ≤ 1 := by
    rw [← map_inv (Units.map (finiteCompletionPadicEquiv v).toMonoidHom) u]
    exact h2
  have hprod : ‖(Units.map (finiteCompletionPadicEquiv v).toMonoidHom u).val‖ *
      ‖(Units.map (finiteCompletionPadicEquiv v).toMonoidHom u)⁻¹.val‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, norm_one]
  have hge : 1 ≤ ‖(Units.map (finiteCompletionPadicEquiv v).toMonoidHom u).val‖ := by
    have := mul_le_mul_of_nonneg_left hB
      (norm_nonneg (Units.map (finiteCompletionPadicEquiv v).toMonoidHom u).val)
    linarith
  exact le_antisymm hA hge

/-- `normPower` of an integral place-`v` unit is `1`. -/
theorem normPower_finiteAtPlaceUnit_of_integral (u : (v.adicCompletion ℚ)ˣ)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (h1 : ‖pe v u.val‖ ≤ 1) (h2 : ‖pe v (u⁻¹).val‖ ≤ 1) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (finiteAtPlaceUnit v u)) b = 1 := by
  unfold normPower
  rw [adeleNorm_finiteAtPlaceUnit_of_integral v u h1 h2]
  simp

theorem det_mem_OS_of_entries (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hX : ∀ i j, X i j ∈ OS v) : X.det ∈ OS v := by
  rw [Matrix.det_fin_two]
  exact (OS v).sub_mem ((OS v).mul_mem (hX 0 0) (hX 1 1)) ((OS v).mul_mem (hX 0 1) (hX 1 0))

/-- For integral `gp` (with integral inverse), `det gp` and `(det gp)⁻¹` have norm at most `1`. -/
theorem det_norm_le_one (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgI : IntGL v gp.val) :
    ‖pe v (GeneralLinearGroup.det gp).val‖ ≤ 1 ∧ ‖pe v (GeneralLinearGroup.det gp)⁻¹.val‖ ≤ 1 := by
  refine ⟨(mem_iff_norm v _).1 (det_mem_OS_of_entries v _ hgI.2.1), ?_⟩
  rw [← map_inv GeneralLinearGroup.det gp]
  have e : (GeneralLinearGroup.det gp⁻¹).val = (gp.val⁻¹).det := by
    rw [← Matrix.coe_units_inv]
    rfl
  rw [e]
  exact (mem_iff_norm v _).1 (det_mem_OS_of_entries v _ hgI.2.2)

/-- Replacing `det(g_f · ι_v(gp)⁻¹)` by `det g_f`: the place-`v` factor has `normPower = 1`. -/
theorem normPower_det_iota_inv [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgI : IntGL v gp.val) (b : ℂ) :
    normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (gf * ιGL v gp⁻¹))) b =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) b := by
  have hd := det_norm_le_one v gp hgI
  have e : GeneralLinearGroup.det gp⁻¹ = (GeneralLinearGroup.det gp)⁻¹ :=
    map_inv GeneralLinearGroup.det gp
  have h1 : ‖pe v (GeneralLinearGroup.det gp⁻¹).val‖ ≤ 1 := by
    rw [e]
    exact hd.2
  have h2 : ‖pe v (GeneralLinearGroup.det gp⁻¹)⁻¹.val‖ ≤ 1 := by
    rw [e, inv_inv]
    exact hd.1
  rw [map_mul GeneralLinearGroup.det, det_ιGL, finiteAdeleUnit_mul,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
    normPower_finiteAtPlaceUnit_of_integral v _ h1 h2, mul_one]

end DetNorm

section Plane

/-- **Plane section at a general base point, scalar at `det g_f`.** Same as
`ShellLitPlaneG.finitePlaneVector_blk_iota_LstV`, with the scalar `normPower(det g_f)`. -/
theorem finitePlaneVector_blk_iota_LstV_det {σ : CuspidalRepresentation} (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] {r : ℕ}
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])))
    (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (ιGL3 v (LstV v z) * blkGL gf) vec =
      (Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf)) b) •
        σ.π (atFinite (ιGL v Ablk * (gf * ιGL v gp⁻¹))) vec := by
  rw [finitePlaneVector_blk_iota_LstV v hK Ablk hA b hsph gf gp hgp hgI,
    normPower_det_iota_inv v gf gp hgI b]

end Plane

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitDetNorm

end
