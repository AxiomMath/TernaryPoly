module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.GL3
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.PlaneSection
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicAdelicNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceIntegralEmbedding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceMatrixEmbedding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceUnitEmbedding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlacePadicCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary

@[expose] public section


/-!
# Specializing the plane section at `ι_v(L(s,t) k₀)` (part 3a)

For `k₀` from `SeedK0.exists_k0`, the local element `P = L(s,t) k₀` (transported to `v.adicCompletion ℚ`)
lies in the upper plane parabolic, and `ι_v(P)` is the plane-section point with `k = 1`.  The plane section
equals `normPower(det A) • σ.π(ι_v A)` with `A` the `GL₂` block of `P`, and `det A = p^r`.

Formalized by Claude Haiku 5.5.  The local point is `ι_v(L k₀)` at the place
`v` with identity elsewhere; the global rational `L(s,t)` is not multiplied in here (its `GL₃(ℚ)`
equivariance is a separate step).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (Lst toQ K0Spec norm_pr)
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (planeBlockGL_val_apply)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize

variable {σ : CuspidalRepresentation}

/-- The `GL₂` local embedding is the finite-place embedding `finiteAtPlaceGL`. -/
theorem ιGL_eq_finiteAtPlaceGL (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ιGL v A = finiteAtPlaceGL 2 v A := by
  apply finiteGeneralLinearGroup_ext
  intro w
  by_cases hw : w = v
  · rw [hw, finiteAtPlaceGL_same 2 v A]
    apply Units.ext
    exact evM_ιMat_self v A.val
  · rw [finiteAtPlaceGL_away 2 v A w hw]
    apply Units.ext
    exact evM_ιMat_ne v w hw A.val

/-- The determinant of `ι_v(A)` is the place-`v` unit `det A`. -/
theorem det_ιGL (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup.det (ιGL v A) = finiteAtPlaceUnit v (GeneralLinearGroup.det A) := by
  rw [ιGL_eq_finiteAtPlaceGL, finiteAtPlaceGL_det]

/-- Membership of the transported `L(s,t) k₀` in the plane parabolic. -/
theorem mem_plane_of_K0 (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    {r : ℕ} {s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r s t k A)
    (P : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ))
    (hP : ∀ i j, P.val i j = (finiteCompletionPadicEquiv v).symm ((Lst s t * toQ k) i j)) :
    P ∈ planeParabolic (v.adicCompletion ℚ) := by
  have hrow0 : (Lst s t * toQ k) 2 0 = 0 := hK.2.2.2.2.1
  have hrow1 : (Lst s t * toQ k) 2 1 = 0 := hK.2.2.2.2.2.1
  exact ⟨by rw [hP, hrow0, map_zero], by rw [hP, hrow1, map_zero]⟩

/-- **The plane section at `ι_v(L(s,t) k₀)`.** -/
theorem finitePlaneVector_K0 (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    {r : ℕ} {s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r s t k A)
    (P : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ))
    (hP : ∀ i j, P.val i j = (finiteCompletionPadicEquiv v).symm ((Lst s t * toQ k) i j))
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))) 
    (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) :
    finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (ιGL3 v P) vec =
      normPower (Norm.finiteAdeleUnit (finiteAtPlaceUnit v (GeneralLinearGroup.det Ablk))) b •
        σ.π (atFinite (ιGL v Ablk)) vec := by
  have hmem : P ∈ planeParabolic (v.adicCompletion ℚ) := mem_plane_of_K0 v hK P hP
  have hp : ιGL3 v P ∈ planeParabolic FiniteAdeles := ιGL3_mem_plane v hmem
  have hg : ιGL3 v P = ιGL3 v P * GeneralLinearGroup.map integralEmbedding 1 := by simp
  have hblk : planeBlockGL P hmem = Ablk := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [planeBlockGL_val_apply, hP, hA, hK.2.2.2.1 i j]
  rw [finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b (fun _ => rfl) hsph hp 1 hg,
    planeBlockGL_ιGL3 v hmem, hblk, det_ιGL]


/-- The adele norm of the block determinant is `(p^r)⁻¹` (the `p^{-r}` factor of the paper). -/
theorem adeleNorm_det_block (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    {r : ℕ} {s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r s t k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))) :
    (adeleNorm (Norm.finiteAdeleUnit (finiteAtPlaceUnit v (GeneralLinearGroup.det Ablk))) : ℝ) =
      (((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹ := by
  have hdet : finiteCompletionPadicEquiv v (GeneralLinearGroup.det Ablk).val =
      ((Rat.HeightOneSpectrum.primesEquiv v).val : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r := by
    have h1 : (GeneralLinearGroup.det Ablk).val =
        Ablk.val 0 0 * Ablk.val 1 1 - Ablk.val 0 1 * Ablk.val 1 0 := by
      exact Matrix.det_fin_two Ablk.val
    have h2 : (A 0 0 * A 1 1 - A 0 1 * A 1 0 : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) =
        ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r := by
      rw [← Matrix.det_fin_two]
      exact hK.2.1
    have h3 := congrArg (fun x : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val] =>
      (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) h2
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow] at h3
    rw [h1, hA 0 0, hA 0 1, hA 1 0, hA 1 1, ← map_mul, ← map_mul, ← map_sub,
      RingEquiv.apply_symm_apply]
    exact h3
  have hnorm : (adeleNorm (Norm.finiteAdeleUnit (finiteAtPlaceUnit v (GeneralLinearGroup.det Ablk))) : ℝ) =
      ‖finiteCompletionPadicEquiv v (GeneralLinearGroup.det Ablk).val‖ := by
    have hW : finiteAtPadicUnit v (Units.map (finiteCompletionPadicEquiv v).toMonoidHom
        (GeneralLinearGroup.det Ablk)) = finiteAtPlaceUnit v (GeneralLinearGroup.det Ablk) := by
      unfold finiteAtPadicUnit
      rw [MonoidHom.comp_apply]
      congr 1
      apply Units.ext
      exact (finiteCompletionPadicEquiv v).symm_apply_apply _
    have key := adeleNorm_finiteAtPadicUnit v (Units.map (finiteCompletionPadicEquiv v).toMonoidHom
        (GeneralLinearGroup.det Ablk))
    rw [hW] at key
    exact key
  rw [hnorm, hdet, norm_pr r]

/-- The plane section at `ι_v(L(s,t) k₀)` with the `p^{-r}` normalization made explicit. -/
theorem finitePlaneVector_K0_explicit (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    {r : ℕ} {s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r s t k A)
    (P : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ))
    (hP : ∀ i j, P.val i j = (finiteCompletionPadicEquiv v).symm ((Lst s t * toQ k) i j))
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])))
    (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) :
    finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (ιGL3 v P) vec =
      Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) •
        σ.π (atFinite (ιGL v Ablk)) vec := by
  rw [finitePlaneVector_K0 v hK P hP Ablk hA b hsph]
  congr 2
  unfold normPower
  rw [adeleNorm_det_block v hK Ablk hA]

end TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize

end
