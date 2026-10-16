module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBlockG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBasis
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlane

@[expose] public section


/-!
# Plane section at `ι_v(L(z)) · blk(g_f)` for an arbitrary finite base point (generalised shell integral)

For `g_f ∈ GL₂(𝔸_f)` whose place-`v` component is `gp ∈ GL₂(ℚ_v)` with `gp ∈ GL₂(O_v)`, the
decomposition `g_f = g' · ι_v(gp)` has `g'` trivial at `v`. The plane section at
`ι_v(L(z)) · blk(g_f)` then equals the `p^{-r}`-normalised value at the block `ι_v(Ablk) · g'`,
with the scalar `exp(b · log((p^r)⁻¹)) · normPower(det g', b)`.

The factorisation `ι_v(L(z)) = ι_v(P(z,k)) · ι_v(k⁻¹)` and the commutation of `ι_v(k⁻¹ · blk gp)`
past `blk g'` (trivial at `v`) are the two inputs. The integrality of `k⁻¹ · blk gp` in `GL₃(O_v)`
is proved entrywise via the subring `O_v`.

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
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (Lst toQ K0Spec)
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (planeBlockGL_val_apply)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv finiteAtPlaceUnit)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG

section Integrality

variable (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- `ψ_v` of an integer lies in `O_v`. -/
theorem psiV_mem_OS (x : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ∈ OS v := by
  refine (mem_iff_norm v _).2 ?_
  have h : pe v (psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) =
      (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :=
    finiteCompletionPadicEquiv_psiV v _
  rw [h]
  exact PadicInt.norm_le_one _

/-- Entries and inverse entries of a `GL₃(K_v)` element lie in `O_v`. -/
def IS3 (X : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)) : Prop :=
  (∀ i j, X.val i j ∈ OS v) ∧ (∀ i j, X⁻¹.val i j ∈ OS v)

omit [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] in
theorem IS3_mul {X Y : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)}
    (hX : IS3 v X) (hY : IS3 v Y) : IS3 v (X * Y) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => (OS v).mul_mem (hX.1 _ _) (hY.1 _ _)
  · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => (OS v).mul_mem (hY.2 _ _) (hX.2 _ _)

omit [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] in
theorem blk3_mem_OS {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hM : ∀ i j, M i j ∈ OS v) (i j : Fin 3) : blk3 M i j ∈ OS v := by
  fin_cases i <;> fin_cases j <;> simp [blk3, hM, (OS v).zero_mem, (OS v).one_mem]

omit [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] in
theorem IS3_blkLocGL (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgI : IntGL v gp.val) : IS3 v (blkLocGL v gp) := by
  refine ⟨fun i j => blk3_mem_OS v hgI.2.1 i j, fun i j => ?_⟩
  have e : (blkLocGL v gp)⁻¹.val = blk3 (gp.val)⁻¹ := by
    rw [← Matrix.coe_units_inv]
    rfl
  rw [e]
  exact blk3_mem_OS v hgI.2.2 i j

theorem IS3_kInvV (k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hk : k.det = 1) : IS3 v (GeneralLinearGroup.map (psiV v) (kInvGL k hk)) := by
  have hinv : (GeneralLinearGroup.map (psiV v) (kInvGL k hk))⁻¹ =
      GeneralLinearGroup.map (psiV v) (kGL k hk) := by
    rw [← map_inv, ← kGL_inv_eq, inv_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · show psiV v ((k.adjugate i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ∈ OS v
    exact psiV_mem_OS v _
  · rw [hinv]
    show psiV v ((k i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ∈ OS v
    exact psiV_mem_OS v _

omit [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] in
theorem exists_of_IS3 {X : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ)} (hX : IS3 v X) :
    ∃ kI : GeneralLinearGroup (Fin 3) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding kI = ιGL3 v X :=
  ιGL3_mem_integral_of_norm v X (fun i j => (mem_iff_norm v _).1 (hX.1 i j))
    (fun i j => (mem_iff_norm v _).1 (hX.2 i j))

end Integrality

theorem ιGL_one_eq (v : FinitePlace) : ιGL v 1 = 1 := by
  apply Units.ext
  simp [ιGL_val, ιMat_one]

section Plane

variable {σ : CuspidalRepresentation} (v : FinitePlace)
  [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- **Core identity.** For `gf = g' · ι_v(gp)` with `g'` trivial at `v` and `gp` integral at `v`,
the plane section at `ι_v(L(z)) · blk(gf)` is the `p^{-r}`-normalised value at `ι_v(Ablk) · g'`. -/
theorem finitePlaneVector_plane_core {r : ℕ}
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])))
    (b : ℂ) {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ)
    (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (hgI : IntGL v gp.val)
    (g' gf : BinaryFiniteGL) (hg' : g'.val.map (finiteEvaluation v) = 1)
    (hgf : gf = g' * ιGL v gp) :
    finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (ιGL3 v (LstV v z) * blkGL gf) vec =
      (Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det g')) b) •
        σ.π (atFinite (ιGL v Ablk * g')) vec := by
  subst hgf
  have hPval : ∀ i j, (PV v z k hK.1).val i j =
      (finiteCompletionPadicEquiv v).symm ((Lst z.1 z.2 * toQ k) i j) := fun _ _ => rfl
  have hmemP : PV v z k hK.1 ∈ planeParabolic (v.adicCompletion ℚ) :=
    mem_plane_of_K0 v hK (PV v z k hK.1) hPval
  have hp1 : ιGL3 v (PV v z k hK.1) ∈ planeParabolic FiniteAdeles := ιGL3_mem_plane v hmemP
  have hpg : blkGL g' ∈ planeParabolic FiniteAdeles := blkGL_mem_plane g'
  have hp : ιGL3 v (PV v z k hK.1) * blkGL g' ∈ planeParabolic FiniteAdeles :=
    (planeParabolic FiniteAdeles).mul_mem hp1 hpg
  have hblk : planeBlockGL (PV v z k hK.1) hmemP = Ablk := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [planeBlockGL_val_apply, hPval, hA, hK.2.2.2.1 i j]
  obtain ⟨kI, hkI⟩ := exists_of_IS3 v
    (IS3_mul v (IS3_kInvV v k hK.1) (IS3_blkLocGL v gp hgI))
  have hsplit : ιGL3 v (LstV v z) =
      ιGL3 v (PV v z k hK.1) * ιGL3 v (GeneralLinearGroup.map (psiV v) (kInvGL k hK.1)) := by
    rw [LstV, LstGL_eq_PGL_mul_inv z.1 z.2 k hK.1, map_mul, ιGL3_mul]
    rfl
  have hc : ιGL3 v (GeneralLinearGroup.map (psiV v) (kInvGL k hK.1)) * blkGL g' =
      blkGL g' * ιGL3 v (GeneralLinearGroup.map (psiV v) (kInvGL k hK.1)) :=
    ιGL3_blkGL_comm v _ g' (fun i j => congrFun (congrFun hg' i) j)
  have hg : ιGL3 v (LstV v z) * blkGL (g' * ιGL v gp) =
      (ιGL3 v (PV v z k hK.1) * blkGL g') * GeneralLinearGroup.map integralEmbedding kI := by
    rw [hkI, hsplit, blkGL_mul, blkGL_ιGL v gp,
      ιGL3_mul v (GeneralLinearGroup.map (psiV v) (kInvGL k hK.1)) (blkLocGL v gp)]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, hc, mul_assoc]
  have hfin := finitePlaneVector_eq_block GeneralEisenstein.trivialCharacter b (fun _ => rfl)
    hsph hp kI hg
  have hblockP : planeBlockGL (ιGL3 v (PV v z k hK.1) * blkGL g') hp = ιGL v Ablk * g' := by
    rw [planeBlockGL_mul hp1 hpg, planeBlockGL_ιGL3 v hmemP, hblk, planeBlockGL_blkGL]
  have hscal1 : normPower (Norm.finiteAdeleUnit (finiteAtPlaceUnit v
      (GeneralLinearGroup.det Ablk))) b =
      Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) := by
    unfold normPower
    rw [adeleNorm_det_block v hK Ablk hA]
  have hdet : normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (ιGL v Ablk * g'))) b =
      Complex.exp (b * (Real.log ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ r)⁻¹) : ℂ)) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det g')) b := by
    rw [map_mul, det_ιGL, finiteAdeleUnit_mul,
      TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_mul,
      hscal1]
  rw [hfin, hblockP, hdet]

/-- **The plane section at `ι_v(L(z)) · blk(g_f)` for an arbitrary finite base point.** The base
point `g_f` enters through its place-`v` component `gp` (integral at `v`, via `hgp`, `hgI`). The
block is `ι_v(Ablk) · g_f · ι_v(gp)⁻¹` and the scalar is `p^{-r b}` times the `normPower` of the
determinant of `g_f · ι_v(gp)⁻¹`. -/
theorem finitePlaneVector_blk_iota_LstV {r : ℕ}
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
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (gf * ιGL v gp⁻¹))) b) •
        σ.π (atFinite (ιGL v Ablk * (gf * ιGL v gp⁻¹))) vec := by
  have hιev : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (ιMat v M).map (finiteEvaluation v) = M :=
    fun M => evM_ιMat_self v M
  have hg' : (gf * ιGL v gp⁻¹).val.map (finiteEvaluation v) = 1 := by
    rw [Units.val_mul, ιGL_val, Matrix.map_mul, hgp, hιev, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  have hgf : gf = (gf * ιGL v gp⁻¹) * ιGL v gp := by
    rw [mul_assoc, ← TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis.ιGL_mul',
      inv_mul_cancel, ιGL_one_eq, mul_one]
  exact finitePlaneVector_plane_core v hK Ablk hA b hsph gp hgI (gf * ιGL v gp⁻¹) gf hg' hgf

end Plane

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG

end
