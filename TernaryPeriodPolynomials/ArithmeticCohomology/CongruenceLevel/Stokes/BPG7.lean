module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG6

@[expose] public section


/-!
# Plane geometry package, part 7: calibration of `λ_F` on the plane test cocycle (G-c)

Formalized by Claude Sonnet 5.5.

For a frame `h`, a primitive vector `w` and an additive `ψ` on `Γ(6)`: `λ_{pflag h w}` of the class of the plane test cocycle `planeTestE h ψ`, pulled back to the stabilizer of `pflag h w`, is `432 ψ(posPar w)`.
-/

open scoped MatrixGroups
open CongruenceSubgroup CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor (planeStabEquiv)
open TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

/-- The inclusion of the stabilizer of a flag over `planeOf h` in the plane group of `h`. -/
def stabToE (h : SL(3, ℤ)) (F : Flag) (hF : flagPlaneOf F = planeOf h) :
    ↥(MulAction.stabilizer Γ6 F) →* ↥(gammaNPAt 6 h) :=
  (planeStabEquiv h).symm.toMonoidHom.comp (Subgroup.inclusion (by
    have := stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F
    rw [hF] at this
    exact this))

theorem stabToE_val (h : SL(3, ℤ)) (F : Flag) (hF : flagPlaneOf F = planeOf h) (s : ↥(MulAction.stabilizer Γ6 F)) :
    ((stabToE h F hF s : ↥(gammaNPAt 6 h)) : SL(3, ℤ)) = iotaOf (s : Γ6) := by
  have h1 : planeStabEquiv h ((planeStabEquiv h).symm (Subgroup.inclusion (by
    have := stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F
    rw [hF] at this
    exact this) s)) = Subgroup.inclusion (by
    have := stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F
    rw [hF] at this
    exact this) s := MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun x : ↥(MulAction.stabilizer Γ6 (planeOf h)) => (x : Γ6)) h1
  have h3 : planeEmb h ((stabToE h F hF) s) = (s : Γ6) := h2
  rw [← iotaOf_planeEmb, h3]

theorem rightHom_val (h : SL(3, ℤ)) (p : ↥(gammaNPAt 6 h)) :
    (((faceExt 6 h).rightHom p : Gamma 6) : SL(2, ℤ)) = leviBlock (h * p.1 * h⁻¹) p.2.2 := rfl

/-- The Levi block of `X ∈ planeStab` whose `qBD`-conjugate has top-left block `[[1, 6k], [0, 1]]`. -/
theorem levi_conj (w : Prim2) (X M : SL(3, ℤ)) (hX : X ∈ planeStab) (hM : X = blockDiag (colSL w) * M * blockDiag (colSL w)⁻¹)
    (k : ℤ) (m00 : (M : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1) (m10 : (M : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0)
    (m11 : (M : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1) (m01 : (M : Matrix (Fin 3) (Fin 3) ℤ) 0 1 = 6 * k) :
    ((leviBlock X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = PKwMat w k := by
  have hc : (X : Matrix (Fin 3) (Fin 3) ℤ) = (blockDiag (colSL w) : Matrix (Fin 3) (Fin 3) ℤ) * (M : Matrix (Fin 3) (Fin 3) ℤ) *
      (blockDiag (colSL w)⁻¹ : Matrix (Fin 3) (Fin 3) ℤ) := by
    rw [hM]; simp
  ext i j
  have e := fun a b => congrFun (congrFun hc a) b
  fin_cases i <;> fin_cases j <;>
    (simp only [leviBlock, PKwMat, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two]
     rw [e]
     simp only [Matrix.mul_apply, Fin.sum_univ_three]
     simp [blockDiag, m00, m10, m11, m01, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two])

theorem tau_qBD_00 (w : Prim2) : ((tau (qBD w) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by
  rw [tau_apply, qBD, blockDiag_inv, inv_inv]
  simp [blockDiag]

/-- The matrix homomorphism attached to the flag `pflag h w`. -/
def pMh (h : SL(3, ℤ)) (w : Prim2) : ↥(MulAction.stabilizer Γ6 (pflag h w)) →* SL(3, ℤ) :=
  (planeEHom h).comp (stabToE h (pflag h w) (flagPlaneOf_pflag h w))

theorem pMh_lineType (h : SL(3, ℤ)) (w : Prim2) : LineType (pMh h w) :=
  fun s => planeEHom_lineType h (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s)

theorem pMh_apply (h : SL(3, ℤ)) (w : Prim2) (s : ↥(MulAction.stabilizer Γ6 (pflag h w))) :
    pMh h w s = tau (h * iotaOf (s : Γ6) * h⁻¹) := by
  have := stabToE_val h (pflag h w) (flagPlaneOf_pflag h w) s
  simp only [pMh, MonoidHom.comp_apply, planeEHom, planeEM, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulAut.conj_apply, Subgroup.coe_subtype, this]

theorem pMh_rel (h : SL(3, ℤ)) (w : Prim2) (s : ↥(MulAction.stabilizer Γ6 (pflag h w))) :
    ((tau (qBD w) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) * (pMh h w s : Matrix (Fin 3) (Fin 3) ℤ) =
      (tau (conjIota (MulAction.stabilizer Γ6 (pflag h w)) (qBD w * h) s) : Matrix (Fin 3) (Fin 3) ℤ) *
        (tau (qBD w) : Matrix (Fin 3) (Fin 3) ℤ) := by
  have : tau (qBD w) * pMh h w s = tau (conjIota (MulAction.stabilizer Γ6 (pflag h w)) (qBD w * h) s) * tau (qBD w) := by
    rw [pMh_apply, ← map_mul, ← map_mul]
    congr 1
    simp only [conjIota_apply, iotaOf]
    group
  exact congrArg (fun x : SL(3, ℤ) => (x : Matrix (Fin 3) (Fin 3) ℤ)) this

theorem pMh_u (h : SL(3, ℤ)) (w : Prim2) (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b)
    (s : ↥(MulAction.stabilizer Γ6 (pflag h w))) :
    planeTestU h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s) =
      (-ψ (posParSL w.1) / 6) * ((-((conjIota (MulAction.stabilizer Γ6 (pflag h w)) (qBD w * h) s : Matrix (Fin 3) (Fin 3) ℤ) 0 1) : ℤ) : ℚ) := by
  have hg : flagOf (qBD w * h) = pflag h w := rfl
  obtain ⟨m00, m11, -, m10, -, -, d01⟩ := frame_entries_all (pflag h w) (qBD w * h) hg s
  obtain ⟨k, hk⟩ := d01
  have hfm : conjIota (MulAction.stabilizer Γ6 (pflag h w)) (qBD w * h) s = frameMat (pflag h w) (qBD w * h) s := rfl
  have e1 := stabToE_val h (pflag h w) (flagPlaneOf_pflag h w) s
  have hX : h * (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s).1 * h⁻¹ ∈ planeStab := (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s).2.2
  have hXM : h * (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s).1 * h⁻¹ =
      blockDiag (colSL w) * frameMat (pflag h w) (qBD w * h) s * blockDiag (colSL w)⁻¹ := by
    have e2 : frameMat (pflag h w) (qBD w * h) s = qBD w * h * iotaOf (s : Γ6) * (qBD w * h)⁻¹ := rfl
    have hB : blockDiag (colSL w) = (blockDiag (colSL w)⁻¹)⁻¹ := by rw [← blockDiag_inv, inv_inv]
    rw [e2, e1, qBD]
    generalize blockDiag (colSL w)⁻¹ = B at hB ⊢
    rw [hB]
    group
  have hL := levi_conj w _ _ hX hXM k m00 m10 m11 hk
  have hR : (faceExt 6 h).rightHom (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s) = PKw w k := by
    apply Subtype.ext
    apply Subtype.ext
    rw [show (((faceExt 6 h).rightHom (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s) : Gamma 6) : SL(2, ℤ)) = leviBlock _ hX from rfl]
    exact hL
  have : planeTestU h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s) = ψ (PKw w k) := by rw [planeTestU, hR]
  rw [this, psi_PKw ψ hψ w k, PKw_one, hfm, hk]
  push_cast
  ring

end TernaryPeriodPolynomials.Argument.GammaNStokes
