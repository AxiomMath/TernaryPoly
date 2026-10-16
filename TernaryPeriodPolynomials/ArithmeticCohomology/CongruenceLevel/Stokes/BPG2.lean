module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel

@[expose] public section


/-!
# Plane geometry package, part 2: the flags over a plane attached to the primitive vectors; their stabilizers

Formalized by Claude Sonnet 5.5.

For a frame `h` and a primitive vector `w`, `pflag h w = flagOf (blockDiag (colSL w)⁻¹ * h)` is a complete flag over the plane `planeOf h`.  Its stabilizer in `Γ(6)` contains the radical letters
`faceExt.inl r = h⁻¹ radElt r h` of the plane group of `h`, and the Levi letter `h⁻¹ blockDiag (posPar w) h` (`pflag_stab_nl`, `pflag_stab_ll`); `faceExt_inl_val`, `faceSplitting_val` give the matrices of the letters.
-/

open scoped MatrixGroups
open CongruenceSubgroup

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice)

theorem faceExt_inl_val (h : SL(3, ℤ)) (r : RadicalLattice) :
    (((faceExt 6 h).inl r : gammaNPAt 6 h) : SL(3, ℤ)) = h⁻¹ * radElt 6 r * h := rfl

theorem faceSplitting_val (h : SL(3, ℤ)) (σ : CongruenceSubgroup.Gamma 6) :
    (((faceSplitting 6 h) σ : gammaNPAt 6 h) : SL(3, ℤ)) = h⁻¹ * blockDiag σ.1 * h := rfl

theorem iotaOf_planeEmb (h : SL(3, ℤ)) (p : gammaNPAt 6 h) : iotaOf (planeEmb h p) = p.1 := by
  simp [iotaOf, planeEmb]

theorem blockDiag_inv (A : SL(2, ℤ)) : (blockDiag A)⁻¹ = blockDiag A⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← blockDiag_mul, mul_inv_cancel, blockDiag_one]

/-- The block-diagonal element attached to a primitive vector. -/
def qBD (w : Prim2) : SL(3, ℤ) := blockDiag (colSL w)⁻¹

theorem qBD_mem (w : Prim2) : qBD w ∈ planeBorel := blockDiag_mem_planeBorel _

/-- **The complete flag over the plane `planeOf h` attached to the primitive vector `w`.** -/
def pflag (h : SL(3, ℤ)) (w : Prim2) : Flag := flagOf (qBD w * h)

theorem flagPlaneOf_pflag (h : SL(3, ℤ)) (w : Prim2) : flagPlaneOf (pflag h w) = planeOf h := by
  rw [pflag, flagPlaneOf_flagOf]
  exact ((planeOf_eq_iff h (qBD w * h)).2 (by simpa using qBD_mem w)).symm

theorem mem_stab_pflag (h : SL(3, ℤ)) (w : Prim2) (p : gammaN 6)
    (hp : qBD w * (h * p.1 * h⁻¹) * (qBD w)⁻¹ ∈ borelStab) : gammaSixEquiv p ∈ MulAction.stabilizer Γ6 (pflag h w) := by
  rw [pflag, mem_stabilizer_flagOf_iff]
  have e : qBD w * h * p.1 * (qBD w * h)⁻¹ = qBD w * (h * p.1 * h⁻¹) * (qBD w)⁻¹ := by group
  show qBD w * h * p.1 * (qBD w * h)⁻¹ ∈ gammaNB 6
  rw [e]
  refine ⟨?_, hp⟩
  have := (gammaN_normal 6).conj_mem _ ((gammaN_normal 6).conj_mem _ p.2 h) (qBD w)
  simpa [mul_assoc] using this

theorem borel_blockDiag_rad (Q : SL(2, ℤ)) (r : RadicalLattice) :
    blockDiag Q * radElt 6 r * blockDiag Q⁻¹ ∈ borelStab := by
  have hd : (Q : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (Q : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (Q : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (Q : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := Q.2; rw [Matrix.det_fin_two] at this; exact this
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
     simp [blockDiag, radElt, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_three]
     try ring)

/-- The radical letters stabilize `pflag h w`. -/
theorem pflag_stab_nl (h : SL(3, ℤ)) (w : Prim2) (r : RadicalLattice) :
    planeEmb h ((faceExt 6 h).inl r) ∈ MulAction.stabilizer Γ6 (pflag h w) := by
  have := mem_stab_pflag h w ⟨((faceExt 6 h).inl r : gammaNPAt 6 h).1, gammaNPAt_le_gammaN 6 h ((faceExt 6 h).inl r).2⟩ ?_
  · exact this
  · rw [faceExt_inl_val]
    have e : h * (h⁻¹ * radElt 6 r * h) * h⁻¹ = radElt 6 r := by group
    rw [e, qBD, blockDiag_inv]
    exact borel_blockDiag_rad _ r

theorem borel_blockDiag_posPar_e1 : blockDiag (posPar ![1, 0]) ∈ borelStab := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [blockDiag, posPar]

/-- The Levi letter `h⁻¹ blockDiag (posPar w) h` stabilizes `pflag h w`. -/
theorem pflag_stab_ll (h : SL(3, ℤ)) (w : Prim2) (σ : CongruenceSubgroup.Gamma 6) (hσ : σ.1 = posPar w.1) :
    planeEmb h ((faceSplitting 6 h) σ) ∈ MulAction.stabilizer Γ6 (pflag h w) := by
  have := mem_stab_pflag h w ⟨(((faceSplitting 6 h) σ : gammaNPAt 6 h)).1, gammaNPAt_le_gammaN 6 h ((faceSplitting 6 h) σ).2⟩ ?_
  · exact this
  · rw [faceSplitting_val]
    have e : h * (h⁻¹ * blockDiag σ.1 * h) * h⁻¹ = blockDiag σ.1 := by group
    rw [e, qBD, blockDiag_inv, ← blockDiag_mul, ← blockDiag_mul, hσ, posPar_conj, colSL_inv_mulVec]
    exact borel_blockDiag_posPar_e1

end TernaryPeriodPolynomials.Argument.GammaNStokes
