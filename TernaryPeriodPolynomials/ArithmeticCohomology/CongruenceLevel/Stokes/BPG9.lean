module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG8

@[expose] public section


/-!
# Plane geometry package, part 9: the matrix datum of the plane test cocycle on the letters (G-d)

Formalized by Claude Sonnet 5.5.

The line-type homomorphism `planeEHom h : p ↦ tau (h p h⁻¹)` of the plane group of `h` takes, on the radical letter `inl r` with `r = (a, b)`, the datum `A = 1`, `v = (-6b, -6a)`, and on the Levi letter `faceSplitting σ`, `σ = [[a, b], [c, d]]`, the datum `A = [[a, -b], [-c, d]]`, `v = 0`.
-/

open scoped MatrixGroups
open CongruenceSubgroup

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice)

theorem planeEHom_apply (h : SL(3, ℤ)) (x : ↥(gammaNPAt 6 h)) : planeEHom h x = tau (h * x.1 * h⁻¹) := rfl

theorem radElt_inv (r : RadicalLattice) : (radElt 6 r)⁻¹ = radElt 6 r⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← radElt_mul, mul_inv_cancel, radElt_one]

theorem tau_radElt_apply (r : RadicalLattice) (i j : Fin 3) :
    ((tau (radElt 6 r) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) i j = (radElt 6 r⁻¹ : Matrix (Fin 3) (Fin 3) ℤ) j.rev i.rev := by
  rw [tau_apply, radElt_inv]

theorem tau_blockDiag_apply (σ : SL(2, ℤ)) (i j : Fin 3) :
    ((tau (blockDiag σ) : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) i j = (blockDiag σ⁻¹ : Matrix (Fin 3) (Fin 3) ℤ) j.rev i.rev := by
  rw [tau_apply, blockDiag_inv]

/-- The datum of the plane test homomorphism on a radical letter: `A = 1`. -/
theorem planeE_inl_A (h : SL(3, ℤ)) (r : RadicalLattice) :
    (matLineData (planeEHom h) (planeEHom_lineType h)).A ((faceExt 6 h).inl r) = 1 := by
  have e : h * (((faceExt 6 h).inl r : gammaNPAt 6 h) : SL(3, ℤ)) * h⁻¹ = radElt 6 r := by
    rw [faceExt_inl_val]; group
  have e' : planeEHom h ((faceExt 6 h).inl r) = tau (radElt 6 r) := by rw [planeEHom_apply, e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [matLineData, e', tau_radElt_apply]
     simp [radElt, Fin.rev])

/-- The datum of the plane test homomorphism on a radical letter: `v = (-6b, -6a)`. -/
theorem planeE_inl_v (h : SL(3, ℤ)) (r : RadicalLattice) :
    (matLineData (planeEHom h) (planeEHom_lineType h)).v ((faceExt 6 h).inl r) =
      ![-(6 * r.toAdd.2), -(6 * r.toAdd.1)] := by
  have e : h * (((faceExt 6 h).inl r : gammaNPAt 6 h) : SL(3, ℤ)) * h⁻¹ = radElt 6 r := by
    rw [faceExt_inl_val]; group
  have e' : planeEHom h ((faceExt 6 h).inl r) = tau (radElt 6 r) := by rw [planeEHom_apply, e]
  ext j
  fin_cases j <;>
    (simp only [matLineData, e', tau_radElt_apply]
     simp [radElt, Fin.rev])

/-- The datum on a Levi letter: `A = [[a, -b], [-c, d]]`. -/
theorem planeE_split_A (h : SL(3, ℤ)) (σ : CongruenceSubgroup.Gamma 6) :
    (matLineData (planeEHom h) (planeEHom_lineType h)).A ((faceSplitting 6 h) σ) =
      !![(σ.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0, -(σ.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        -(σ.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (σ.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := by
  have e : h * (((faceSplitting 6 h) σ : gammaNPAt 6 h) : SL(3, ℤ)) * h⁻¹ = blockDiag σ.1 := by
    rw [faceSplitting_val]; group
  have e' : planeEHom h ((faceSplitting 6 h) σ) = tau (blockDiag σ.1) := by rw [planeEHom_apply, e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [matLineData, e', tau_blockDiag_apply]
     simp [blockDiag, Fin.rev, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two])

/-- The datum on a Levi letter: `v = 0`. -/
theorem planeE_split_v (h : SL(3, ℤ)) (σ : CongruenceSubgroup.Gamma 6) :
    (matLineData (planeEHom h) (planeEHom_lineType h)).v ((faceSplitting 6 h) σ) = 0 := by
  have e : h * (((faceSplitting 6 h) σ : gammaNPAt 6 h) : SL(3, ℤ)) * h⁻¹ = blockDiag σ.1 := by
    rw [faceSplitting_val]; group
  have e' : planeEHom h ((faceSplitting 6 h) σ) = tau (blockDiag σ.1) := by rw [planeEHom_apply, e]
  ext j
  fin_cases j <;>
    (simp only [matLineData, e', tau_blockDiag_apply]
     simp [blockDiag, Fin.rev])

end TernaryPeriodPolynomials.Argument.GammaNStokes
