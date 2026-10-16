module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneTheta

@[expose] public section


/-!
# The frame change of a plane face as a twisted isomorphism of extensions (assembly)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel)

theorem planeFrame_inl (r : RadicalLattice) :
    planeTheta N h q γ hq ((faceExt N (q * h * γ)).inl r) = (faceExt N h).inl (phiPQ hq r) := by
  apply Subtype.ext
  change γ * ((q * h * γ)⁻¹ * radElt N r * (q * h * γ)) * γ⁻¹ = h⁻¹ * radElt N (phiPQHom q r) * h
  have e : γ * ((q * h * γ)⁻¹ * radElt N r * (q * h * γ)) * γ⁻¹ = h⁻¹ * (q⁻¹ * (radElt N r * q)) * h := by group
  rw [e, rad_mul_qP N hq, inv_mul_cancel_left]

theorem planeFrame_right (p : gammaNPAt N (q * h * γ)) :
    (faceExt N h).rightHom (planeTheta N h q γ hq p) = alphaP hN hq ((faceExt N (q * h * γ)).rightHom p) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [alphaP_val]
  set X : SL(3, ℤ) := h * (γ * p.1 * γ⁻¹) * h⁻¹ with hX
  have hXmem : X ∈ gammaNP N := (planeTheta N h q γ hq p).2
  have hXb : X ∈ planeBorel := mem_planeBorel_of_mem_planeStab hXmem.2
  have hY : q * h * γ * p.1 * (q * h * γ)⁻¹ = q * X * q⁻¹ := by rw [hX]; group
  have hbr := topLeft_conj q X hq hXb
  have key : topLeft q⁻¹ * topLeft (q * X * q⁻¹) * topLeft q = topLeft X := by
    rw [hbr]
    have h1 := (topLeft_inv_mul q hq).2
    calc topLeft q⁻¹ * (topLeft q * topLeft X * topLeft q⁻¹) * topLeft q
        = (topLeft q⁻¹ * topLeft q) * topLeft X * (topLeft q⁻¹ * topLeft q) := by simp only [mul_assoc]
      _ = topLeft X := by rw [h1]; simp
  change topLeft X = topLeft q⁻¹ * topLeft (q * h * γ * p.1 * (q * h * γ)⁻¹) * topLeft q
  rw [hY, key]

/-- **The frame change `h ↦ q h γ` of a plane face as a twisted isomorphism of the extensions.** -/
def planeFrameEquiv : TwistEquiv (faceExt N (q * h * γ)) (faceExt N h) where
  θ := planeTheta N h q γ hq
  φ := phiPQ hq
  α := alphaP hN hq
  inl_comm := planeFrame_inl N h q γ hq
  rightHom_comm := planeFrame_right N hN h q γ hq

/-- **The orientation signs cancel**: the determinant of the radical map times the determinant of the Levi conjugation is `1`. -/
theorem planeFrame_sign :
    (radDet (planeFrameEquiv N hN h q γ hq).φ.toMonoidHom : ℂ) * (((AGP hq).val.det : ℤ) : ℂ) = 1 := by
  have h1 := radDet_phiPQ hq
  have h2 := planeBorel_d_sq hq
  have h3 : (AGP hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
    rw [AGP_val, Matrix.det_fin_two]
    have hd := planeBorel_detA (planeBorel.inv_mem hq)
    rw [inv_d hq] at hd
    exact hd
  show ((radDet (phiPQ hq).toMonoidHom : ℤ) : ℂ) * (((AGP hq).val.det : ℤ) : ℂ) = 1
  rw [h1, h3]
  exact_mod_cast h2

end TernaryPeriodPolynomials.Argument.FrameInvariance
