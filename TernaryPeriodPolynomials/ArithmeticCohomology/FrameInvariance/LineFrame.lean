module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineTheta

@[expose] public section


/-!
# The frame change of a line face as a twisted isomorphism of extensions (assembly)

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel)

theorem lineFrame_inl (r : RadicalLattice) :
    lineTheta N h q γ hq ((lineFaceExt N (q * h * γ)).inl r) = (lineFaceExt N h).inl (phiQ hq r) := by
  apply Subtype.ext
  change γ * ((q * h * γ)⁻¹ * radEltQ N r * (q * h * γ)) * γ⁻¹ = h⁻¹ * radEltQ N (phiQHom q r) * h
  have e : γ * ((q * h * γ)⁻¹ * radEltQ N r * (q * h * γ)) * γ⁻¹ = h⁻¹ * (q⁻¹ * (radEltQ N r * q)) * h := by group
  rw [e, rad_mul_q N hq, inv_mul_cancel_left]

theorem lineFrame_right (p : gammaNQAt N (q * h * γ)) :
    (lineFaceExt N h).rightHom (lineTheta N h q γ hq p) = alphaQ hN hq ((lineFaceExt N (q * h * γ)).rightHom p) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [alphaQ_val]
  set X : SL(3, ℤ) := h * (γ * p.1 * γ⁻¹) * h⁻¹ with hX
  have hXmem : X ∈ gammaNQ N := (lineTheta N h q γ hq p).2
  have hXb : X ∈ lineBorel := mem_lineBorel_of_mem_lineStab hXmem.2
  have hY : q * h * γ * p.1 * (q * h * γ)⁻¹ = q * X * q⁻¹ := by rw [hX]; group
  have hbr := botRight_conj q X hq hXb
  have key : botRight q⁻¹ * botRight (q * X * q⁻¹) * botRight q = botRight X := by
    rw [hbr]
    have h1 := (botRight_inv_mul q hq).2
    calc botRight q⁻¹ * (botRight q * botRight X * botRight q⁻¹) * botRight q
        = (botRight q⁻¹ * botRight q) * botRight X * (botRight q⁻¹ * botRight q) := by simp only [mul_assoc]
      _ = botRight X := by rw [h1]; simp
  change botRight X = botRight q⁻¹ * botRight (q * h * γ * p.1 * (q * h * γ)⁻¹) * botRight q
  rw [hY, key]

/-- **The frame change `h ↦ q h γ` of a line face as a twisted isomorphism of the extensions.** -/
def lineFrameEquiv : TwistEquiv (lineFaceExt N (q * h * γ)) (lineFaceExt N h) where
  θ := lineTheta N h q γ hq
  φ := phiQ hq
  α := alphaQ hN hq
  inl_comm := lineFrame_inl N h q γ hq
  rightHom_comm := lineFrame_right N hN h q γ hq

/-- **The orientation signs cancel**: the determinant of the radical map times the determinant of the Levi conjugation is `1`. -/
theorem lineFrame_sign :
    (radDet (lineFrameEquiv N hN h q γ hq).φ.toMonoidHom : ℂ) * (((AG hq).val.det : ℤ) : ℂ) = 1 := by
  have h1 := radDet_phiQ hq
  have h2 := lineBorel_a_sq hq
  have h3 : (AG hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
    rw [AG_val]
    have hm := congrArg Matrix.det (botRight_inv_mul q hq).2
    rw [Matrix.det_mul, Matrix.det_one] at hm
    have hd := lineBorel_detA hq
    rw [← Matrix.det_fin_two] at hd
    rw [hd] at hm
    linear_combination (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * hm - (botRight q⁻¹).det * h2
  show ((radDet (phiQ hq).toMonoidHom : ℤ) : ℂ) * (((AG hq).val.det : ℤ) : ℂ) = 1
  rw [h1, h3]
  exact_mod_cast h2

end TernaryPeriodPolynomials.Argument.FrameInvariance
