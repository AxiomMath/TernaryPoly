module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneArith
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineTheta

@[expose] public section


/-!
# The frame change of a plane face as a twisted isomorphism of extensions

Formalized by Claude Sonnet 5.5.

For `h' = q h γ` (`q ∈ planeBorel`, `γ ∈ SL₃(ℤ)`): `planeFrameEquiv N hN h q γ hq : TwistEquiv (faceExt N h') (faceExt N h)` with `θ p = γ p γ⁻¹`, radical map `phiPQ q` and Levi map conjugation by `A_G = topLeft q⁻¹ ∈ GL₂(ℤ)`.
The two orientation determinants are `det(phiPQ) = d` and `det A_G = d` with `d = q₂₂ = ±1`: their product is `1` (`planeFrame_sign`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

section Theta

variable (N : ℕ) [NeZero N] (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel)

/-- The conjugation `p ↦ γ p γ⁻¹` from the plane group of `q h γ` to that of `h`. -/
def planeThetaHom : gammaNPAt N (q * h * γ) →* gammaNPAt N h :=
  (frameHom N h q hq).comp (conjGammaHom N (q * h) γ)

omit [NeZero N] in
theorem planeThetaHom_val (p : gammaNPAt N (q * h * γ)) :
    ((planeThetaHom N h q γ hq p : gammaNPAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

omit [NeZero N] in
theorem planeThetaHom_bijective : Function.Bijective (planeThetaHom N h q γ hq) :=
  (frameHom_bijective N h q hq).comp (conjGammaHom_bijective N (q * h) γ)

def planeTheta : gammaNPAt N (q * h * γ) ≃* gammaNPAt N h :=
  MulEquiv.ofBijective (planeThetaHom N h q γ hq) (planeThetaHom_bijective N h q γ hq)

omit [NeZero N] in
theorem planeTheta_val (p : gammaNPAt N (q * h * γ)) :
    ((planeTheta N h q γ hq p : gammaNPAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

end Theta

section Alpha

variable {N : ℕ}

/-- The element `topLeft q⁻¹` of `GL₂(ℤ)`, whose inverse is `topLeft q`. -/
def AGP {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : IntegralGL :=
  ⟨topLeft q⁻¹, topLeft q, (topLeft_inv_mul q hq).2, (topLeft_inv_mul q hq).1⟩

theorem AGP_val {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : ((AGP hq : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = topLeft q⁻¹ := rfl

/-- **The Levi map of the frame change**: conjugation by `A_G = topLeft q⁻¹` on `Γ(N)`. -/
def alphaP (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : Gamma N ≃* Gamma N :=
  ((gammaEquiv hN).trans (MulAut.conjNormal (H := gammaNGL N) (AGP hq))).trans (gammaEquiv hN).symm

theorem alphaP_glConj (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : GLConj hN (alphaP hN hq) (AGP hq) := by
  intro l
  simp only [alphaP, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem alphaP_val (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (l : Gamma N) :
    (((alphaP hN hq l : Gamma N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      topLeft q⁻¹ * (l : SL(2, ℤ)) * topLeft q := by
  have h := alphaP_glConj hN hq l
  rw [gammaEquiv_coe, gammaEquiv_coe] at h
  have := congrArg (fun u : IntegralGL => (u : Matrix (Fin 2) (Fin 2) ℤ)) h
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end Alpha

end TernaryPeriodPolynomials.Argument.FrameInvariance
