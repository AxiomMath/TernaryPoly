module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineArith
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CanonicalTwist
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# The frame change of a line face as a twisted isomorphism of extensions

Formalized by Claude Sonnet 5.5.

For `h' = q h γ` (`q ∈ lineBorel`, `γ ∈ SL₃(ℤ)`): `lineFrameEquiv N hN h q γ hq : TwistEquiv (lineFaceExt N h') (lineFaceExt N h)` with `θ p = γ p γ⁻¹`, radical map `phiQ q` and Levi map conjugation by `A_G = botRight q⁻¹ ∈ GL₂(ℤ)`
(`GLConj`).  The two orientation determinants are `det(phiQ) = a` and `det A_G = a` with `a = q₀₀ = ±1`: their product is `1` (`lineFrame_sign`).
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

section Theta

variable (N : ℕ) [NeZero N] (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel)

/-- The conjugation `p ↦ γ p γ⁻¹` from the line group of `q h γ` to that of `h`. -/
def lineThetaHom : gammaNQAt N (q * h * γ) →* gammaNQAt N h :=
  (GammaNFacesFull.frameHomQ N h q hq).comp (GammaNFacesFull.conjGammaHomQ N (q * h) γ)

omit [NeZero N] in
theorem lineThetaHom_val (p : gammaNQAt N (q * h * γ)) :
    ((lineThetaHom N h q γ hq p : gammaNQAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

omit [NeZero N] in
theorem lineThetaHom_bijective : Function.Bijective (lineThetaHom N h q γ hq) :=
  (GammaNFacesFull.frameHomQ_bijective N h q hq).comp (GammaNFacesFull.conjGammaHomQ_bijective N (q * h) γ)

def lineTheta : gammaNQAt N (q * h * γ) ≃* gammaNQAt N h :=
  MulEquiv.ofBijective (lineThetaHom N h q γ hq) (lineThetaHom_bijective N h q γ hq)

omit [NeZero N] in
theorem lineTheta_val (p : gammaNQAt N (q * h * γ)) :
    ((lineTheta N h q γ hq p : gammaNQAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := rfl

end Theta

section Alpha

variable {N : ℕ}

instance gammaNGL_normal : (gammaNGL N).Normal := MonoidHom.normal_ker _

/-- The element `botRight q⁻¹` of `GL₂(ℤ)`, whose inverse is `botRight q`. -/
def AG {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : IntegralGL :=
  ⟨botRight q⁻¹, botRight q, (botRight_inv_mul q hq).2, (botRight_inv_mul q hq).1⟩

theorem AG_val {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : ((AG hq : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = botRight q⁻¹ := rfl

theorem AG_inv_val {q : SL(3, ℤ)} (hq : q ∈ lineBorel) :
    (((AG hq)⁻¹ : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = botRight q := rfl

/-- **The Levi map of the frame change**: conjugation by `A_G = botRight q⁻¹` on `Γ(N)`. -/
def alphaQ (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : Gamma N ≃* Gamma N :=
  ((gammaEquiv hN).trans (MulAut.conjNormal (H := gammaNGL N) (AG hq))).trans (gammaEquiv hN).symm

theorem alphaQ_glConj (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : GLConj hN (alphaQ hN hq) (AG hq) := by
  intro l
  simp only [alphaQ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem alphaQ_val (hN : 3 ≤ N) {q : SL(3, ℤ)} (hq : q ∈ lineBorel) (l : Gamma N) :
    (((alphaQ hN hq l : Gamma N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      botRight q⁻¹ * (l : SL(2, ℤ)) * botRight q := by
  have h := alphaQ_glConj hN hq l
  rw [gammaEquiv_coe, gammaEquiv_coe] at h
  have := congrArg (fun u : IntegralGL => (u : Matrix (Fin 2) (Fin 2) ℤ)) h
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end Alpha

end TernaryPeriodPolynomials.Argument.FrameInvariance
