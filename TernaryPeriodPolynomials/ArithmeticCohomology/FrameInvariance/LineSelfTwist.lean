module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineFrame

@[expose] public section


/-!
# Self-twists of a line face by the big stabilizer

Formalized by Claude Sonnet 5.5.

For `f ∈ SL₃(ℤ)` with `g = h f h⁻¹ ∈ lineBorel` (first column `(±1, 0, 0)ᵗ`, the integral stabilizer `Q(ℚ) ∩ SL₃(ℤ)` of the line) the conjugation `p ↦ f p f⁻¹` is a twisted automorphism
`lineSelfTwist : TwistEquiv (lineFaceExt N h) (lineFaceExt N h)` of the extension of the line cusp `h⁻¹ Q h`: it is the frame change `h ↦ q h f` of `lineFrameEquiv` with `q = g⁻¹`, so `q h f = h`.
Its Levi map is conjugation by `A_f = botRight g ∈ GL₂(ℤ)` (`lineSelfTwist_glConj`), and the determinant of its radical map is `det A_f` (`lineSelfTwist_radDet`).
Every `B ∈ GL₂(ℤ)` occurs (`exists_lineSelf`).
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

section Generic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel)

/-- The frame change `h ↦ q h γ`, stated for a frame `h'` equal to `q h γ`. -/
def lineFrameEquivOf {h' : SL(3, ℤ)} (e : q * h * γ = h') : TwistEquiv (lineFaceExt N h') (lineFaceExt N h) := by
  subst e; exact lineFrameEquiv N hN h q γ hq

theorem lineFrameEquivOf_φ {h' : SL(3, ℤ)} (e : q * h * γ = h') :
    (lineFrameEquivOf N hN h q γ hq e).φ = phiQ hq := by
  subst e; rfl

theorem lineFrameEquivOf_α {h' : SL(3, ℤ)} (e : q * h * γ = h') :
    (lineFrameEquivOf N hN h q γ hq e).α = alphaQ hN hq := by
  subst e; rfl

theorem lineFrameEquivOf_θ_val {h' : SL(3, ℤ)} (e : q * h * γ = h') (p : gammaNQAt N h') :
    (((lineFrameEquivOf N hN h q γ hq e).θ p : gammaNQAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := by
  subst e; rfl

end Generic

theorem AG_det {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : (AG hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  rw [AG_val]
  have hm := congrArg Matrix.det (botRight_inv_mul q hq).2
  rw [Matrix.det_mul, Matrix.det_one] at hm
  have hd := lineBorel_detA hq
  rw [← Matrix.det_fin_two] at hd
  rw [hd] at hm
  have h2 := lineBorel_a_sq hq
  linear_combination (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * hm - (botRight q⁻¹).det * h2

theorem radDet_phiQ_symm {q : SL(3, ℤ)} (hq : q ∈ lineBorel) :
    radDet (phiQ hq).symm.toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  have e : (phiQ hq).symm = phiQ (lineBorel.inv_mem hq) := MulEquiv.ext (fun r => rfl)
  rw [e, radDet_phiQ, inv_a hq]

section Self

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)

theorem lineSelf_mem {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : h * f⁻¹ * h⁻¹ ∈ lineBorel := by
  have := lineBorel.inv_mem hf
  have e : (h * f * h⁻¹)⁻¹ = h * f⁻¹ * h⁻¹ := by group
  rwa [e] at this

theorem lineSelf_eq (h f : SL(3, ℤ)) : (h * f⁻¹ * h⁻¹) * h * f = h := by group

/-- **The self-twist of the line face at `h` by `f`**, `h f h⁻¹ ∈ Q(ℚ) ∩ SL₃(ℤ)`. -/
def lineSelfTwist {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : TwistEquiv (lineFaceExt N h) (lineFaceExt N h) :=
  lineFrameEquivOf N hN h (h * f⁻¹ * h⁻¹) f (lineSelf_mem hf) (lineSelf_eq h f)

/-- The Levi element `A_f = botRight (h f h⁻¹) ∈ GL₂(ℤ)` of the self-twist. -/
def lineSelfA {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : IntegralGL := AG (lineSelf_mem hf)

theorem lineSelfA_val {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : ((lineSelfA hf : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = botRight (h * f * h⁻¹) := by
  rw [lineSelfA, AG_val]
  have e : (h * f⁻¹ * h⁻¹)⁻¹ = h * f * h⁻¹ := by group
  rw [e]

theorem lineSelfTwist_θ_val {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) (p : gammaNQAt N h) :
    (((lineSelfTwist N hN hf).θ p : gammaNQAt N h) : SL(3, ℤ)) = f * p.1 * f⁻¹ :=
  lineFrameEquivOf_θ_val N hN h _ f (lineSelf_mem hf) (lineSelf_eq h f) p

theorem lineSelfTwist_φ {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : (lineSelfTwist N hN hf).φ = phiQ (lineSelf_mem hf) :=
  lineFrameEquivOf_φ N hN h _ f (lineSelf_mem hf) (lineSelf_eq h f)

theorem lineSelfTwist_α {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : (lineSelfTwist N hN hf).α = alphaQ hN (lineSelf_mem hf) :=
  lineFrameEquivOf_α N hN h _ f (lineSelf_mem hf) (lineSelf_eq h f)

/-- **The Levi map of the self-twist is conjugation by `A_f`.** -/
theorem lineSelfTwist_glConj {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) : GLConj hN (lineSelfTwist N hN hf).α (lineSelfA hf) := by
  rw [lineSelfTwist_α]; exact alphaQ_glConj hN (lineSelf_mem hf)

/-- **The determinant of the radical map of the self-twist is `det A_f`.** -/
theorem lineSelfTwist_radDet {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ lineBorel) :
    radDet (lineSelfTwist N hN hf).φ.toMonoidHom = (lineSelfA hf).val.det := by
  rw [lineSelfTwist_φ, radDet_phiQ, lineSelfA, AG_det]

end Self

section BlockDiag

/-- The block diagonal element `diag(det B, B) ∈ SL₃(ℤ)` of `B ∈ GL₂(ℤ)`. -/
def lineBlockDiag (B : IntegralGL) : SL(3, ℤ) :=
  ⟨!![B.val.det, 0, 0; 0, B.val 0 0, B.val 0 1; 0, B.val 1 0, B.val 1 1], by
    have hu : IsUnit B.val.det := Matrix.isUnits_det_units B
    have hsq : B.val.det * B.val.det = 1 := by
      rcases Int.isUnit_iff.mp hu with h0 | h0 <;> rw [h0] <;> norm_num
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_fin_const]
    rw [Matrix.det_fin_two] at hsq ⊢
    linear_combination hsq⟩

theorem lineBlockDiag_mem (B : IntegralGL) : lineBlockDiag B ∈ lineBorel :=
  ⟨by simp [lineBlockDiag], by simp [lineBlockDiag]⟩

theorem botRight_lineBlockDiag (B : IntegralGL) : botRight (lineBlockDiag B) = B.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [botRight, lineBlockDiag]

/-- **Every `B ∈ GL₂(ℤ)` is the Levi element of a self-twist of the line face at `h`.** -/
theorem exists_lineSelf (h : SL(3, ℤ)) (B : IntegralGL) :
    ∃ (f : SL(3, ℤ)) (hf : h * f * h⁻¹ ∈ lineBorel), lineSelfA hf = B := by
  have e : h * (h⁻¹ * lineBlockDiag B * h) * h⁻¹ = lineBlockDiag B := by group
  have hf : h * (h⁻¹ * lineBlockDiag B * h) * h⁻¹ ∈ lineBorel := by
    rw [e]; exact lineBlockDiag_mem B
  refine ⟨_, hf, Units.ext ?_⟩
  rw [lineSelfA_val, e, botRight_lineBlockDiag]

end BlockDiag

/-- The determinant of the inverse of an element of `GL₂(ℤ)` equals its determinant (both are `±1`). -/
theorem det_inv_eq_det (A : IntegralGL) : ((A⁻¹ : IntegralGL).val).det = A.val.det := by
  have h1 : A.val.det * (A⁻¹ : IntegralGL).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]; simp
  have hu : IsUnit A.val.det := Matrix.isUnits_det_units A
  rcases Int.isUnit_iff.mp hu with h0 | h0 <;> rw [h0] at h1 ⊢ <;> linarith

section Coefficients

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ SL(3, ℤ) V)

/-- The action `ρ(f)` as a linear automorphism. -/
def coeffEquiv (f : SL(3, ℤ)) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinearMap (ρ f) (ρ f⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem coeffEquiv_apply (f : SL(3, ℤ)) (v : V) : coeffEquiv ρ f v = ρ f v := rfl

end Coefficients

end TernaryPeriodPolynomials.Argument.FrameInvariance
