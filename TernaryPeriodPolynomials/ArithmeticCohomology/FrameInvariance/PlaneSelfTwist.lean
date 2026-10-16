module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineSelfTwist

@[expose] public section


/-!
# Self-twists of a plane face by the big stabilizer

Formalized by Claude Sonnet 5.5.

For `f ∈ SL₃(ℤ)` with `g = h f h⁻¹ ∈ planeBorel` (bottom row `(0, 0, ±1)`, the integral stabilizer `P(ℚ) ∩ SL₃(ℤ)` of the plane) the conjugation `p ↦ f p f⁻¹` is a twisted automorphism
`planeSelfTwist : TwistEquiv (faceExt N h) (faceExt N h)`: it is the frame change `h ↦ q h f` of `planeFrameEquiv` with `q = g⁻¹`, so `q h f = h`.
Its Levi map is conjugation by `A_f = topLeft g ∈ GL₂(ℤ)` (`planeSelfTwist_glConj`), and the determinant of its radical map is `det A_f` (`planeSelfTwist_radDet`).
Every `B ∈ GL₂(ℤ)` occurs (`exists_planeSelf`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

section Generic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel)

/-- The frame change `h ↦ q h γ`, stated for a frame `h'` equal to `q h γ`. -/
def planeFrameEquivOf {h' : SL(3, ℤ)} (e : q * h * γ = h') : TwistEquiv (faceExt N h') (faceExt N h) := by
  subst e; exact planeFrameEquiv N hN h q γ hq

theorem planeFrameEquivOf_φ {h' : SL(3, ℤ)} (e : q * h * γ = h') :
    (planeFrameEquivOf N hN h q γ hq e).φ = phiPQ hq := by
  subst e; rfl

theorem planeFrameEquivOf_α {h' : SL(3, ℤ)} (e : q * h * γ = h') :
    (planeFrameEquivOf N hN h q γ hq e).α = alphaP hN hq := by
  subst e; rfl

theorem planeFrameEquivOf_θ_val {h' : SL(3, ℤ)} (e : q * h * γ = h') (p : gammaNPAt N h') :
    (((planeFrameEquivOf N hN h q γ hq e).θ p : gammaNPAt N h) : SL(3, ℤ)) = γ * p.1 * γ⁻¹ := by
  subst e; rfl

end Generic

theorem AGP_det {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : (AGP hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
  rw [AGP_val, Matrix.det_fin_two]
  have hd := planeBorel_detA (planeBorel.inv_mem hq)
  rw [inv_d hq] at hd
  exact hd

theorem radDet_phiPQ_symm {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    radDet (phiPQ hq).symm.toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
  have e : (phiPQ hq).symm = phiPQ (planeBorel.inv_mem hq) := MulEquiv.ext (fun r => rfl)
  rw [e, radDet_phiPQ, inv_d hq]

section Self

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)

theorem planeSelf_mem {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : h * f⁻¹ * h⁻¹ ∈ planeBorel := by
  have := planeBorel.inv_mem hf
  have e : (h * f * h⁻¹)⁻¹ = h * f⁻¹ * h⁻¹ := by group
  rwa [e] at this

theorem planeSelf_eq (h f : SL(3, ℤ)) : (h * f⁻¹ * h⁻¹) * h * f = h := by group

/-- **The self-twist of the plane face at `h` by `f`**, `h f h⁻¹ ∈ P(ℚ) ∩ SL₃(ℤ)`. -/
def planeSelfTwist {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : TwistEquiv (faceExt N h) (faceExt N h) :=
  planeFrameEquivOf N hN h (h * f⁻¹ * h⁻¹) f (planeSelf_mem hf) (planeSelf_eq h f)

/-- The Levi element `A_f = topLeft (h f h⁻¹) ∈ GL₂(ℤ)` of the self-twist. -/
def planeSelfA {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : IntegralGL := AGP (planeSelf_mem hf)

theorem planeSelfA_val {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : ((planeSelfA hf : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = topLeft (h * f * h⁻¹) := by
  rw [planeSelfA, AGP_val]
  have e : (h * f⁻¹ * h⁻¹)⁻¹ = h * f * h⁻¹ := by group
  rw [e]

theorem planeSelfTwist_θ_val {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) (p : gammaNPAt N h) :
    (((planeSelfTwist N hN hf).θ p : gammaNPAt N h) : SL(3, ℤ)) = f * p.1 * f⁻¹ :=
  planeFrameEquivOf_θ_val N hN h _ f (planeSelf_mem hf) (planeSelf_eq h f) p

theorem planeSelfTwist_φ {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : (planeSelfTwist N hN hf).φ = phiPQ (planeSelf_mem hf) :=
  planeFrameEquivOf_φ N hN h _ f (planeSelf_mem hf) (planeSelf_eq h f)

theorem planeSelfTwist_α {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : (planeSelfTwist N hN hf).α = alphaP hN (planeSelf_mem hf) :=
  planeFrameEquivOf_α N hN h _ f (planeSelf_mem hf) (planeSelf_eq h f)

/-- **The Levi map of the self-twist is conjugation by `A_f`.** -/
theorem planeSelfTwist_glConj {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) : GLConj hN (planeSelfTwist N hN hf).α (planeSelfA hf) := by
  rw [planeSelfTwist_α]; exact alphaP_glConj hN (planeSelf_mem hf)

/-- **The determinant of the radical map of the self-twist is `det A_f`.** -/
theorem planeSelfTwist_radDet {h f : SL(3, ℤ)} (hf : h * f * h⁻¹ ∈ planeBorel) :
    radDet (planeSelfTwist N hN hf).φ.toMonoidHom = (planeSelfA hf).val.det := by
  rw [planeSelfTwist_φ, radDet_phiPQ, planeSelfA, AGP_det]

end Self

section BlockDiag

/-- The block diagonal element `diag(B, det B) ∈ SL₃(ℤ)` of `B ∈ GL₂(ℤ)`. -/
def planeBlockDiag (B : IntegralGL) : SL(3, ℤ) :=
  ⟨!![B.val 0 0, B.val 0 1, 0; B.val 1 0, B.val 1 1, 0; 0, 0, B.val.det], by
    have hu : IsUnit B.val.det := Matrix.isUnits_det_units B
    have hsq : B.val.det * B.val.det = 1 := by
      rcases Int.isUnit_iff.mp hu with h0 | h0 <;> rw [h0] <;> norm_num
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_fin_const]
    rw [Matrix.det_fin_two] at hsq ⊢
    linear_combination hsq⟩

theorem planeBlockDiag_mem (B : IntegralGL) : planeBlockDiag B ∈ planeBorel :=
  ⟨by simp [planeBlockDiag], by simp [planeBlockDiag]⟩

theorem topLeft_planeBlockDiag (B : IntegralGL) : topLeft (planeBlockDiag B) = B.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topLeft, planeBlockDiag]

/-- **Every `B ∈ GL₂(ℤ)` is the Levi element of a self-twist of the plane face at `h`.** -/
theorem exists_planeSelf (h : SL(3, ℤ)) (B : IntegralGL) :
    ∃ (f : SL(3, ℤ)) (hf : h * f * h⁻¹ ∈ planeBorel), planeSelfA hf = B := by
  have e : h * (h⁻¹ * planeBlockDiag B * h) * h⁻¹ = planeBlockDiag B := by group
  have hf : h * (h⁻¹ * planeBlockDiag B * h) * h⁻¹ ∈ planeBorel := by
    rw [e]; exact planeBlockDiag_mem B
  refine ⟨_, hf, Units.ext ?_⟩
  rw [planeSelfA_val, e, topLeft_planeBlockDiag]

end BlockDiag

end TernaryPeriodPolynomials.Argument.FrameInvariance
