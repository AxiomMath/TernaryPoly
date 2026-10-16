module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LALocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.Separation

@[expose] public section


/-!
# The local joint generalized eigenspace at the twisted good-line cusp has dimension at most one

For the odd character `χ` the composite of the transport `ψ` to `Λ₁` and the full good-line binary
edge is an injective map `H²(Γ_F, V) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` which turns `localOp` of `T_p`
into `sgnP p • 1 + (p^{n+2})⁻¹ • T_p`.  Hence it maps the local joint generalized eigenspace of the
pair character into the joint generalized eigenspace of level-one `H¹` for the eigenvalues
`(c(T_p) - sgnP p) / (p^{n+2})⁻¹`.  For even `n` the target vanishes; for odd `n` the eigenvalue at
`p = 2` (where `sgnP 2 = -1`) is within `(3/4) 2^{n+2}` of zero when `‖c(T_2) + 1‖ ≤ 3/4`, which is
below the Eisenstein bound `2^{n+3}`, so generalized multiplicity one applies.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen.Satake

namespace TernaryPeriodPolynomials.Twisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.ParabolicES

namespace LH

section Generic

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A map with `f (A v) = a • f v + s • B (f v)` (`s ≠ 0`) sends generalized eigenvectors of `A` of
eigenvalue `μ` to generalized eigenvectors of `B` of eigenvalue `(μ - a) / s`. -/
theorem map_mem_maxGenEigenspace_of_affineT (f : V →ₗ[ℂ] W) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (a s μ : ℂ) (hs : s ≠ 0)
    (hrel : ∀ v, f (A v) = a • f v + s • B (f v)) {v : V} (hv : v ∈ A.maxGenEigenspace μ) :
    f v ∈ B.maxGenEigenspace ((μ - a) / s) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hone : ∀ w : V, f ((A - μ • 1) w) = s • (B - ((μ - a) / s) • 1) (f w) := by
    intro w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, hrel, smul_sub, smul_smul]
    rw [mul_div_cancel₀ _ hs, sub_smul]
    abel
  have hpow : ∀ (m : ℕ) (w : V),
      f (((A - μ • 1) ^ m) w) = s ^ m • ((B - ((μ - a) / s) • 1) ^ m) (f w) := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, hone, map_smul, smul_smul, pow_succ, pow_succ,
        Module.End.mul_apply]
  have h := hpow k v
  rw [hk, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hs)

end Generic

end LH

/-- The `H¹` eigenvalues seen by the twisted good-line edge: `p^{n+2} (c(T_p) - sgnP p)`. -/
def eLineT (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) : ℂ :=
  (c (TpExistence.tp p) - ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ)) / ((p.val : ℂ) ^ (n + 2))⁻¹

/-- **The twisted good-line edge maps the local joint generalized eigenspace into the joint
generalized eigenspace of level-one `H¹`.** -/
theorem edgeH2LT_mem_jointH1 (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    {y : CuspH2 n χ .line true} (hy : y ∈ localJoint n χ c .line true) :
    edgeH2LT n χ hχ hn (psiLT n χ y) ∈ jointH1 (n + 1) (-1) (eLineT n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hyp := (Submodule.mem_iInf _).mp hy ⟨TpExistence.tp p, TpExistence.tp_awayThree p hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 2))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  exact LH.map_mem_maxGenEigenspace_of_affineT ((edgeH2LT n χ hχ hn).comp (psiLT n χ))
    (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p) _ _ _ hs
    (edgeH2LT_localOp_tp n χ hχ hn p hp3) hyp

/-- For odd `n`, the joint generalized eigenspace of level-one `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` for
the twisted line eigenvalues has dimension at most one. -/
theorem finrank_jointH1_eLineT_le_one {n : ℕ} (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LevelOneEisenstein.two) + 1‖ ≤ 3 / 4) :
    Module.finrank ℂ (jointH1 (n + 1) (-1) (eLineT n c)) ≤ 1 := by
  refine LevelOneEisenstein.finrank_jointH1_le_one_of_norm_lt hodd.add_one
    (Nat.succ_pos n) (-1) _ ?_
  have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - (-1)) = 2 ^ (n + 3) := by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 - (-1) = ((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : ‖((LevelOneEisenstein.two.val : ℕ) : ℂ)‖ = 2 := by
    simp [LevelOneEisenstein.two]
  have hs2 : IdentityPlaneLocalOp.sgnP LevelOneEisenstein.two = -1 := by
    simp [IdentityPlaneLocalOp.sgnP, LevelOneEisenstein.two]
  unfold eLineT
  rw [hs2, hexp, Int.cast_neg, Int.cast_one, sub_neg_eq_add, norm_div, norm_inv, norm_pow, h2,
    div_inv_eq_mul]
  have hpos : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  calc ‖c (TpExistence.tp LevelOneEisenstein.two) + 1‖ * 2 ^ (n + 2)
      ≤ 3 / 4 * 2 ^ (n + 2) := mul_le_mul_of_nonneg_right hc hpos.le
    _ < 2 ^ (n + 3) := by
      have hx : (2 : ℝ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
      rw [hx]
      linarith

/-- **The local joint generalized eigenspace at the twisted good-line cusp has dimension at most
one.** -/
theorem localJoint_goodLine_twisted_finite_le_one {n : ℕ} (hn : 0 < n) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4) :
    FiniteDimensional ℂ (localJoint n χ c .line true) ∧
      Module.finrank ℂ (localJoint n χ c .line true) ≤ 1 := by
  have hf : Function.Injective ((edgeH2LT n χ hχ hn).comp (psiLT n χ)) :=
    (edgeH2LT_injective n χ hχ hn).comp (psiLT_injective n χ)
  rcases Nat.even_or_odd n with heven | hodd
  · have hbot : localJoint n χ c .line true = ⊥ := by
      rw [eq_bot_iff]
      intro y _
      have h0 : ((edgeH2LT n χ hχ hn).comp (psiLT n χ)) y =
          ((edgeH2LT n χ hχ hn).comp (psiLT n χ)) 0 := by
        rw [map_zero]
        exact IdentityPlaneEven.arithmeticH1_eq_zero_of_odd (n + 1) (Even.add_one heven) (-1) _
      exact (Submodule.mem_bot ℂ).mpr (hf h0)
    rw [hbot]
    exact ⟨inferInstance, by simp⟩
  · have hJ := finrank_jointH1_eLineT_le_one hodd c hc
    have hJfd : FiniteDimensional ℂ (jointH1 (n + 1) (-1) (eLineT n c)) :=
      LevelOneEisenstein.jointH1_finiteDimensional (n + 1) (-1) (eLineT n c)
    let g : localJoint n χ c .line true →ₗ[ℂ] jointH1 (n + 1) (-1) (eLineT n c) :=
      ((edgeH2LT n χ hχ hn).comp (psiLT n χ)).restrict (fun _ hy => edgeH2LT_mem_jointH1 n χ hχ hn c hy)
    have hg : Function.Injective g := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
    have hKfd : FiniteDimensional ℂ (localJoint n χ c .line true) := Module.Finite.of_injective g hg
    exact ⟨hKfd, (LinearMap.finrank_le_finrank_of_injective hg).trans hJ⟩

end TernaryPeriodPolynomials.Twisted
