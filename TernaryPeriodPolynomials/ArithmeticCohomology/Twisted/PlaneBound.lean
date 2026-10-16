module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PALocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneEven
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.LocalMultiplicity

@[expose] public section


/-!
# Local multiplicity at the twisted identity-plane cusp

Let `χ(-1_∞) = -1` and let `c` be a character of the away-three Hecke algebra with
`‖c(T_2) + 1‖ ≤ 3/4` (the cuspidal pair character of the odd quadratic character of conductor three
for `n ≥ 3`).  For odd `n` the twisted binary edge embeds the local joint generalized eigenspace at
the identity plane into the joint generalized eigenspace of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` with
eigenvalues `e_p = (c(T_p) - sgnP p) · p^{n+1}`; at `p = 2` (where `sgnP 2 = -1`) this has norm at
most `(3/4) 2^{n+1} < 2^{n+2}`, so the eigenspace is spanned by period classes and has dimension at
most one.  For even `n` the local cohomology vanishes.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.LevelOneEisenstein

namespace TernaryPeriodPolynomials.Twisted

section Generic

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A map with `f (A v) = a • f v + s • B (f v)` (`s ≠ 0`) sends generalized eigenvectors of `A` of
eigenvalue `μ` to generalized eigenvectors of `B` of eigenvalue `(μ - a) / s`. -/
theorem map_mem_maxGenEigenspace_of_affineT (f : V →ₗ[ℂ] W) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (a s μ : ℂ) (hs : s ≠ 0)
    (hrel : ∀ v, f (A v) = a • f v + s • B (f v))
    {v : V} (hv : v ∈ A.maxGenEigenspace μ) : f v ∈ B.maxGenEigenspace ((μ - a) / s) := by
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

/-- The `H¹` eigenvalues seen by the twisted identity-plane edge: `p^{n+1} (c(T_p) - sgnP p)`. -/
def eIdentityT (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) : ℂ :=
  (c (TpExistence.tp p) - ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ)) / ((p.val : ℂ) ^ (n + 1))⁻¹

/-- The sign of the prime two. -/
theorem sgnP_two : IdentityPlaneLocalOp.sgnP LocalUniqueness.two = -1 := by
  unfold IdentityPlaneLocalOp.sgnP
  decide

section Edge

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (c : HeckeCorrespondence → ℂ) (hn : 0 < n) (hodd : Odd n)

/-- **The twisted identity-plane edge maps the local joint generalized eigenspace into the joint
generalized eigenspace of level-one `H¹`.** -/
theorem edgeH2T_mem_jointH1 {x : CuspH2 n χ .plane false}
    (hx : x ∈ localJoint n χ c .plane false) :
    edgeH2T n χ hχ hn hodd x ∈ jointH1 (n + 1) 0 (eIdentityT n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hxp := (Submodule.mem_iInf _).mp hx ⟨TpExistence.tp p, TpExistence.tp_awayThree p hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  exact map_mem_maxGenEigenspace_of_affineT (edgeH2T n χ hχ hn hodd)
    (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p) _ _ _ hs
    (edgeH2T_localOp_tp n χ hχ p hn hodd hp3) hxp

end Edge

/-- **Twisted identity-plane cusp: local multiplicity at most one.** -/
theorem localJoint_identityPlane_twisted_finite_le_one {n : ℕ} (hn : 0 < n) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4) :
    FiniteDimensional ℂ (localJoint n χ c .plane false) ∧
      Module.finrank ℂ (localJoint n χ c .plane false) ≤ 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · rw [localJoint_identityPlane_eq_botT n χ hχ hn heven c]
    exact ⟨inferInstance, by simp⟩
  · have : FiniteDimensional ℂ (jointH1 (n + 1) 0 (eIdentityT n c)) :=
      jointH1_finiteDimensional _ _ _
    refine ⟨finiteDimensional_of_injective_map (edgeH2T n χ hχ hn hodd) (edgeH2T_injective n χ hχ hn hodd)
      _ (jointH1 (n + 1) 0 (eIdentityT n c)) (fun _ hx => edgeH2T_mem_jointH1 n χ hχ c hn hodd hx),
      (LocalUniqueness.finrank_le_of_injective_map (edgeH2T n χ hχ hn hodd) (edgeH2T_injective n χ hχ hn hodd) _ _
        (fun _ hx => edgeH2T_mem_jointH1 n χ hχ c hn hodd hx)).trans ?_⟩
    refine finrank_jointH1_le_one_of_norm_lt hodd.add_one (Nat.succ_pos n) 0 _ ?_
    have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
      rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have h2 : ‖((LocalUniqueness.two.val : ℕ) : ℂ)‖ = 2 := by simp [LocalUniqueness.two]
    rw [hexp]
    change ‖eIdentityT n c LocalUniqueness.two‖ < 2 ^ (n + 2)
    have hE : eIdentityT n c LocalUniqueness.two =
        (c (TpExistence.tp LocalUniqueness.two) + 1) * ((LocalUniqueness.two.val : ℂ) ^ (n + 1)) := by
      unfold eIdentityT
      rw [sgnP_two, Int.cast_neg, Int.cast_one, sub_neg_eq_add, div_inv_eq_mul]
    rw [hE, norm_mul, norm_pow, h2]
    have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    calc ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ * 2 ^ (n + 1) ≤ 3 / 4 * 2 ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hc hpos.le
      _ < 2 ^ (n + 2) := by
        have hx : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
        rw [hx]
        linarith

end TernaryPeriodPolynomials.Twisted
