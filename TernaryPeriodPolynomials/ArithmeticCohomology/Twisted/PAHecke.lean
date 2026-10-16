module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PACoordinate

@[expose] public section


/-!
# The local `T_p` at the twisted identity plane is `sgnP p + p^{-(n+1)} T_p^{GL₂}` on the binary edge

For `χ(-1_∞) = -1` and the explicit local correspondence `identityPlaneCosets p` of the identity-plane
stabilizer `Λ₀ = ℤ² ⋊ GL₂(ℤ)`, the twisted binary edge
`E : H²(Λ₀, Sym^n ⊗ χ∘det) ↪ H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` (odd `n > 0`) intertwines the local Hecke
operator with `sgnP p + p^{-(n+1)} T_p`, where `T_p` is the cohomological Hecke operator
`LevelOneHeckeH1.arithmeticHecke` of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` and `sgnP p = ±1` is the sign of
`εp ≡ 1 (mod 3)` (`edgeH2T_hecke`).  The sign only comes from the representative `σ₀ = diag(1,1,εp)`;
the representatives `u(w) diag(B_j, 1)` have determinant `p > 0`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneEdge IdentityPlaneCoordinate
open LevelOneHeckeH1 HeckeH1 AmbientHecke LocalHecke

/-- A twist-`0` scalar acts on `Sym^d` by `u⁻ᵈ`. -/
theorem homogeneousAction_zero_scalar {d : ℕ} (f : Binary.HomogeneousPoly d) (unit : ℂˣ) :
    Binary.homogeneousAction d 0 (GeneralLinearGroup.scalar (Fin 2) unit) f =
      (unit.val⁻¹) ^ d • f := by
  have h := LinearMap.congr_fun
    (homogeneousAction_succ_twist d (-1) (GeneralLinearGroup.scalar (Fin 2) unit)) f
  rw [neg_add_cancel, LinearMap.smul_apply, binary_homogeneousAction_scalar, smul_smul,
    GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
  have hu : (unit.val : ℂ) ≠ 0 := unit.ne_zero
  have hs : ((unit ^ 2 : ℂˣ) : ℂ) * (unit.val⁻¹) ^ (d + 2) = (unit.val⁻¹) ^ d := by
    rw [Units.val_pow_eq_pow_val, pow_add]
    calc (unit.val) ^ 2 * ((unit.val⁻¹) ^ d * (unit.val⁻¹) ^ 2)
        = (unit.val * unit.val⁻¹) ^ 2 * (unit.val⁻¹) ^ d := by ring
      _ = (unit.val⁻¹) ^ d := by rw [mul_inv_cancel₀ hu, one_pow, one_mul]
  rw [h]
  exact congrArg (fun a : ℂ => a • f) hs

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (p : Nat.Primes)

/-- `ρ(α_j)⁻¹ = p^{n+1} ρ(B_j)` on `Sym^{n+1} ⊗ det⁰`. -/
theorem rho_rep_invT (j : Option (Fin p.val)) (v : arithmeticBinaryRep (n + 1) 0) :
    rationalRho (n + 1) 0 (binaryHeckeRepresentative p j)⁻¹ v =
      ((p.val : ℂ) ^ (n + 1)) • rationalRho (n + 1) 0 (BGL p j) v := by
  set u : ℚˣ := Units.mk0 (p.val : ℚ) (p_ne_zero p)
  have h := BGL_inv_eq p j
  have hrep : (binaryHeckeRepresentative p j)⁻¹ =
      BGL p j * GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
    rw [show binaryHeckeRepresentative p j =
      (GeneralLinearGroup.scalar (Fin 2) u⁻¹)⁻¹ * (BGL p j)⁻¹ by rw [h, inv_mul_cancel_left]]
    rw [_root_.mul_inv_rev, inv_inv, inv_inv]
  rw [hrep, map_mul, Module.End.mul_apply, ← map_smul]
  congr 1
  change Binary.homogeneousAction (n + 1) 0
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.scalar (Fin 2) u⁻¹))
      (v : Binary.HomogeneousPoly (n + 1)) = _
  rw [GeneralLinearGroup.map_scalar]
  refine (homogeneousAction_zero_scalar (v : Binary.HomogeneousPoly (n + 1)) _).trans ?_
  congr 1
  simp [u]

/-- The Hecke cocycle of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `Sym^{n+1} ⊗ det⁰`. -/
abbrev heckeZT : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ]
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep (n + 1) 0) (rationalRho (n + 1) 0)
    (arithmetic_compat (n + 1) 0) integralEmbed_injective

include hχ in
/-- **Cocycle-level identity**: `E(Tc) = sgnP p • E(c) + p^{-(n+1)} T_p E(c)`. -/
theorem edgeCycle_heckeT (c : RelT n χ) :
    identityPlaneBinaryEdgeCycleT n χ hχ (heckeRelT n χ p c) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • identityPlaneBinaryEdgeCycleT n χ hχ c +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeZT n p (identityPlaneBinaryEdgeCycleT n χ hχ c) := by
  have hp : ((p.val : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  apply groupCohomology.cocycles₁_ext
  intro m
  rw [binaryEdge_heckeT]
  have hz : heckeZT n p (identityPlaneBinaryEdgeCycleT n χ hχ c) m =
      ∑ j, rationalRho (n + 1) 0 (binaryHeckeRepresentative p j)⁻¹
        (identityPlaneBinaryEdgeCycleT n χ hχ c (arithmeticDelta p m j)) :=
    heckeCocycle_apply _ _ _ _ _ _ _
  have hsum : ∑ j : Option (Fin p.val), rationalRho (n + 1) 0 (BGL p j)
        (identityPlaneBinaryEdgeCycleT n χ hχ c (arithmeticDelta p m j)) =
      ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeZT n p (identityPlaneBinaryEdgeCycleT n χ hχ c) m := by
    rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [rho_rep_invT, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [hsum]
  rfl

variable (hn : 0 < n) (hodd : Odd n)

include hχ in
/-- **Class-level identity for relative cocycles.** -/
theorem fullEdge_heckeRelT (c : RelT n χ) :
    identityPlaneFullBinaryEdgeT n χ hχ hn hodd
        (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) (heckeRelT n χ p c).val) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • identityPlaneFullBinaryEdgeT n χ hχ hn hodd
          (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) c.val) +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • arithmeticHecke (n + 1) 0 p
          (identityPlaneFullBinaryEdgeT n χ hχ hn hodd
            (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) c.val)) := by
  rw [identityPlaneFullBinaryEdgeT_relative, identityPlaneFullBinaryEdgeT_relative,
    edgeCycle_heckeT n χ hχ p]
  simp only [map_add, map_smul]
  rw [arithmeticHecke, heckeH1_H1π]

/-- **The local Hecke operator at the twisted identity plane on the binary edge.** For every
ambient cocycle `C` of `Λ₀`, `E(T C) = sgnP p • E(C) + p^{-(n+1)} T_p E(C)`. -/
theorem ambientEdge_heckeT (C : cocycles Λ₀ (ρT n χ)) :
    identityPlaneAmbientBinaryEdgeT n χ hχ hn hodd
        (cocycleAction (ρT n χ) (identityPlaneCosets p) C) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • identityPlaneAmbientBinaryEdgeT n χ hχ hn hodd C +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • arithmeticHecke (n + 1) 0 p
          (identityPlaneAmbientBinaryEdgeT n χ hχ hn hodd C) := by
  rw [identityPlaneAmbientBinaryEdgeT_apply, identityPlaneAmbientBinaryEdgeT_apply]
  obtain ⟨c₁, hc₁⟩ := relativeTwoCocycleClass_surjective identityPlaneRadicalInclusion
    identityPlaneRadicalInclusion_injective (identityPlaneCoefficientRepT n χ)
    ⟨groupCohomology.H2π (identityPlaneCoefficientRepT n χ)
      (ambientCocycleToGroup Λ₀ (ρT n χ) C),
      identityPlaneH2_restriction_zeroT n χ hχ hn hodd _⟩
  have hc : groupCohomology.H2π (identityPlaneCoefficientRepT n χ) c₁.val =
      groupCohomology.H2π (identityPlaneCoefficientRepT n χ)
        (ambientCocycleToGroup Λ₀ (ρT n χ) C) :=
    congrArg Subtype.val hc₁
  have hcongr := ambientHecke_congr (identityPlaneCosets p) (ρT n χ) C
    (liftCocycle (identityPlaneCosets p) (ρT n χ) c₁.val)
    (by exact hc.symm.trans (congrArg (groupCohomology.H2π (identityPlaneCoefficientRepT n χ))
      (ambientCocycleToGroup_lift (identityPlaneCosets p) (ρT n χ) c₁.val).symm))
  have h1 : identityPlaneFullBinaryEdgeT n χ hχ hn hodd
      (groupCohomology.H2π (identityPlaneCoefficientRepT n χ)
        (ambientCocycleToGroup Λ₀ (ρT n χ) (cocycleAction (ρT n χ) (identityPlaneCosets p) C))) =
      identityPlaneFullBinaryEdgeT n χ hχ hn hodd
        (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) (heckeRelT n χ p c₁).val) :=
    congrArg (identityPlaneFullBinaryEdgeT n χ hχ hn hodd) hcongr
  rw [h1, fullEdge_heckeRelT n χ hχ p hn hodd, hc]

/-! ### On the ambient `H²(Λ₀, V)` -/

/-- The twisted binary edge on the ambient cohomology `H²(Λ₀, V_χ)`. -/
def edgeH2T : H2 Λ₀ (ρT n χ) →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (LinearMap.range (boundaryMap Λ₀ (ρT n χ))).liftQ
    (identityPlaneAmbientBinaryEdgeT n χ hχ hn hodd) (by
      rintro _ ⟨P, rfl⟩
      exact LinearMap.mem_ker.mpr
        ((identityPlaneAmbientBinaryEdgeT_zero_iff n χ hχ hn hodd _).mpr ⟨P, rfl⟩))

theorem edgeH2T_classOf (C : cocycles Λ₀ (ρT n χ)) :
    edgeH2T n χ hχ hn hodd (classOf Λ₀ (ρT n χ) C) =
      identityPlaneAmbientBinaryEdgeT n χ hχ hn hodd C := rfl

/-- **The twisted binary edge is injective on `H²(Λ₀, V_χ)`.** -/
theorem edgeH2T_injective : Function.Injective (edgeH2T n χ hχ hn hodd) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change edgeH2T n χ hχ hn hodd (classOf Λ₀ (ρT n χ) C) = 0 at hx
  rw [edgeH2T_classOf, identityPlaneAmbientBinaryEdgeT_zero_iff] at hx
  exact (classOf_eq_zero_iff Λ₀ (ρT n χ) C).mpr hx

/-- **The local Hecke operator of the twisted identity plane, identified.** On
`H²(Λ₀, Sym^n ⊗ χ∘det)` (odd `n > 0`), the binary edge intertwines the local Hecke operator of the
explicit correspondence `identityPlaneCosets p` with `sgnP p + p^{-(n+1)} T_p`, `T_p` the Hecke
operator of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)`. -/
theorem edgeH2T_hecke (x : H2 Λ₀ (ρT n χ)) :
    edgeH2T n χ hχ hn hodd (cohomologyAction (ρT n χ) (identityPlaneCosets p) x) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2T n χ hχ hn hodd x +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • arithmeticHecke (n + 1) 0 p (edgeH2T n χ hχ hn hodd x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change edgeH2T n χ hχ hn hodd
    (cohomologyAction (ρT n χ) (identityPlaneCosets p) (classOf Λ₀ (ρT n χ) C)) = _
  rw [cohomologyAction_classOf, edgeH2T_classOf, ambientEdge_heckeT n χ hχ p hn hodd]
  rfl

end TernaryPeriodPolynomials.Twisted
