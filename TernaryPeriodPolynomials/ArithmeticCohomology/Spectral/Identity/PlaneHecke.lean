module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge

@[expose] public section


/-!
# The local `T_p` at the identity plane is `1 + p^{-(n+2)} T_p^{GL₂}` on the binary edge

For the explicit local correspondence `identityPlaneCosets p` of the identity-plane stabilizer
`Λ₀ = ℤ² ⋊ GL₂(ℤ)` (`1 + p + p²` cosets: `σ₀ = diag(1, 1, ±p)` and `u(w_{j,r}) diag(B_j, 1)`),
the Sol binary edge `E : H²(Λ₀, Sym^n ⊗ det⁻¹) ≅ H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` (odd `n > 0`)
intertwines the local Hecke operator with `1 + p^{-(n+2)} T_p`, where `T_p` is the cohomological Hecke
operator `LevelOneHeckeH1.arithmeticHecke` of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)`
(`ambientEdge_hecke`, `ambientEdgeH2_hecke`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneEdge IdentityPlaneCoordinate
open LevelOneHeckeH1 HeckeH1 AmbientHecke LocalHecke

variable (n : ℕ) (p : Nat.Primes)

/-- `ρ(α_j)⁻¹ = p^{n+3} ρ(B_j)` on `Sym^{n+1} ⊗ det⁻¹`. -/
theorem rho_rep_inv (j : Option (Fin p.val)) (v : arithmeticBinaryRep (n + 1) (-1)) :
    rationalRho (n + 1) (-1) (binaryHeckeRepresentative p j)⁻¹ v =
      ((p.val : ℂ) ^ (n + 3)) • rationalRho (n + 1) (-1) (BGL p j) v := by
  set u : ℚˣ := Units.mk0 (p.val : ℚ) (p_ne_zero p)
  have h := BGL_inv_eq p j
  have hrep : (binaryHeckeRepresentative p j)⁻¹ =
      BGL p j * GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
    rw [show binaryHeckeRepresentative p j =
      (GeneralLinearGroup.scalar (Fin 2) u⁻¹)⁻¹ * (BGL p j)⁻¹ by rw [h, inv_mul_cancel_left]]
    rw [_root_.mul_inv_rev, inv_inv, inv_inv]
  rw [hrep, map_mul, Module.End.mul_apply, ← map_smul]
  congr 1
  change Binary.homogeneousAction (n + 1) (-1)
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.scalar (Fin 2) u⁻¹))
      (v : Binary.HomogeneousPoly (n + 1)) = _
  rw [GeneralLinearGroup.map_scalar]
  refine (binary_homogeneousAction_scalar (v : Binary.HomogeneousPoly (n + 1)) _).trans ?_
  congr 1
  simp [u]

theorem cast_p : (((p.val : ℚ) : ℂ)) = ((p.val : ℂ) ^ (n + 2))⁻¹ * (p.val : ℂ) ^ (n + 3) := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp
  push_cast
  ring

/-- The Hecke cocycle of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `Sym^{n+1} ⊗ det⁻¹`. -/
abbrev heckeZ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) →ₗ[ℂ]
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) :=
  heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep (n + 1) (-1)) (rationalRho (n + 1) (-1))
    (arithmetic_compat (n + 1) (-1)) integralEmbed_injective

/-- **Cocycle-level identity**: `E(Tc) = E(c) + p^{-(n+2)} T_p E(c)`. -/
theorem edgeCycle_hecke (c : Rel n) :
    identityPlaneBinaryEdgeCycle n (heckeRel n p c) =
      identityPlaneBinaryEdgeCycle n c +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • heckeZ n p (identityPlaneBinaryEdgeCycle n c) := by
  apply groupCohomology.cocycles₁_ext
  intro m
  rw [binaryEdge_hecke]
  have hz : heckeZ n p (identityPlaneBinaryEdgeCycle n c) m =
      ∑ j, rationalRho (n + 1) (-1) (binaryHeckeRepresentative p j)⁻¹
        (identityPlaneBinaryEdgeCycle n c (arithmeticDelta p m j)) :=
    heckeCocycle_apply _ _ _ _ _ _ _
  have hsum : ((p.val : ℚ) : ℂ) • ∑ j : Option (Fin p.val), rationalRho (n + 1) (-1) (BGL p j)
        (identityPlaneBinaryEdgeCycle n c (arithmeticDelta p m j)) =
      ((p.val : ℂ) ^ (n + 2))⁻¹ • heckeZ n p (identityPlaneBinaryEdgeCycle n c) m := by
    rw [hz, cast_p n p, mul_smul]
    refine congrArg _ ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => (rho_rep_inv n p j _).symm)
  rw [hsum]
  rfl

variable (hn : 0 < n) (hodd : Odd n)

/-- **Class-level identity for relative cocycles.** -/
theorem fullEdge_heckeRel (c : Rel n) :
    identityPlaneFullBinaryEdge n hn hodd
        (groupCohomology.H2π (identityPlaneCoefficientRep n) (heckeRel n p c).val) =
      identityPlaneFullBinaryEdge n hn hodd (groupCohomology.H2π (identityPlaneCoefficientRep n) c.val) +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p
          (identityPlaneFullBinaryEdge n hn hodd (groupCohomology.H2π (identityPlaneCoefficientRep n) c.val)) := by
  rw [identityPlaneFullBinaryEdge_relative, identityPlaneFullBinaryEdge_relative, edgeCycle_hecke,
    map_add, map_smul, arithmeticHecke, heckeH1_H1π]

/-- **The local Hecke operator at the identity plane on the binary edge.** For every ambient
cocycle `C` of `Λ₀`, `E(T C) = E(C) + p^{-(n+2)} T_p E(C)`. -/
theorem ambientEdge_hecke (C : cocycles Λ₀ (ρn n)) :
    identityPlaneAmbientBinaryEdge n hn hodd trivialCharacter rfl
        (cocycleAction (ρn n) (identityPlaneCosets p) C) =
      identityPlaneAmbientBinaryEdge n hn hodd trivialCharacter rfl C +
        ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p
          (identityPlaneAmbientBinaryEdge n hn hodd trivialCharacter rfl C) := by
  rw [identityPlaneAmbientBinaryEdge_apply, identityPlaneAmbientBinaryEdge_apply]
  obtain ⟨c₁, hc₁⟩ := relativeTwoCocycleClass_surjective identityPlaneRadicalInclusion
    identityPlaneRadicalInclusion_injective (identityPlaneCoefficientRep n)
    ⟨groupCohomology.H2π (identityPlaneCoefficientRep n) (ambientCocycleToGroup Λ₀ (ρn n) C),
      identityPlaneH2_restriction_zero n hn hodd _⟩
  have hc : groupCohomology.H2π (identityPlaneCoefficientRep n) c₁.val =
      groupCohomology.H2π (identityPlaneCoefficientRep n) (ambientCocycleToGroup Λ₀ (ρn n) C) :=
    congrArg Subtype.val hc₁
  have hcongr := ambientHecke_congr (identityPlaneCosets p) (ρn n) C
    (liftCocycle (identityPlaneCosets p) (ρn n) c₁.val)
    (by exact hc.symm.trans (congrArg (groupCohomology.H2π (identityPlaneCoefficientRep n))
      (ambientCocycleToGroup_lift (identityPlaneCosets p) (ρn n) c₁.val).symm))
  have h1 : identityPlaneFullBinaryEdge n hn hodd (groupCohomology.H2π (identityPlaneCoefficientRep n)
      (ambientCocycleToGroup Λ₀ (ρn n) (cocycleAction (ρn n) (identityPlaneCosets p) C))) =
      identityPlaneFullBinaryEdge n hn hodd
        (groupCohomology.H2π (identityPlaneCoefficientRep n) (heckeRel n p c₁).val) :=
    congrArg (identityPlaneFullBinaryEdge n hn hodd) hcongr
  rw [h1, fullEdge_heckeRel, hc]

/-! ### On the ambient `H²(Λ₀, V)` -/

/-- The binary edge on the ambient cohomology `H²(Λ₀, V)`. -/
def edgeH2 : H2 Λ₀ (ρn n) →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (LinearMap.range (boundaryMap Λ₀ (ρn n))).liftQ
    (identityPlaneAmbientBinaryEdge n hn hodd trivialCharacter rfl) (by
      rintro _ ⟨P, rfl⟩
      exact LinearMap.mem_ker.mpr
        ((identityPlaneAmbientBinaryEdge_zero_iff n hn hodd trivialCharacter rfl _).mpr ⟨P, rfl⟩))

theorem edgeH2_classOf (C : cocycles Λ₀ (ρn n)) :
    edgeH2 n hn hodd (classOf Λ₀ (ρn n) C) =
      identityPlaneAmbientBinaryEdge n hn hodd trivialCharacter rfl C := rfl

/-- **The binary edge is injective on `H²(Λ₀, V)`.** -/
theorem edgeH2_injective : Function.Injective (edgeH2 n hn hodd) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change edgeH2 n hn hodd (classOf Λ₀ (ρn n) C) = 0 at hx
  rw [edgeH2_classOf, identityPlaneAmbientBinaryEdge_zero_iff] at hx
  exact (classOf_eq_zero_iff Λ₀ (ρn n) C).mpr hx

/-- **The local Hecke operator of the identity plane, identified.** On `H²(Λ₀, Sym^n ⊗ det⁻¹)`
(odd `n > 0`), the binary edge intertwines the local Hecke operator of the explicit correspondence
`identityPlaneCosets p` with `1 + p^{-(n+2)} T_p`, `T_p` the Hecke operator of
`GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
theorem edgeH2_hecke (x : H2 Λ₀ (ρn n)) :
    edgeH2 n hn hodd (cohomologyAction (ρn n) (identityPlaneCosets p) x) =
      edgeH2 n hn hodd x + ((p.val : ℂ) ^ (n + 2))⁻¹ • arithmeticHecke (n + 1) (-1) p (edgeH2 n hn hodd x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change edgeH2 n hn hodd (cohomologyAction (ρn n) (identityPlaneCosets p) (classOf Λ₀ (ρn n) C)) = _
  rw [cohomologyAction_classOf, edgeH2_classOf, ambientEdge_hecke]
  rfl

end TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
