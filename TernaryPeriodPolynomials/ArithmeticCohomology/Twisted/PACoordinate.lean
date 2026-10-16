module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PARes
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneCycle

@[expose] public section


/-!
# The binary coordinate of the twisted identity-plane edge under the local Hecke operator

The restricted generator values of the edge cocycle of a relative two-cocycle `c` of the
identity-plane stabilizer `Λ₀ = ℤ² ⋊ GL₂(ℤ)` with sign-twisted coefficients are
`lamT c μ k = res (ζ_μ(e_k))`.  By `PARes` the restricted generator values of the Hecke image `T c` are
`sgnP p • lamT c m k + ∑_j A⁰_{B_j} (∑_i (B_j⁻¹)_{ik} lamT c μ_j i)`, with `A⁰` the binary action of
twist `0`.  Applying the twist-`0` contraction `(l₀, l₁) ↦ (n+1)⁻¹ (X₀ l₀ + X₁ l₁)` gives the exact
cocycle-level identity
`E(T c)(m) = sgnP p • E(c)(m) + ∑_j ρ_{(n+1),0}(B_j) E(c)(μ_j)` (`binaryEdge_heckeT`) in
`Sym^{n+1} ⊗ det⁰`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneTransitions IdentityPlaneEdge
  IdentityPlaneCoordinate

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (p : Nat.Primes)

/-- The relative two-cocycles of the twisted identity-plane stabilizer. -/
abbrev RelT := relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)

/-- The restricted generator values of the edge at `μ`. -/
abbrev lamT (c : RelT n χ) (μ : GL (Fin 2) ℤ) : Fin 2 → Binary.HomogeneousPoly n :=
  genRes n (identityPlaneRadicalEdgeCycleT n χ c μ)

theorem edgeFun_eqT (c : RelT n χ) (m : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    edgeFun (ρT n χ) c.val m y = identityPlaneRadicalEdgeCycleT n χ c m (Multiplicative.ofAdd y) := by
  rw [identityPlaneSplitEdgeCycleT_apply, inl_eq, inl_eq, splitting_eq]
  rfl

theorem res_edgeFunT (c : RelT n χ) (m : GL (Fin 2) ℤ) (y : ℤ × ℤ) :
    res n (edgeFun (ρT n χ) c.val m y) = Lam (lamT n χ c m) (icast y) := by
  rw [edgeFun_eqT]
  exact res_cocycle n _ y

theorem rel_UelT (c : RelT n χ) (a b : ℤ × ℤ) : c.val (Uel a, Uel b) = 0 := by
  have h := c.2 (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rwa [inl_eq, inl_eq] at h

/-- The Hecke image as a relative cocycle. -/
def heckeRelT (c : RelT n χ) : RelT n χ :=
  ⟨heckeTwo p (ρT n χ) c.val, by
    intro u v
    rw [inl_eq, inl_eq]
    exact heckeTwo_relative p (ρT n χ) c.val (rel_UelT n χ c) _ _⟩

theorem lam_generatorT (c : RelT n χ) (μ : GL (Fin 2) ℤ) (k : Fin 2) :
    lamT n χ c μ k = res n (edgeFun (ρT n χ) c.val μ (if k = 0 then (1, 0) else (0, 1))) := by
  rw [edgeFun_eqT]
  unfold lamT genRes radicalLatticeGenerator radicalLatticeFirst radicalLatticeSecond
  split_ifs <;> rfl

/-- The function-valued Hecke term attached to the coset `B_j`. -/
def termT (j : Option (Fin p.val)) (l : Fin 2 → Binary.HomogeneousPoly n) :
    Fin 2 → Binary.HomogeneousPoly n := fun k => AbinT n (BGL p j)
  ((((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 0 k : ℂ) • l 0 + (((BGL p j)⁻¹ : GL (Fin 2) ℚ).val 1 k : ℂ) • l 1)

include hχ in
/-- **The restricted generator values of the twisted Hecke image.** -/
theorem lam_heckeT_fun (c : RelT n χ) (m : GL (Fin 2) ℤ) :
    lamT n χ (heckeRelT n χ p c) m = ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • lamT n χ c m +
      ∑ j : Option (Fin p.val), termT n p j (lamT n χ c (arithmeticDelta p m j)) := by
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  rw [lam_generatorT n χ (heckeRelT n χ p c) m k]
  exact lam_heckeT n p χ hχ c.val (rel_UelT n χ c) (lamT n χ c) (res_edgeFunT n χ c) m k

/-! ### The binary coordinate -/

/-- The contraction `(l₀, l₁) ↦ (n+1)⁻¹ (X₀ l₀ + X₁ l₁)`. -/
def PhiT : (Fin 2 → Binary.HomogeneousPoly n) →ₗ[ℂ] Binary.Poly where
  toFun l := (n + 1 : ℂ)⁻¹ • (MvPolynomial.X 0 * (l 0).val + MvPolynomial.X 1 * (l 1).val)
  map_add' l l' := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, smul_add]
    abel
  map_smul' a l := by
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, mul_smul_comm, ← smul_add]
    exact smul_comm _ _ _

theorem PhiT_apply (l : Fin 2 → Binary.HomogeneousPoly n) :
    PhiT n l = (n + 1 : ℂ)⁻¹ • (MvPolynomial.X 0 * (l 0).val + MvPolynomial.X 1 * (l 1).val) := rfl

theorem binaryEdge_valT (c : RelT n χ) (μ : GL (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycleT n χ hχ c μ).val = PhiT n (lamT n χ c μ) := by
  rw [identityPlaneBinaryEdgeCycleT_apply, upperRadicalCocycleCoordinate_value, PhiT_apply]
  rfl

/-- **The twist-`0` binary action of `B` on a radical coordinate.** -/
theorem PhiT_equivariant (B : GL (Fin 2) ℚ) (l : Fin 2 → Binary.HomogeneousPoly n) :
    PhiT n (fun k => AbinT n B ((((B⁻¹ : GL (Fin 2) ℚ).val 0 k : ℚ) : ℂ) • l 0 +
      (((B⁻¹ : GL (Fin 2) ℚ).val 1 k : ℚ) : ℂ) • l 1)) =
      Binary.action 0 (cx2 B) (PhiT n l) := by
  rw [PhiT_apply, PhiT_apply, map_smul,
    ← binaryPairContraction_equivariant 0 (cx2 B) (fun i => (l i).val)]
  simp only [cx2_inv_val, map_add, map_smul, Binary.homogeneousAction_coe, Submodule.coe_add,
    Submodule.coe_smul]

/-- The underlying polynomial of a binary coefficient. -/
abbrev polyValT : arithmeticBinaryRep (n + 1) 0 →ₗ[ℂ] Binary.Poly :=
  (Binary.HomogeneousPoly (n + 1)).subtype

/-- **Cocycle-level Hecke formula for the twisted identity-plane binary edge.** For a relative
two-cocycle `c`, the binary edge cocycle of its local Hecke image is
`E(Tc)(m) = sgnP p • E(c)(m) + ∑_j ρ_{(n+1),0}(B_j) E(c)(μ_j)`, where `B_j a_j = p` and
`a_j m = μ_j a_{k_j}`. -/
theorem binaryEdge_heckeT (c : RelT n χ) (m : GL (Fin 2) ℤ) :
    identityPlaneBinaryEdgeCycleT n χ hχ (heckeRelT n χ p c) m =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • identityPlaneBinaryEdgeCycleT n χ hχ c m +
        ∑ j : Option (Fin p.val), LevelOneHeckeH1.rationalRho (n + 1) 0 (BGL p j)
          (identityPlaneBinaryEdgeCycleT n χ hχ c (arithmeticDelta p m j)) := by
  apply (show Function.Injective (polyValT n) from Subtype.val_injective)
  rw [map_add, map_smul, map_sum]
  change (identityPlaneBinaryEdgeCycleT n χ hχ (heckeRelT n χ p c) m).val =
    ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • (identityPlaneBinaryEdgeCycleT n χ hχ c m).val +
      ∑ j : Option (Fin p.val), Binary.action 0 (cx2 (BGL p j))
        (identityPlaneBinaryEdgeCycleT n χ hχ c (arithmeticDelta p m j)).val
  rw [binaryEdge_valT n χ hχ, binaryEdge_valT n χ hχ, lam_heckeT_fun n χ hχ p c m, map_add,
    map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [binaryEdge_valT n χ hχ]
  exact PhiT_equivariant n (BGL p j) (lamT n χ c (arithmeticDelta p m j))

end TernaryPeriodPolynomials.Twisted
