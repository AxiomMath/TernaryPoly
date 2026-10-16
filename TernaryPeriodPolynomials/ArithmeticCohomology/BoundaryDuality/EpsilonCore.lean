module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EpsilonSplit
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CoreBridge

@[expose] public section


/-!
# Parabolic cup duality for `Γ₁'(3) = Γ₁(3) ⋊ ⟨ε⟩`

`ε = diag(-1, 1)` normalizes `Γ₁(3) = ⟨T, L⟩` (`εTε = T⁻¹`, `εLε = L⁻¹`).  For representations
`ρ, ρ'` of `Γ₁'(3)` paired by a perfect `B` which is `Γ₁(3)`-invariant and changes sign under `ε`
(the twist by the determinant), an `ε`-invariant parabolic crossed homomorphism of `Γ₁(3)` which pairs
to zero with every `ε`-invariant parabolic one is the coboundary of an `ε`-invariant vector: Poincaré
duality for the parabolic cohomology of `Γ₁'(3)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.EpsilonCore

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree FreeProduct

/-- Conjugation by `ε` as an automorphism of `Γ₁(3)`. -/
def coreSigma : core →* core where
  toFun h := ⟨reflection * h.1 * reflection, conj_mem_core h.2⟩
  map_one' := Subtype.ext (by
    show reflection * 1 * reflection = 1
    rw [mul_one, reflection_mul_self])
  map_mul' g h := Subtype.ext (by
    show reflection * (g.1 * h.1) * reflection =
      (reflection * g.1 * reflection) * (reflection * h.1 * reflection)
    calc reflection * (g.1 * h.1) * reflection
        = reflection * g.1 * (1 : binaryArithmeticLevel) * h.1 * reflection := by
          simp only [mul_assoc, one_mul]
      _ = reflection * g.1 * (reflection * reflection) * h.1 * reflection := by
          rw [reflection_mul_self]
      _ = (reflection * g.1 * reflection) * (reflection * h.1 * reflection) := by
          simp only [mul_assoc])

theorem coreSigma_coe (h : core) :
    ((coreSigma h : core) : binaryArithmeticLevel) = reflection * h.1 * reflection := rfl

theorem coreSigma_sigma (h : core) : coreSigma (coreSigma h) = h := by
  apply Subtype.ext
  rw [coreSigma_coe, coreSigma_coe]
  calc reflection * (reflection * h.1 * reflection) * reflection
      = (reflection * reflection) * h.1 * (reflection * reflection) := by
        simp only [mul_assoc]
    _ = h.1 := by rw [reflection_mul_self, one_mul, mul_one]

theorem coreSigma_T : coreSigma coreT = coreT⁻¹ := by
  apply Subtype.ext
  rw [coreSigma_coe]
  change reflection * upper 1 * reflection = (upper 1)⁻¹
  rw [reflection_conj_upper, upper_zpow (-1), zpow_neg_one]

theorem coreSigma_L : coreSigma coreL = coreL⁻¹ := by
  apply Subtype.ext
  rw [coreSigma_coe]
  change reflection * lower 1 * reflection = (lower 1)⁻¹
  rw [reflection_conj_lower, lower_zpow (-1), zpow_neg_one]

theorem coreSigma_Linv : coreSigma coreL⁻¹ = (coreL⁻¹)⁻¹ := by
  rw [map_inv, coreSigma_L]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ binaryArithmeticLevel V) (ρ' : Representation ℂ binaryArithmeticLevel W)
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

theorem reflection_equiv {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ binaryArithmeticLevel M) (h : core) (v : M) :
    ρ reflection (ρ h.1 v) = ρ (coreSigma h).1 (ρ reflection v) := by
  have key : reflection * h.1 = reflection * h.1 * reflection * reflection := by
    calc reflection * h.1 = reflection * h.1 * (reflection * reflection) := by
          rw [reflection_mul_self, mul_one]
      _ = reflection * h.1 * reflection * reflection := by simp only [mul_assoc]
  calc ρ reflection (ρ h.1 v) = ρ (reflection * h.1) v := (rep_mul_apply ρ _ _ _).symm
    _ = ρ (reflection * h.1 * reflection * reflection) v := congrArg (fun x => ρ x v) key
    _ = ρ (reflection * h.1 * reflection) (ρ reflection v) := rep_mul_apply ρ _ _ _
    _ = ρ (coreSigma h).1 (ρ reflection v) := by rw [coreSigma_coe]

theorem reflection_reflection {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ binaryArithmeticLevel M) (v : M) :
    ρ reflection (ρ reflection v) = v := by
  rw [← rep_mul_apply, reflection_mul_self, map_one, Module.End.one_apply]

/-- The reflection data for `Γ₁'(3)` acting on a perfectly paired twisted pair of representations. -/
def reflectData (hcore : ∀ g : core, ∀ v w, B (ρ g.1 v) (ρ' g.1 w) = B v w)
    (hε : ∀ v w, B (ρ reflection v) (ρ' reflection w) = (-1 : ℂ) * B v w) :
    ReflectData (ρ.comp core.subtype) (ρ'.comp core.subtype) B coreT coreL⁻¹ (-1 : ℂ) where
  σ := coreSigma
  e := ρ reflection
  e' := ρ' reflection
  σσ := coreSigma_sigma
  ee := reflection_reflection ρ
  ee' := reflection_reflection ρ'
  equiv := fun h v => reflection_equiv ρ h v
  equiv' := fun h w => reflection_equiv ρ' h w
  sa := coreSigma_T
  sg := coreSigma_Linv
  pair := hε
  invA := fun v w => hcore coreT v w
  invG := fun v w => hcore coreL⁻¹ v w

/-- **Left nondegeneracy of the parabolic cup pairing on `Γ₁'(3)`**: an `ε`-invariant parabolic
crossed homomorphism of `Γ₁(3)` which pairs to zero with every `ε`-invariant parabolic one is the
coboundary of an `ε`-invariant vector. -/
theorem left_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hcore : ∀ g : core, ∀ v w, B (ρ g.1 v) (ρ' g.1 w) = B v w)
    (hε : ∀ v w, B (ρ reflection v) (ρ' reflection w) = (-1 : ℂ) * B v w)
    {z : core → V} (hz : IsCocycle (ρ.comp core.subtype) z) {v : V × V × V}
    (hv : IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹ z v)
    (zinv : reflect coreSigma (ρ reflection) z = z)
    (zero : ∀ (z' : core → W) (v' : W × W × W), IsCocycle (ρ'.comp core.subtype) z' →
      IsPrimitive (ρ'.comp core.subtype) coreT coreL⁻¹ z' v' →
      reflect coreSigma (ρ' reflection) z' = z' →
      cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹ z z' v = 0) :
    ∃ u : V, ρ reflection u = u ∧ ∀ g : core, z g = ρ g.1 u - u :=
  left_nondegenerate_reflect (ρ := ρ.comp core.subtype) (ρ' := ρ'.comp core.subtype) (B := B)
    hL hR (fun g v w => hcore g v w) (reflectData ρ ρ' hcore hε)
    (CoreBridge.generated (ρ.comp core.subtype))
    (fun _ hv' => CoreBridge.exists_cocycle_primitive (ρ'.comp core.subtype) hv')
    hz hv zinv zero

/-- A crossed homomorphism of `Γ₁'(3)` which vanishes at `ε` restricts to an `ε`-invariant one on `Γ₁(3)`. -/
theorem restrict_invariant (ρ : Representation ℂ binaryArithmeticLevel V)
    {z : binaryArithmeticLevel → V} (hz : IsCocycle ρ z) (hε0 : z reflection = 0) :
    reflect coreSigma (ρ reflection) (fun h : core => z h.1) = fun h : core => z h.1 := by
  funext h
  have e1 : reflection * h.1 * reflection = reflection * (h.1 * reflection) := by
    rw [mul_assoc]
  have e2 := hz reflection (h.1 * reflection)
  have e3 := hz h.1 reflection
  rw [← e1, hε0, zero_add] at e2
  rw [hε0, map_zero, add_zero] at e3
  show ρ reflection (z (reflection * h.1 * reflection)) = z h.1
  rw [e2, e3, reflection_reflection]

/-- A coboundary of an `ε`-invariant vector on `Γ₁(3)` is a coboundary on `Γ₁'(3)` for a crossed
homomorphism vanishing at `ε`. -/
theorem boundary_of_core (ρ : Representation ℂ binaryArithmeticLevel V)
    {z : binaryArithmeticLevel → V} (hz : IsCocycle ρ z) (hε0 : z reflection = 0) {u : V}
    (hu : ρ reflection u = u) (h : ∀ g : core, z g.1 = ρ g.1 u - u) :
    ∀ g, z g = ρ g u - u := by
  intro g
  rcases mem_core_or g with hg | hg
  · exact h ⟨g, hg⟩
  · have e1 : (g * reflection) * reflection = g := by
      rw [mul_assoc, reflection_mul_self, mul_one]
    have := hz (g * reflection) reflection
    rw [e1, hε0, map_zero, add_zero] at this
    have h2 : z (g * reflection) = ρ (g * reflection) u - u := h ⟨g * reflection, hg⟩
    rw [this, h2, rep_mul_apply, hu]

end TernaryPeriodPolynomials.BoundaryDuality.EpsilonCore
