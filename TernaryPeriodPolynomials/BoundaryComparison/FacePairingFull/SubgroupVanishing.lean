module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AmbientResolution

@[expose] public section


/-!
# Restriction of a homogeneous two-class to a subgroup vanishes from an inhomogeneous primitive

For subgroups `Γe ≤ Γ0` of `GL₃(ℚ)`, a homogeneous two-cocycle `original` of `Γ0` whose
inhomogeneous form `(a, b) ↦ original(1, a, ab)` is the inhomogeneous boundary of a function
`q : Γe → V` on `Γe` restricts to a coboundary on `Γe`
(`subgroupRestrictionH2_classOf_eq_zero`). This is the direction opposite to the extraction of
inhomogeneous primitives from homogeneous ones in `InnerEdgePrimitives`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A homogeneous two-cocycle is determined by its inhomogeneous form on the subgroup. -/
theorem cocycle_apply_of_mem {Γ0 : Subgroup RationalGL3} {ρ : Representation ℂ RationalGL3 V}
    (original : cochains Γ0 ρ 2) (x0 x1 x2 : RationalGL3) (h0 : x0 ∈ Γ0) :
    original.val ![x0, x1, x2] =
      ρ x0 (original.val ![1, x0⁻¹ * x1, x0⁻¹ * x2]) := by
  have h := original.property ⟨x0⁻¹, Γ0.inv_mem h0⟩ ![x0, x1, x2]
  have hv : (fun i => x0⁻¹ * (![x0, x1, x2] : Fin 3 → RationalGL3) i) =
      ![1, x0⁻¹ * x1, x0⁻¹ * x2] := by
    funext i
    fin_cases i <;> simp
  change original.val (fun i => x0⁻¹ * ![x0, x1, x2] i) = ρ x0⁻¹ (original.val ![x0, x1, x2]) at h
  rw [hv] at h
  rw [h, ← Module.End.mul_apply, ← map_mul]
  simp

theorem subgroupRestrictionH2_classOf_eq_zero {Γe Γ0 : Subgroup RationalGL3} (hle : Γe ≤ Γ0)
    (ρ : Representation ℂ RationalGL3 V) (original : cocycles Γ0 ρ) (q : Γe → V)
    (hq : ∀ a b : Γe, ρ a.val (q b) - q (a * b) + q a =
      original.val.val ![1, a.val, a.val * b.val]) :
    subgroupRestrictionH2 hle ρ (classOf Γ0 ρ original) = 0 := by
  apply (ambientResolutionH2Equiv Γe ρ).injective
  rw [map_zero]
  change classOf (⊤ : Subgroup Γe) (ρ.comp Γe.subtype)
    (ambientRestrictionCycles Γe ρ (subgroupRestrictionCycle hle ρ original)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let P : cochains (⊤ : Subgroup Γe) (ρ.comp Γe.subtype) 1 :=
    ⟨fun x => ρ (x 0).val (q ((x 0)⁻¹ * x 1)), by
      intro γ x
      change ρ (γ.val * x 0).val (q ((γ.val * x 0)⁻¹ * (γ.val * x 1))) =
        ρ γ.val.val (ρ (x 0).val (q ((x 0)⁻¹ * x 1)))
      have e : (γ.val * x 0)⁻¹ * (γ.val * x 1) = (x 0)⁻¹ * x 1 := by group
      rw [e, ← Module.End.mul_apply, ← map_mul]
      rfl⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := hq ((x 0)⁻¹ * x 1) ((x 1)⁻¹ * x 2)
  have e1 : (x 0)⁻¹ * x 1 * ((x 1)⁻¹ * x 2) = (x 0)⁻¹ * x 2 := by group
  have e2 : ((x 0)⁻¹ * x 1).val * ((x 1)⁻¹ * x 2).val = ((x 0)⁻¹ * x 2).val := by
    rw [← Subgroup.coe_mul, e1]
  have orig := cocycle_apply_of_mem original.val (x 0).val (x 1).val (x 2).val (hle (x 0).property)
  have hvec : (fun i => ((x i : Γe) : RationalGL3)) = ![(x 0).val, (x 1).val, (x 2).val] := by
    funext i
    fin_cases i <;> rfl
  have h3 : original.val.val
      ![1, (x 0).val⁻¹ * (x 1).val, (x 0).val⁻¹ * (x 2).val] =
      ρ ((x 0)⁻¹ * x 1).val (q ((x 1)⁻¹ * x 2)) - q ((x 0)⁻¹ * x 2) + q ((x 0)⁻¹ * x 1) := by
    have h := hx
    rw [e1, e2] at h
    exact h.symm
  have hρ : ρ (x 0).val (ρ ((x 0)⁻¹ * x 1).val (q ((x 1)⁻¹ * x 2))) =
      ρ (x 1).val (q ((x 1)⁻¹ * x 2)) := by
    rw [← Module.End.mul_apply, ← map_mul]
    have : (x 0).val * ((x 0)⁻¹ * x 1).val = (x 1).val := by
      show (x 0).val * ((x 0).val⁻¹ * (x 1).val) = (x 1).val
      group
    rw [this]
  change ρ (x 1).val (q ((x 1)⁻¹ * x 2)) - ρ (x 0).val (q ((x 0)⁻¹ * x 2)) +
    ρ (x 0).val (q ((x 0)⁻¹ * x 1)) = original.val.val (fun i => ((x i : Γe) : RationalGL3))
  rw [hvec, orig, h3, map_add, map_sub, hρ]

end TernaryPeriodPolynomials.Argument.FacePairingFull
