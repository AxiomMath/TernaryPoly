module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Reversal

@[expose] public section


/-!
# Vertex reversal is `-1` on `H²`

For a homogeneous two-cocycle `z` the one-cochain `u(a, b) = z(a, b, a) + z(b, b, b)` satisfies
`du = rev z + z` (`differentialOne_antiHomotopy`), by the cocycle identities at
`(x₀, x₁, x₂, x₀)`, `(x₁, x₂, x₁, x₀)` and `(x₁, x₁, x₁, x₀)`. Hence the involution `revH2` of `H²` is
`-1` (`revH2_eq_neg`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (Γ : Subgroup G)
  (ρ : Representation ℂ G V)

/-- The one-cochain `u(a, b) = z(a, b, a) + z(b, b, b)`. -/
def antiHomotopy : cochains Γ ρ 2 →ₗ[ℂ] cochains Γ ρ 1 where
  toFun z := ⟨fun x => z.val ![x 0, x 1, x 0] + z.val ![x 1, x 1, x 1], by
    intro γ x
    have h1 := z.property γ ![x 0, x 1, x 0]
    have h2 := z.property γ ![x 1, x 1, x 1]
    have t1 : (fun i => γ.val * ![x 0, x 1, x 0] i) =
        ![γ.val * x 0, γ.val * x 1, γ.val * x 0] := by
      funext i
      fin_cases i <;> rfl
    have t2 : (fun i => γ.val * ![x 1, x 1, x 1] i) =
        ![γ.val * x 1, γ.val * x 1, γ.val * x 1] := by
      funext i
      fin_cases i <;> rfl
    rw [t1] at h1
    rw [t2] at h2
    change z.val ![γ.val * x 0, γ.val * x 1, γ.val * x 0] +
      z.val ![γ.val * x 1, γ.val * x 1, γ.val * x 1] = _
    rw [h1, h2, map_add]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (f.val _ + g.val _) + (f.val _ + g.val _) = (f.val _ + f.val _) + (g.val _ + g.val _)
    abel
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change a • f.val _ + a • f.val _ = a • (f.val _ + f.val _)
    rw [smul_add]

theorem differentialOne_antiHomotopy (c : cocycles Γ ρ) :
    differentialOne Γ ρ (antiHomotopy Γ ρ c.val) = rev2 Γ ρ c.val + c.val := by
  apply Subtype.ext
  funext x
  have cyc : ∀ a b d e : G, c.val.val ![b, d, e] - c.val.val ![a, d, e] + c.val.val ![a, b, e] -
      c.val.val ![a, b, d] = 0 := fun a b d e => congrFun c.property ![a, b, d, e]
  have i1 := cyc (x 0) (x 1) (x 2) (x 0)
  have i2 := cyc (x 1) (x 2) (x 1) (x 0)
  have i3 := cyc (x 1) (x 1) (x 1) (x 0)
  simp only [differentialOne, antiHomotopy, rev2_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_add, Pi.add_apply]
  simp at i1 i2 i3 ⊢
  have hx : (![x 0, x 1, x 2] : Fin 3 → G) = x := by
    funext i
    fin_cases i <;> rfl
  rw [← hx]
  simp
  generalize c.val.val ![x 1, x 2, x 1] = A at *
  generalize c.val.val ![x 0, x 2, x 0] = B at *
  generalize c.val.val ![x 0, x 1, x 0] = C at *
  generalize c.val.val ![x 1, x 1, x 1] = D at *
  generalize c.val.val ![x 2, x 1, x 0] = E at *
  generalize c.val.val ![x 0, x 1, x 2] = F at *
  generalize c.val.val ![x 1, x 2, x 0] = P at *
  generalize c.val.val ![x 1, x 1, x 0] = Q at *
  rw [← sub_eq_zero]
  have e : A - B + (C + D) - (E + F) = (P - B + C - F) - (E - Q + P - A) - (Q - D) := by abel
  rw [e, i1, i2, i3]
  simp

/-- Reversal of a two-cocycle plus the cocycle is a coboundary. -/
theorem revCocycle_add_mem_range (c : cocycles Γ ρ) :
    revCocycle Γ ρ c + c ∈ LinearMap.range (boundaryMap Γ ρ) :=
  ⟨antiHomotopy Γ ρ c.val, Subtype.ext (differentialOne_antiHomotopy Γ ρ c)⟩

/-- **Vertex reversal is `-1` on `H²`.** -/
theorem revH2_eq_neg (a : H2 Γ ρ) : revH2 Γ ρ a = -a := by
  induction a using Submodule.Quotient.induction_on with
  | H c =>
    change revH2 Γ ρ (classOf Γ ρ c) = -classOf Γ ρ c
    rw [revH2_classOf, eq_neg_iff_add_eq_zero, ← map_add]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (revCocycle_add_mem_range Γ ρ c)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
