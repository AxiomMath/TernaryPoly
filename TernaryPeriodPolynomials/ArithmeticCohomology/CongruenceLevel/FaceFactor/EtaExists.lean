module

public import Mathlib

@[expose] public section


/-!
# The cup cocycle of two crossed homomorphisms has a primitive when `H²` vanishes

Formalized by Claude Sonnet 5.5.

`koszul_cocycle`: for crossed homomorphisms `a : Γ → U`, `a' : Γ → U'` and an invariant bilinear pairing `β`, the function `ζ(x, y) = β(a x, x · a' y)` is a `2`-cocycle with trivial complex coefficients;
`exists_eta`: if `H²(Γ, ℂ) = 0` there is `η : Γ → ℂ` with `η(xy) = η x + η y - ζ(x, y)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

/-- **A primitive of a `2`-cocycle with trivial coefficients when `H²(Γ, ℂ) = 0`**. -/
theorem exists_primitive_of_vanishing {Γ : Type} [Group Γ] (hH2 : ∀ x : groupCohomology.H2 (Rep.trivial ℂ Γ ℂ), x = 0)
    (ζ : Γ → Γ → ℂ) (hζ : ∀ x y z, ζ (x * y) z + ζ x y = ζ y z + ζ x (y * z)) :
    ∃ η : Γ → ℂ, ∀ x y, η (x * y) = η x + η y - ζ x y := by
  have hmem : (fun p : Γ × Γ => ζ p.1 p.2) ∈ groupCohomology.cocycles₂ (Rep.trivial ℂ Γ ℂ) := by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    exact hζ g h j
  have h0 := hH2 (groupCohomology.H2π (Rep.trivial ℂ Γ ℂ) ⟨_, hmem⟩)
  rw [groupCohomology.H2π_eq_zero_iff] at h0
  obtain ⟨f, hf⟩ := h0
  refine ⟨f, fun x y => ?_⟩
  have := congrFun hf (x, y)
  simp only [groupCohomology.d₁₂_hom_apply] at this
  change f y - f (x * y) + f x = ζ x y at this
  linear_combination -this

variable {Γ : Type} [Group Γ] {U U' : Rep ℂ Γ}

/-- **The cup cocycle of two crossed homomorphisms**: `ζ(x, y) = β(a x, x · a' y)`. -/
theorem koszul_cocycle (β : U →ₗ[ℂ] U' →ₗ[ℂ] ℂ) (hβ : ∀ g u u', β (U.ρ g u) (U'.ρ g u') = β u u')
    (a : Γ → U) (ha : ∀ x y, a (x * y) = U.ρ x (a y) + a x)
    (a' : Γ → U') (ha' : ∀ x y, a' (x * y) = U'.ρ x (a' y) + a' x) (x y z : Γ) :
    β (a (x * y)) (U'.ρ (x * y) (a' z)) + β (a x) (U'.ρ x (a' y)) =
      β (a y) (U'.ρ y (a' z)) + β (a x) (U'.ρ x (a' (y * z))) := by
  have e1 : β (a (x * y)) (U'.ρ (x * y) (a' z)) = β (a y) (U'.ρ y (a' z)) + β (a x) (U'.ρ (x * y) (a' z)) := by
    rw [ha, map_add, LinearMap.add_apply, ← hβ x (a y) (U'.ρ y (a' z))]
    congr 2
    rw [map_mul]; rfl
  have e2 : β (a x) (U'.ρ x (a' (y * z))) = β (a x) (U'.ρ (x * y) (a' z)) + β (a x) (U'.ρ x (a' y)) := by
    rw [ha', map_add, map_add, map_mul]
    rfl
  rw [e1, e2]
  ring

/-- **A primitive `η` of `ζ(x, y) = β(a x, x · a' y)`** exists when `H²(Γ, ℂ) = 0`. -/
theorem exists_eta (hH2 : ∀ x : groupCohomology.H2 (Rep.trivial ℂ Γ ℂ), x = 0)
    (β : U →ₗ[ℂ] U' →ₗ[ℂ] ℂ) (hβ : ∀ g u u', β (U.ρ g u) (U'.ρ g u') = β u u')
    (a : Γ → U) (ha : ∀ x y, a (x * y) = U.ρ x (a y) + a x)
    (a' : Γ → U') (ha' : ∀ x y, a' (x * y) = U'.ρ x (a' y) + a' x) :
    ∃ η : Γ → ℂ, ∀ x y, η (x * y) = η x + η y - β (a x) (U'.ρ x (a' y)) :=
  exists_primitive_of_vanishing hH2 _ (koszul_cocycle β hβ a ha a' ha')

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
