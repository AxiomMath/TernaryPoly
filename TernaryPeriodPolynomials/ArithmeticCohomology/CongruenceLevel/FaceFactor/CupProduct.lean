module

public import Mathlib

@[expose] public section


/-!
# The cup product `H¹ × H² → H³` on inhomogeneous cochains

Formalized by Claude Sonnet 5.5.  Generic infrastructure (Mathlib has no cup products) for the evaluation of the face pairing on the
flag groups; coefficient modules `V`, `W` of a group `G` with an invariant pairing `e : V × W → T` into a trivial module `T`.

Cochains are the explicit functions `G → V` (degree one), `G → G → V` (degree two), `G → G → G → T` (degree three), with the inhomogeneous differentials
`dd1 ρ u (g,h) = ρ g (u h) - u (g h) + u g`, `dd2 ρ β (g,h,k) = ρ g (β h k) - β (g h) k + β g (h k) - β g h` and, for trivial coefficients, `dd2T`, `dd3T`.
The products are `(u ∪ β)(g₁,g₂,g₃) = e (u g₁) (g₁ β(g₂,g₃))` and the auxiliary ones needed for the Leibniz rule and the descent to cohomology
(`cup12_cocycle`, `cup12_coboundary_left`, `cup12_coboundary_right`).  Naturality under restriction along a homomorphism is definitional (`cup12_comp`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Cup

variable {k : Type} [CommRing k] {G : Type} [Group G] {V W T : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup T] [Module k T] (ρ : Representation k G V) (ρ' : Representation k G W) (e : V →ₗ[k] W →ₗ[k] T)

/-- The differential of a degree-one cochain. -/
def dd1 {M : Type} [AddCommGroup M] [Module k M] (σ : Representation k G M) (u : G → M) : G → G → M :=
  fun g h => σ g (u h) - u (g * h) + u g

/-- The differential of a degree-two cochain. -/
def dd2 {M : Type} [AddCommGroup M] [Module k M] (σ : Representation k G M) (β : G → G → M) : G → G → G → M :=
  fun g h l => σ g (β h l) - β (g * h) l + β g (h * l) - β g h

/-- The differential of a degree-two cochain with trivial coefficients. -/
def dd2T (c : G → G → T) : G → G → G → T := fun g h l => c h l - c (g * h) l + c g (h * l) - c g h

/-- The differential of a degree-three cochain with trivial coefficients. -/
def dd3T (c : G → G → G → T) : G → G → G → G → T :=
  fun g1 g2 g3 g4 => c g2 g3 g4 - c (g1 * g2) g3 g4 + c g1 (g2 * g3) g4 - c g1 g2 (g3 * g4) + c g1 g2 g3

/-- The coboundary of a vector. -/
def dd0 (v : V) : G → V := fun g => ρ g v - v

/-- `(u ∪ w)(g₁, g₂) = e (u g₁) (g₁ w(g₂))`. -/
def cup11 (u : G → V) (w : G → W) : G → G → T := fun g1 g2 => e (u g1) (ρ' g1 (w g2))

/-- `(v ∪ β)(g₁, g₂) = e v (β(g₁, g₂))`. -/
def cup02 (v : V) (β : G → G → W) : G → G → T := fun g1 g2 => e v (β g1 g2)

/-- `(u ∪ β)(g₁, g₂, g₃) = e (u g₁) (g₁ β(g₂, g₃))`. -/
def cup12 (u : G → V) (β : G → G → W) : G → G → G → T := fun g1 g2 g3 => e (u g1) (ρ' g1 (β g2 g3))

/-- `(α ∪ w)(g₁, g₂, g₃) = e (α(g₁, g₂)) (g₁ g₂ w(g₃))`. -/
def cup21 (α : G → G → V) (w : G → W) : G → G → G → T := fun g1 g2 g3 => e (α g1 g2) (ρ' (g1 * g2) (w g3))

/-- `(α ∪ β)(g₁, …, g₄) = e (α(g₁, g₂)) (g₁ g₂ β(g₃, g₄))`. -/
def cup22 (α : G → G → V) (β : G → G → W) : G → G → G → G → T :=
  fun g1 g2 g3 g4 => e (α g1 g2) (ρ' (g1 * g2) (β g3 g4))

/-- `(u ∪ γ)(g₁, …, g₄) = e (u g₁) (g₁ γ(g₂, g₃, g₄))` for a degree-three cochain `γ` with values in `W`. -/
def cup13 (u : G → V) (γ : G → G → G → W) : G → G → G → G → T :=
  fun g1 g2 g3 g4 => e (u g1) (ρ' g1 (γ g2 g3 g4))

/-- `(v ∪ γ)(g₁, g₂, g₃) = e v (γ(g₁, g₂, g₃))` for a degree-three cochain `γ` with values in `W`. -/
def cup03 (v : V) (γ : G → G → G → W) : G → G → G → T := fun g1 g2 g3 => e v (γ g1 g2 g3)

variable {ρ ρ' e}

section Leibniz

variable (he : ∀ (g : G) (v : V) (w : W), e (ρ g v) (ρ' g w) = e v w)
include he

/-- **Leibniz rule for `H¹ × H² → H³`**: `d(u ∪ β) = du ∪ β - u ∪ dβ`. -/
theorem leibniz12 (u : G → V) (β : G → G → W) :
    dd3T (cup12 ρ' e u β) = fun g1 g2 g3 g4 => cup22 ρ' e (dd1 ρ u) β g1 g2 g3 g4 - cup13 ρ' e u (dd2 ρ' β) g1 g2 g3 g4 := by
  funext g1 g2 g3 g4
  have h1 := he g1 (u g2) (ρ' g2 (β g3 g4))
  simp only [dd3T, cup12, cup22, cup13, dd1, dd2, map_mul, Module.End.mul_apply, map_sub, map_add, LinearMap.sub_apply,
    LinearMap.add_apply] at h1 ⊢
  rw [h1]
  abel

/-- **Leibniz rule for the product of two one-cochains**: `d(u ∪ w) = du ∪ w - u ∪ dw`. -/
theorem leibniz11 (u : G → V) (w : G → W) :
    dd2T (cup11 ρ' e u w) = fun g1 g2 g3 => cup21 ρ' e (dd1 ρ u) w g1 g2 g3 - cup12 ρ' e u (dd1 ρ' w) g1 g2 g3 := by
  funext g1 g2 g3
  have h1 := he g1 (u g2) (ρ' g2 (w g3))
  simp only [dd2T, cup11, cup21, cup12, dd1, map_mul, Module.End.mul_apply, map_sub, map_add, LinearMap.sub_apply,
    LinearMap.add_apply] at h1 ⊢
  rw [h1]
  abel

/-- **Leibniz rule for a vector and a two-cochain**: `d(v ∪ β) = dv ∪ β + v ∪ dβ`. -/
theorem leibniz02 (v : V) (β : G → G → W) :
    dd2T (cup02 e v β) = fun g1 g2 g3 => cup12 ρ' e (dd0 ρ v) β g1 g2 g3 + cup03 e v (dd2 ρ' β) g1 g2 g3 := by
  funext g1 g2 g3
  have h1 := he g1 v (β g2 g3)
  simp only [dd2T, cup02, cup12, cup03, dd0, dd2, map_sub, map_add, LinearMap.sub_apply] at h1 ⊢
  rw [h1]
  abel

/-- **The cup product of a one-cocycle and a two-cocycle is a three-cocycle.** -/
theorem cup12_cocycle (u : G → V) (β : G → G → W) (hu : dd1 ρ u = 0) (hβ : dd2 ρ' β = 0) :
    dd3T (cup12 ρ' e u β) = 0 := by
  rw [leibniz12 he, hu, hβ]
  funext g1 g2 g3 g4
  simp [cup22, cup13]

/-- **Independence of the representative (left)**: `(dv) ∪ β = d(v ∪ β)` for a two-cocycle `β`. -/
theorem cup12_coboundary_left (v : V) (β : G → G → W) (hβ : dd2 ρ' β = 0) :
    cup12 ρ' e (dd0 ρ v) β = dd2T (cup02 e v β) := by
  rw [leibniz02 he]
  funext g1 g2 g3
  simp [hβ, cup03]

/-- **Independence of the representative (right)**: `u ∪ dw = -d(u ∪ w)` for a one-cocycle `u`. -/
theorem cup12_coboundary_right (u : G → V) (w : G → W) (hu : dd1 ρ u = 0) :
    cup12 ρ' e u (dd1 ρ' w) = - dd2T (cup11 ρ' e u w) := by
  rw [leibniz11 he, hu]
  funext g1 g2 g3
  simp [cup21]

end Leibniz

section Natural

variable {H : Type} [Group H] (f : H →* G)

/-- **Naturality under restriction** along a homomorphism `f : H →* G` (definitional). -/
theorem cup12_comp (u : G → V) (β : G → G → W) :
    cup12 (ρ'.comp f) e (u ∘ f) (fun a b => β (f a) (f b)) = fun a b c => cup12 ρ' e u β (f a) (f b) (f c) := by
  funext a b c
  simp [cup12]

end Natural

end Cup

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
