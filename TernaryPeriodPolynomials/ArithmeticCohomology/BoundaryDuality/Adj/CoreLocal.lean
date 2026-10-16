module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EpsilonSplit

@[expose] public section


/-!
# Primitives of scalar cup products and the local terms of a cup pairing

Let `ρ`, `ρ'` be representations of a group `G` on `V`, `W` with an invariant pairing `B`, and
let `X`, `Y` be crossed homomorphisms.  A function `θ : G → ℂ` is a *cup primitive* of `(X, Y)` if

  `θ g + θ h - θ (g h) = B (X g) (g • Y h)`,

that is, if `θ` is a primitive of the scalar two-cocycle `X ∪ Y` (for the trivial action on `ℂ`).
For an element `h` at which `X h = (h - 1) v` the *local term* is `θ h - B v (Y h)`.

* On the subgroup of elements at which `v` is a primitive of `X`, the local term is a
  homomorphism to `ℂ` (`localTerm_mul`); in particular it vanishes at elements of finite order
  (`localTerm_eq_zero_of_pow_eq_one`) and changes sign under inversion (`localTerm_inv`).
* It does not depend on the primitive `v` when `Y h` is a coboundary at `h`
  (`localTerm_eq_of_primitive`).
* The cup formula of the triple model (the cup product on the fundamental two-chain
  `[a | g₂] + [a g₂ | g₃]` corrected by the primitives) is the sum of the three local terms at
  `a`, `g₂`, `g₃ = (a g₂)⁻¹` for every cup primitive (`cupFormula_eq_localTerm`).
* Changing `X` or `Y` by a coboundary changes a cup primitive by an explicit function and leaves
  the local terms unchanged (`isCupPrimitive_add_boundary_left`, `localTerm_add_boundary_left`,
  `isCupPrimitive_add_boundary_right`, `localTerm_add_boundary_right`).
* A cup primitive pulls back along a group homomorphism together with linear maps of the
  coefficients which scale the pairing (`isCupPrimitive_pullback`, `localTerm_pullback`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TripleModel LinearDuality CocycleBridge EpsilonSplit

section Local

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {X : G → V} {Y : G → W} {θ : G → ℂ}

/-- `θ` is a primitive of the scalar cup product of `X` and `Y`:
`θ g + θ h - θ (g h) = B (X g) (g • Y h)`. -/
def IsCupPrimitive (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W) (X : G → V) (Y : G → W)
    (θ : G → ℂ) : Prop :=
  ∀ g h, θ g + θ h - θ (g * h) = B (X g) (ρ' g (Y h))

/-- The local term `θ h - B v (Y h)` of a cup primitive at `h`, for a primitive `v` of the first
cocycle at `h`. -/
def localTerm (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G → ℂ) (Y : G → W) (h : G) (v : V) : ℂ :=
  θ h - B v (Y h)

omit [Group G] in
theorem localTerm_def (h : G) (v : V) : localTerm B θ Y h v = θ h - B v (Y h) := rfl

/-- A cup primitive of a crossed homomorphism vanishes at the identity. -/
theorem IsCupPrimitive.map_one (hX : IsCocycle ρ X) (hθ : IsCupPrimitive B ρ' X Y θ) : θ 1 = 0 := by
  have e := hθ 1 1
  rw [mul_one, hX.map_one, map_zero, LinearMap.zero_apply] at e
  linear_combination e

/-- The local term at the identity vanishes. -/
theorem localTerm_one (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ)
    (v : V) : localTerm B θ Y 1 v = 0 := by
  rw [localTerm_def, hθ.map_one hX, hY.map_one, map_zero, sub_zero]

/-- **The local term is additive** along the elements at which `v` is a primitive: if
`X g = (g - 1) v` then `L (g h) = L g + L h`. -/
theorem localTerm_mul (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hY : IsCocycle ρ' Y)
    (hθ : IsCupPrimitive B ρ' X Y θ) {g h : G} {v : V} (hg : X g = (ρ g - 1) v) :
    localTerm B θ Y (g * h) v = localTerm B θ Y g v + localTerm B θ Y h v := by
  have e := hθ g h
  rw [hg, LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply, hinv] at e
  simp only [localTerm_def, hY g h, map_add]
  linear_combination -e

/-- The local term at a power: `L (h ^ n) = n L h`. -/
theorem localTerm_pow (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X)
    (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ) {h : G} {v : V}
    (hh : X h = (ρ h - 1) v) (n : ℕ) :
    localTerm B θ Y (h ^ n) v = (n : ℂ) * localTerm B θ Y h v := by
  induction n with
  | zero => rw [pow_zero, localTerm_one hX hY hθ, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ', localTerm_mul hinv hY hθ hh, ih, Nat.cast_succ]
    ring

/-- **The local term vanishes at an element of finite order.** -/
theorem localTerm_eq_zero_of_pow_eq_one (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ) {h : G} {v : V}
    (hh : X h = (ρ h - 1) v) {n : ℕ} (hn : 0 < n) (hpow : h ^ n = 1) :
    localTerm B θ Y h v = 0 := by
  have e := localTerm_pow hinv hX hY hθ hh n
  rw [hpow, localTerm_one hX hY hθ] at e
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  exact (mul_eq_zero.mp e.symm).resolve_left hn'

/-- The local term changes sign under inversion. -/
theorem localTerm_inv (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hX : IsCocycle ρ X)
    (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ) {h : G} {v : V}
    (hh : X h = (ρ h - 1) v) : localTerm B θ Y h⁻¹ v = -localTerm B θ Y h v := by
  have e := localTerm_mul hinv hY hθ (h := h⁻¹) hh
  rw [mul_inv_cancel, localTerm_one hX hY hθ] at e
  linear_combination -e

/-- A primitive of `X` at `h` is also a primitive at `h⁻¹`. -/
theorem primitive_inv (hX : IsCocycle ρ X) {h : G} {v : V} (hh : X h = (ρ h - 1) v) :
    X h⁻¹ = (ρ h⁻¹ - 1) v := by
  rw [isCocycle_map_inv hX h, hh]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, rep_inv_apply ρ]
  abel

/-- A primitive of `X` at `h⁻¹` is also a primitive at `h`. -/
theorem primitive_of_inv (hX : IsCocycle ρ X) {h : G} {v : V} (hh : X h⁻¹ = (ρ h⁻¹ - 1) v) :
    X h = (ρ h - 1) v := by
  have := primitive_inv hX hh
  rwa [inv_inv] at this

/-- **The local term does not depend on the primitive** when the second cocycle is a coboundary
at `h`. -/
theorem localTerm_eq_of_primitive (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) {h : G} {v v' : V}
    (hv : X h = (ρ h - 1) v) (hv' : X h = (ρ h - 1) v') {u : W} (hu : Y h = (ρ' h - 1) u) :
    localTerm B θ Y h v = localTerm B θ Y h v' := by
  have hfix : ρ h (v - v') = v - v' := by
    have e := hv.symm.trans hv'
    simp only [LinearMap.sub_apply, Module.End.one_apply] at e
    rw [map_sub]
    linear_combination (norm := module) e
  have key : B (v - v') (Y h) = 0 := by
    have e := hinv h (v - v') u
    rw [hfix] at e
    rw [hu, LinearMap.sub_apply, Module.End.one_apply, (B (v - v')).map_sub (ρ' h u) u, e,
      sub_self]
  rw [map_sub, LinearMap.sub_apply] at key
  simp only [localTerm_def]
  linear_combination -key

/-- **The cup formula is the sum of the three local terms**, for every cup primitive. -/
theorem cupFormula_eq_localTerm (hX : IsCocycle ρ X) (hθ : IsCupPrimitive B ρ' X Y θ) (a g₂ : G)
    (v : V × V × V) :
    cupFormula B ρ' a g₂ X Y v =
      localTerm B θ Y a v.1 + localTerm B θ Y g₂ v.2.1 + localTerm B θ Y (a * g₂)⁻¹ v.2.2 := by
  have h1 := hθ a g₂
  have h2 := hθ (a * g₂) (a * g₂)⁻¹
  rw [mul_inv_cancel, hθ.map_one hX] at h2
  simp only [cupFormula, localTerm_def]
  linear_combination -h1 - h2

/-- **Changing the first cocycle by a coboundary**: `θ + B u (Y ·)` is a cup primitive of
`(X + d u, Y)`. -/
theorem isCupPrimitive_add_boundary_left (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ) (u : V) :
    IsCupPrimitive B ρ' (fun g => X g + (ρ g u - u)) Y (fun g => θ g + B u (Y g)) := by
  intro g h
  have e := hθ g h
  simp only [hY g h, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hinv]
  linear_combination e

omit [Group G] in
/-- The local term is unchanged by a coboundary change of the first cocycle. -/
theorem localTerm_add_boundary_left (u : V) (h : G) (v : V) :
    localTerm B (fun g => θ g + B u (Y g)) Y h (v + u) = localTerm B θ Y h v := by
  simp only [localTerm_def, map_add, LinearMap.add_apply]
  ring

/-- **Changing the second cocycle by a coboundary**: `θ - B (X ·) (· • u)` is a cup primitive of
`(X, Y + d u)`. -/
theorem isCupPrimitive_add_boundary_right (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX : IsCocycle ρ X) (hθ : IsCupPrimitive B ρ' X Y θ) (u : W) :
    IsCupPrimitive B ρ' X (fun g => Y g + (ρ' g u - u)) (fun g => θ g - B (X g) (ρ' g u)) := by
  intro g h
  have e := hθ g h
  simp only [hX g h, map_add, map_sub, LinearMap.add_apply, rep_mul_apply ρ',
    hinv]
  linear_combination e

/-- The local term is unchanged by a coboundary change of the second cocycle. -/
theorem localTerm_add_boundary_right (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (u : W)
    {h : G} {v : V} (hh : X h = (ρ h - 1) v) :
    localTerm B (fun g => θ g - B (X g) (ρ' g u)) (fun g => Y g + (ρ' g u - u)) h v =
      localTerm B θ Y h v := by
  simp only [localTerm_def, hh, LinearMap.sub_apply, Module.End.one_apply, map_sub, map_add,
    hinv]
  ring

end Local

section Pullback

variable {G₁ G V W V₁ W₁ : Type} [Group G₁] [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup W₁] [Module ℂ W₁]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {ρ₁ : Representation ℂ G₁ V₁} {ρ₁' : Representation ℂ G₁ W₁} {B₁ : V₁ →ₗ[ℂ] W₁ →ₗ[ℂ] ℂ}
  {X : G → V} {Y : G → W} {θ : G → ℂ}

/-- The pullback of a crossed homomorphism along a homomorphism and an intertwining linear map. -/
theorem isCocycle_pullback (φ : G₁ →* G) (f : V →ₗ[ℂ] V₁)
    (hf : ∀ a v, f (ρ (φ a) v) = ρ₁ a (f v)) (hX : IsCocycle ρ X) :
    IsCocycle ρ₁ (fun a => f (X (φ a))) := by
  intro a b
  simp only [map_mul, hX (φ a) (φ b), map_add, hf]

/-- **Pullback of a cup primitive.**  If `B₁ (f v) (a • f' w) = κ B v (φ a • w)` then `κ θ ∘ φ` is a
cup primitive of the pulled back cocycles. -/
theorem isCupPrimitive_pullback (φ : G₁ →* G) (f : V →ₗ[ℂ] V₁) (f' : W →ₗ[ℂ] W₁) (κ : ℂ)
    (hcomp : ∀ a v w, B₁ (f v) (ρ₁' a (f' w)) = κ * B v (ρ' (φ a) w))
    (hθ : IsCupPrimitive B ρ' X Y θ) :
    IsCupPrimitive B₁ ρ₁' (fun a => f (X (φ a))) (fun a => f' (Y (φ a)))
      (fun a => κ * θ (φ a)) := by
  intro a b
  have e := hθ (φ a) (φ b)
  show κ * θ (φ a) + κ * θ (φ b) - κ * θ (φ (a * b)) = B₁ (f (X (φ a))) (ρ₁' a (f' (Y (φ b))))
  rw [hcomp, map_mul, ← e]
  ring

/-- The local term of a pulled back cup primitive. -/
theorem localTerm_pullback (φ : G₁ →* G) (f : V →ₗ[ℂ] V₁) (f' : W →ₗ[ℂ] W₁) (κ : ℂ)
    (hcomp : ∀ a v w, B₁ (f v) (ρ₁' a (f' w)) = κ * B v (ρ' (φ a) w)) (a : G₁) (v : V) :
    localTerm B₁ (fun a => κ * θ (φ a)) (fun a => f' (Y (φ a))) a (f v) =
      κ * localTerm B θ Y (φ a) v := by
  have h1 := hcomp 1 v (Y (φ a))
  simp only [map_one, Module.End.one_apply] at h1
  simp only [localTerm_def]
  rw [h1]
  ring

end Pullback

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
