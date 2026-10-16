module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChiHom

@[expose] public section


/-!
# Cochain algebra for the fiber integration at a cusp

Homogeneous cochains with vertices in a group `G` take values in representations `V`, `W` of
`G` paired by a bilinear form `B`. This file collects the identities between the following
operations on them:
* the cup products `f ⌣ g` of one- and two-cochains (`cup11`, `cup12`, `cup22`) and their
  Leibniz rules;
* the pullback `h ⋆ f = ρ(h)⁻¹ f(h ·)` of a one-cochain along left translation (`pull1`) and its
  scalar version `h^* f = f(h ·)` on two-cochains (`spull2`), with `d(h ⋆ f) = h ⋆ df`,
  `h^*(f ⌣ g) = (h ⋆ f) ⌣ (h ⋆ g)` for a pairing invariant under `h⁻¹`, and
  `k ⋆ (h ⋆ f) = (h k) ⋆ f`;
* the Levi cocycle `A(h) = h ⋆ ω − ω` of a one-cochain `ω` whose coboundary is equivariant: it
  is a one-cocycle, it is `U`-equivariant when `ω` is and `h` normalizes `U`, and it is a right
  crossed homomorphism, `A(h k) = A(k) + k ⋆ A(h)`;
* the left action `g · f = g⁻¹ ⋆ f` of `G` on one-cochains (`cochainRep`).

Pairings of scalar cochains with chains are linear in the cochain.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberCochains

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains

variable {G : Type}

section Basic

/-- A pair of vertices is the vector of its entries. -/
theorem vec2_eta (x : Fin 2 → G) : ![x 0, x 1] = x := by
  funext i
  fin_cases i <;> rfl

/-- A triple of vertices is the vector of its entries. -/
theorem vec3_eta (x : Fin 3 → G) : ![x 0, x 1, x 2] = x := by
  funext i
  fin_cases i <;> rfl

/-- The degree-one differential is additive. -/
theorem differentialOneRaw_sub {M : Type} [AddCommGroup M] (f g : (Fin 2 → G) → M)
    (x : Fin 3 → G) :
    differentialOneRaw (f - g) x = differentialOneRaw f x - differentialOneRaw g x := by
  simp only [differentialOneRaw, Pi.sub_apply]
  abel

/-- The degree-two differential is additive. -/
theorem differentialTwoRaw_sub (f g : (Fin 3 → G) → ℂ) (x : Fin 4 → G) :
    differentialTwoRaw (f - g) x = differentialTwoRaw f x - differentialTwoRaw g x := by
  simp only [differentialTwoRaw, Pi.sub_apply]
  ring

/-- The degree-two differential of `-f - g`. -/
theorem differentialTwoRaw_neg_sub (f g : (Fin 3 → G) → ℂ) (x : Fin 4 → G) :
    differentialTwoRaw (-f - g) x = -differentialTwoRaw f x - differentialTwoRaw g x := by
  simp only [differentialTwoRaw, Pi.sub_apply, Pi.neg_apply]
  ring

/-- The degree-three differential is additive. -/
theorem differentialThreeRaw_sub' (f g : (Fin 4 → G) → ℂ) (x : Fin 5 → G) :
    differentialThreeRaw (f - g) x = differentialThreeRaw f x - differentialThreeRaw g x := by
  simp only [differentialThreeRaw, Pi.sub_apply]
  ring

end Basic

section Cup

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

/-- The cup product of two one-cochains: `(f ⌣ g)(x₀, x₁, x₂) = B(f(x₀, x₁), g(x₁, x₂))`. -/
def cup11 (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) (x : Fin 3 → G) : ℂ :=
  B (f ![x 0, x 1]) (g ![x 1, x 2])

/-- The cup product of a one-cochain and a two-cochain. -/
def cup12 (f : (Fin 2 → G) → V) (g : (Fin 3 → G) → W) (x : Fin 4 → G) : ℂ :=
  B (f ![x 0, x 1]) (g ![x 1, x 2, x 3])

/-- The cup product of two two-cochains. -/
def cup22 (f : (Fin 3 → G) → V) (g : (Fin 3 → G) → W) (x : Fin 5 → G) : ℂ :=
  B (f ![x 0, x 1, x 2]) (g ![x 2, x 3, x 4])

/-- **Leibniz rule** for the cup product of two one-cochains:
`d(f ⌣ g) = df ⌣ g − f ⌣ dg`. -/
theorem differentialTwoRaw_cup11 (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) (x : Fin 4 → G) :
    differentialTwoRaw (cup11 B f g) x =
      B (differentialOneRaw f ![x 0, x 1, x 2]) (g ![x 2, x 3]) -
        B (f ![x 0, x 1]) (differentialOneRaw g ![x 1, x 2, x 3]) := by
  change B (f ![x 1, x 2]) (g ![x 2, x 3]) - B (f ![x 0, x 2]) (g ![x 2, x 3]) +
      B (f ![x 0, x 1]) (g ![x 1, x 3]) - B (f ![x 0, x 1]) (g ![x 1, x 2]) =
    B (f ![x 1, x 2] - f ![x 0, x 2] + f ![x 0, x 1]) (g ![x 2, x 3]) -
      B (f ![x 0, x 1]) (g ![x 2, x 3] - g ![x 1, x 3] + g ![x 1, x 2])
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

/-- For a one-cocycle `f`, `d(f ⌣ g) = −(f ⌣ dg)`. -/
theorem differentialTwoRaw_cup11_of_cocycle {f : (Fin 2 → G) → V}
    (hf : ∀ x, differentialOneRaw f x = 0) (g : (Fin 2 → G) → W) (x : Fin 4 → G) :
    differentialTwoRaw (cup11 B f g) x = -cup12 B f (differentialOneRaw g) x := by
  show _ = -B (f ![x 0, x 1]) (differentialOneRaw g ![x 1, x 2, x 3])
  rw [differentialTwoRaw_cup11, hf, map_zero, LinearMap.zero_apply, zero_sub]

/-- The cup product of two one-cocycles is a two-cocycle. -/
theorem cup11_closed {f : (Fin 2 → G) → V} {g : (Fin 2 → G) → W}
    (hf : ∀ x, differentialOneRaw f x = 0) (hg : ∀ x, differentialOneRaw g x = 0)
    (x : Fin 4 → G) : differentialTwoRaw (cup11 B f g) x = 0 := by
  simp only [differentialTwoRaw_cup11, hf, hg, map_zero, LinearMap.zero_apply, sub_zero]

/-- **Leibniz rule** for the cup product of a one-cochain with a two-cocycle:
`d(f ⌣ g) = df ⌣ g`. -/
theorem differentialThreeRaw_cup12 (f : (Fin 2 → G) → V) {g : (Fin 3 → G) → W}
    (hg : IsCocycleTwo g) (x : Fin 5 → G) :
    differentialThreeRaw (cup12 B f g) x = cup22 B (differentialOneRaw f) g x := by
  have second : g ![x 2, x 3, x 4] - g ![x 1, x 3, x 4] + g ![x 1, x 2, x 4] -
      g ![x 1, x 2, x 3] = 0 := hg ![x 1, x 2, x 3, x 4]
  have second' : g ![x 1, x 2, x 3] = g ![x 2, x 3, x 4] - g ![x 1, x 3, x 4] +
      g ![x 1, x 2, x 4] := by
    rw [← sub_eq_zero, ← neg_eq_zero, ← second]; abel
  change B (f ![x 1, x 2]) (g ![x 2, x 3, x 4]) - B (f ![x 0, x 2]) (g ![x 2, x 3, x 4]) +
      B (f ![x 0, x 1]) (g ![x 1, x 3, x 4]) - B (f ![x 0, x 1]) (g ![x 1, x 2, x 4]) +
      B (f ![x 0, x 1]) (g ![x 1, x 2, x 3]) =
    B (f ![x 1, x 2] - f ![x 0, x 2] + f ![x 0, x 1]) (g ![x 2, x 3, x 4])
  rw [second', map_add, map_sub, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

theorem cup11_add_left (f f' : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B (f + f') g = cup11 B f g + cup11 B f' g := by
  funext x
  change B (f ![x 0, x 1] + f' ![x 0, x 1]) (g ![x 1, x 2]) =
    B (f ![x 0, x 1]) (g ![x 1, x 2]) + B (f' ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_add, LinearMap.add_apply]

theorem cup11_sub_left (f f' : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B (f - f') g = cup11 B f g - cup11 B f' g := by
  funext x
  change B (f ![x 0, x 1] - f' ![x 0, x 1]) (g ![x 1, x 2]) =
    B (f ![x 0, x 1]) (g ![x 1, x 2]) - B (f' ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_sub, LinearMap.sub_apply]

theorem cup11_neg_left (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B (-f) g = -cup11 B f g := by
  funext x
  change B (-f ![x 0, x 1]) (g ![x 1, x 2]) = -B (f ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_neg, LinearMap.neg_apply]

theorem cup11_add_right (f : (Fin 2 → G) → V) (g g' : (Fin 2 → G) → W) :
    cup11 B f (g + g') = cup11 B f g + cup11 B f g' := by
  funext x
  change B (f ![x 0, x 1]) (g ![x 1, x 2] + g' ![x 1, x 2]) =
    B (f ![x 0, x 1]) (g ![x 1, x 2]) + B (f ![x 0, x 1]) (g' ![x 1, x 2])
  rw [map_add]

theorem cup11_sub_right (f : (Fin 2 → G) → V) (g g' : (Fin 2 → G) → W) :
    cup11 B f (g - g') = cup11 B f g - cup11 B f g' := by
  funext x
  change B (f ![x 0, x 1]) (g ![x 1, x 2] - g' ![x 1, x 2]) =
    B (f ![x 0, x 1]) (g ![x 1, x 2]) - B (f ![x 0, x 1]) (g' ![x 1, x 2])
  rw [map_sub]

theorem cup11_neg_right (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B f (-g) = -cup11 B f g := by
  funext x
  change B (f ![x 0, x 1]) (-g ![x 1, x 2]) = -B (f ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_neg]

theorem cup11_smul_left (c : ℂ) (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B (c • f) g = c • cup11 B f g := by
  funext x
  change B (c • f ![x 0, x 1]) (g ![x 1, x 2]) = c * B (f ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem cup11_smul_right (c : ℂ) (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    cup11 B f (c • g) = c • cup11 B f g := by
  funext x
  change B (f ![x 0, x 1]) (c • g ![x 1, x 2]) = c * B (f ![x 0, x 1]) (g ![x 1, x 2])
  rw [map_smul, smul_eq_mul]

end Cup

section Pairing

/-- Pairing with a chain is additive in the cochain. -/
theorem pair_add {X : Type} (f g : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (f + g) c =
      Finsupp.linearCombination ℂ f c + Finsupp.linearCombination ℂ g c := by
  simp only [Finsupp.linearCombination_apply, Pi.add_apply, smul_add, Finsupp.sum_add]

/-- Pairing with a chain is additive in the cochain. -/
theorem pair_sub {X : Type} (f g : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (f - g) c =
      Finsupp.linearCombination ℂ f c - Finsupp.linearCombination ℂ g c := by
  simp only [Finsupp.linearCombination_apply, Pi.sub_apply, smul_sub, Finsupp.sum_sub]

/-- Pairing with a chain is additive in the cochain. -/
theorem pair_neg {X : Type} (f : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (-f) c = -Finsupp.linearCombination ℂ f c := by
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg]

/-- Pairing with a chain is homogeneous in the cochain. -/
theorem pair_smul {X : Type} (a : ℂ) (f : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (a • f) c = a * Finsupp.linearCombination ℂ f c := by
  simp only [Finsupp.linearCombination_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun x _ => by ring

/-- The zero cochain pairs to zero. -/
theorem pair_zero {X : Type} (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (0 : X → ℂ) c = 0 :=
  Finsupp.linearCombination_zero_apply ℂ c

end Pairing

section GroupVertices

variable [Group G]

/-- Translated vertices written as a vector. -/
theorem vec2_mul (h : G) (x : Fin 2 → G) : ![h * x 0, h * x 1] = fun i => h * x i := by
  funext i
  fin_cases i <;> rfl

/-- Translated vertices written as a vector. -/
theorem vec3_mul (h : G) (x : Fin 3 → G) : ![h * x 0, h * x 1, h * x 2] = fun i => h * x i := by
  funext i
  fin_cases i <;> rfl

/-- Translated vertices written as a vector. -/
theorem vec4_mul (h : G) (x : Fin 4 → G) :
    ![h * x 0, h * x 1, h * x 2, h * x 3] = fun i => h * x i := by
  funext i
  fin_cases i <;> rfl

/-- An invariant scalar two-cochain is invariant at displayed vertices. -/
theorem inv3_apply {H : Subgroup G} {f : (Fin 3 → G) → ℂ}
    (hf : ∀ (γ : H) x, f (fun i => γ.val * x i) = f x) {γ : G} (hγ : γ ∈ H) (a b c : G) :
    f ![γ * a, γ * b, γ * c] = f ![a, b, c] := by
  have e : (![γ * a, γ * b, γ * c] : Fin 3 → G) = fun i => γ * (![a, b, c] : Fin 3 → G) i := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact hf ⟨γ, hγ⟩ ![a, b, c]

end GroupVertices

section Representation

variable [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem rep_mul_apply' (g h : G) (v : V) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_inv_self (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← rep_mul_apply', inv_mul_cancel, map_one, Module.End.one_apply]

theorem rep_self_inv (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← rep_mul_apply', mul_inv_cancel, map_one, Module.End.one_apply]

end Representation

section Invariance

variable [Group G] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

/-- The cup product of equivariant one-cochains is invariant. -/
theorem cup11_invariant (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) {U : Subgroup G}
    (hB : ∀ g ∈ U, ∀ v w, B (ρ g v) (ρ' g w) = B v w) {f : (Fin 2 → G) → V}
    {g : (Fin 2 → G) → W} (hf : ∀ γ ∈ U, ∀ a b, f ![γ * a, γ * b] = ρ γ (f ![a, b]))
    (hg : ∀ γ ∈ U, ∀ a b, g ![γ * a, γ * b] = ρ' γ (g ![a, b])) :
    ∀ (γ : U) x, cup11 B f g (fun i => γ.val * x i) = cup11 B f g x := by
  intro γ x
  change B (f ![γ.val * x 0, γ.val * x 1]) (g ![γ.val * x 1, γ.val * x 2]) =
    B (f ![x 0, x 1]) (g ![x 1, x 2])
  rw [hf γ.val γ.property, hg γ.val γ.property, hB γ.val γ.property]

end Invariance

section Pullback

variable [Group G]

/-- The scalar pullback of a two-cochain along left translation by `h`. -/
def spull2 (h : G) (f : (Fin 3 → G) → ℂ) : (Fin 3 → G) → ℂ :=
  fun x => f ![h * x 0, h * x 1, h * x 2]

theorem spull2_sub (h : G) (f g : (Fin 3 → G) → ℂ) :
    spull2 h (f - g) = spull2 h f - spull2 h g := rfl

/-- `k^* (h^* f) = (h k)^* f`. -/
theorem spull2_mul (h k : G) (f : (Fin 3 → G) → ℂ) :
    spull2 k (spull2 h f) = spull2 (h * k) f := by
  funext x
  change f ![h * (k * x 0), h * (k * x 1), h * (k * x 2)] =
    f ![h * k * x 0, h * k * x 1, h * k * x 2]
  simp only [mul_assoc]

/-- The scalar pullback is precomposition with left translation. -/
theorem spull2_eq_fun (h : G) (f : (Fin 3 → G) → ℂ) :
    spull2 h f = fun x => f (fun i => h * x i) := by
  funext x
  exact congrArg f (vec3_mul h x)

/-- The differential commutes with the scalar pullback. -/
theorem differentialTwoRaw_spull2 (h : G) (f : (Fin 3 → G) → ℂ) (x : Fin 4 → G) :
    differentialTwoRaw (spull2 h f) x =
      differentialTwoRaw f ![h * x 0, h * x 1, h * x 2, h * x 3] := rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The pullback of a one-cochain along left translation by `h`:
`(h ⋆ f)(x₀, x₁) = ρ(h)⁻¹ f(h x₀, h x₁)`. -/
def pull1 (h : G) (f : (Fin 2 → G) → V) : (Fin 2 → G) → V :=
  fun x => ρ h⁻¹ (f ![h * x 0, h * x 1])

theorem pull1_add (h : G) (f g : (Fin 2 → G) → V) :
    pull1 ρ h (f + g) = pull1 ρ h f + pull1 ρ h g := by
  funext x
  exact map_add (ρ h⁻¹) _ _

theorem pull1_sub (h : G) (f g : (Fin 2 → G) → V) :
    pull1 ρ h (f - g) = pull1 ρ h f - pull1 ρ h g := by
  funext x
  exact map_sub (ρ h⁻¹) _ _

theorem pull1_neg (h : G) (f : (Fin 2 → G) → V) : pull1 ρ h (-f) = -pull1 ρ h f := by
  funext x
  exact map_neg (ρ h⁻¹) _

theorem pull1_smul (h : G) (c : ℂ) (f : (Fin 2 → G) → V) :
    pull1 ρ h (c • f) = c • pull1 ρ h f := by
  funext x
  exact map_smul (ρ h⁻¹) c _

/-- `k ⋆ (h ⋆ f) = (h k) ⋆ f`. -/
theorem pull1_mul (h k : G) (f : (Fin 2 → G) → V) :
    pull1 ρ k (pull1 ρ h f) = pull1 ρ (h * k) f := by
  funext x
  change ρ k⁻¹ (ρ h⁻¹ (f ![h * (k * x 0), h * (k * x 1)])) =
    ρ (h * k)⁻¹ (f ![h * k * x 0, h * k * x 1])
  rw [mul_inv_rev, map_mul, Module.End.mul_apply, mul_assoc, mul_assoc]

/-- `1 ⋆ f = f`. -/
theorem pull1_one (f : (Fin 2 → G) → V) : pull1 ρ 1 f = f := by
  funext x
  change ρ 1⁻¹ (f ![1 * x 0, 1 * x 1]) = f x
  rw [inv_one, map_one, Module.End.one_apply, one_mul, one_mul, vec2_eta]

/-- `h ⋆ (h⁻¹ ⋆ f) = f`. -/
theorem pull1_pull1_inv (h : G) (f : (Fin 2 → G) → V) : pull1 ρ h (pull1 ρ h⁻¹ f) = f := by
  rw [pull1_mul, inv_mul_cancel, pull1_one]

/-- `h ⋆ f = f` for an `h`-equivariant one-cochain. -/
theorem pull1_eq_self {h : G} {f : (Fin 2 → G) → V}
    (hf : ∀ a b, f ![h * a, h * b] = ρ h (f ![a, b])) : pull1 ρ h f = f := by
  funext x
  change ρ h⁻¹ (f ![h * x 0, h * x 1]) = f x
  rw [hf, rep_inv_self, vec2_eta]

/-- The differential commutes with the pullback. -/
theorem differentialOneRaw_pull1 (h : G) (f : (Fin 2 → G) → V) (a b c : G) :
    differentialOneRaw (pull1 ρ h f) ![a, b, c] =
      ρ h⁻¹ (differentialOneRaw f ![h * a, h * b, h * c]) := by
  change ρ h⁻¹ (f ![h * b, h * c]) - ρ h⁻¹ (f ![h * a, h * c]) + ρ h⁻¹ (f ![h * a, h * b]) =
    ρ h⁻¹ (f ![h * b, h * c] - f ![h * a, h * c] + f ![h * a, h * b])
  rw [map_add, map_sub]

/-- The pullback of a `U`-equivariant one-cochain by an element `h` with `h U h⁻¹ ⊆ U` is
`U`-equivariant. -/
theorem pull1_equivariant {U : Subgroup G} {h : G} (hn : ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    {f : (Fin 2 → G) → V} (hf : ∀ γ ∈ U, ∀ a b, f ![γ * a, γ * b] = ρ γ (f ![a, b])) :
    ∀ γ ∈ U, ∀ a b, pull1 ρ h f ![γ * a, γ * b] = ρ γ (pull1 ρ h f ![a, b]) := by
  intro γ hγ a b
  change ρ h⁻¹ (f ![h * (γ * a), h * (γ * b)]) = ρ γ (ρ h⁻¹ (f ![h * a, h * b]))
  have e : ∀ t, h * (γ * t) = h * γ * h⁻¹ * (h * t) := fun t => by group
  rw [e a, e b, hf _ (hn γ hγ), ← rep_mul_apply', ← rep_mul_apply',
    show h⁻¹ * (h * γ * h⁻¹) = γ * h⁻¹ by group]

/-- The pullback of a one-cocycle is a one-cocycle. -/
theorem pull1_closed (h : G) {f : (Fin 2 → G) → V} (hf : ∀ x, differentialOneRaw f x = 0) :
    ∀ x, differentialOneRaw (pull1 ρ h f) x = 0 := by
  intro x
  show differentialOneRaw (pull1 ρ h f) ![x 0, x 1, x 2] = 0
  rw [differentialOneRaw_pull1, hf, map_zero]

variable {W : Type} [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W)
  (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

/-- **Pullback of a cup product**: `h^*(f ⌣ g) = (h ⋆ f) ⌣ (h ⋆ g)` for a pairing invariant
under `h⁻¹`. -/
theorem spull2_cup11 {h : G} (hB : ∀ v w, B (ρ h⁻¹ v) (ρ' h⁻¹ w) = B v w)
    (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    spull2 h (cup11 B f g) = cup11 B (pull1 ρ h f) (pull1 ρ' h g) := by
  funext x
  change B (f ![h * x 0, h * x 1]) (g ![h * x 1, h * x 2]) =
    B (ρ h⁻¹ (f ![h * x 0, h * x 1])) (ρ' h⁻¹ (g ![h * x 1, h * x 2]))
  rw [hB]

end Pullback

section Levi

variable [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The Levi cocycle of a one-cochain `ω`: `A(h) = h ⋆ ω − ω`. -/
def leviCocycle (ω : (Fin 2 → G) → V) (h : G) : (Fin 2 → G) → V :=
  pull1 ρ h ω - ω

/-- The Levi cocycle is a right crossed homomorphism: `A(h k) = A(k) + k ⋆ A(h)`. -/
theorem leviCocycle_mul (ω : (Fin 2 → G) → V) (h k : G) :
    leviCocycle ρ ω (h * k) = leviCocycle ρ ω k + pull1 ρ k (leviCocycle ρ ω h) := by
  unfold leviCocycle
  rw [pull1_sub, pull1_mul]
  abel

theorem leviCocycle_one (ω : (Fin 2 → G) → V) : leviCocycle ρ ω 1 = 0 := by
  unfold leviCocycle
  rw [pull1_one, sub_self]

/-- `A(h⁻¹) = −h⁻¹ ⋆ A(h)`. -/
theorem leviCocycle_inv (ω : (Fin 2 → G) → V) (h : G) :
    leviCocycle ρ ω h⁻¹ = -pull1 ρ h⁻¹ (leviCocycle ρ ω h) := by
  have e := leviCocycle_mul ρ ω h h⁻¹
  rw [mul_inv_cancel, leviCocycle_one] at e
  rw [eq_neg_iff_add_eq_zero]
  exact e.symm

/-- The Levi cocycle is a one-cocycle when the coboundary of `ω` is `h`-equivariant. -/
theorem leviCocycle_closed {ω : (Fin 2 → G) → V} {ζ : (Fin 3 → G) → V}
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = ζ ![a, b, c]) {h : G}
    (hζ : ∀ a b c, ζ ![h * a, h * b, h * c] = ρ h (ζ ![a, b, c])) :
    ∀ x, differentialOneRaw (leviCocycle ρ ω h) x = 0 := by
  intro x
  show differentialOneRaw (pull1 ρ h ω - ω) ![x 0, x 1, x 2] = 0
  rw [differentialOneRaw_sub, differentialOneRaw_pull1, hd, hd, hζ, rep_inv_self, sub_self]

/-- The Levi cocycle of a `U`-equivariant cochain at an element `h` with `h U h⁻¹ ⊆ U` is
`U`-equivariant. -/
theorem leviCocycle_equivariant {U : Subgroup G} {ω : (Fin 2 → G) → V}
    (hω : ∀ γ ∈ U, ∀ a b, ω ![γ * a, γ * b] = ρ γ (ω ![a, b])) {h : G}
    (hn : ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∀ γ ∈ U, ∀ a b, leviCocycle ρ ω h ![γ * a, γ * b] = ρ γ (leviCocycle ρ ω h ![a, b]) := by
  intro γ hγ a b
  change pull1 ρ h ω ![γ * a, γ * b] - ω ![γ * a, γ * b] =
    ρ γ (pull1 ρ h ω ![a, b] - ω ![a, b])
  rw [pull1_equivariant ρ hn hω γ hγ a b, hω γ hγ a b, map_sub]

/-- The left action of `G` on one-cochains: `g · f = g⁻¹ ⋆ f`. -/
def cochainRep : Representation ℂ G ((Fin 2 → G) → V) where
  toFun g :=
    { toFun := pull1 ρ g⁻¹
      map_add' := pull1_add ρ g⁻¹
      map_smul' := fun c f => pull1_smul ρ g⁻¹ c f }
  map_one' := by
    apply LinearMap.ext
    intro f
    change pull1 ρ (1 : G)⁻¹ f = f
    rw [inv_one, pull1_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change pull1 ρ (g * h)⁻¹ f = pull1 ρ g⁻¹ (pull1 ρ h⁻¹ f)
    rw [pull1_mul, mul_inv_rev]

theorem cochainRep_apply (g : G) (f : (Fin 2 → G) → V) : cochainRep ρ g f = pull1 ρ g⁻¹ f :=
  rfl

/-- The Levi cocycle at `g⁻¹` is the coboundary of `ω` for the left action on cochains. -/
theorem leviCocycle_inv_eq (ω : (Fin 2 → G) → V) (g : G) :
    leviCocycle ρ ω g⁻¹ = cochainRep ρ g ω - ω := rfl

end Levi

end TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
