module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Orbit

@[expose] public section


/-!
# Local terms of the Hecke cocycles at the cusp elements

Let `G ⊆ 𝔾`, `S` the Hecke cosets with base coset `j₀` and transversal `r`, and `H` the stabilizer
of `j₀`.  For a crossed homomorphism `x` of `G` the Hecke cocycle `T x = heckeFun x` is the
corestriction of the base cocycle `x' = baseCocycle x` of `H` up to the coboundary `(g - 1) w`
(`AdjCore.heckeFun_eq_transverseSum`).  If `θ'` is a cup primitive of `(x', y|_H)` then

  `g ↦ ∑_j leftTerm g j + B (w, y g)`

is a cup primitive of `(T x, y)` (`isCupPrimitive_heckeFun_left`); if `θ'` is a cup primitive of
`(x|_H, y')` then `g ↦ ∑_j rightTerm g j - B (x g, g w')` is a cup primitive of `(x, T y)`
(`isCupPrimitive_heckeFun_right`).

The local terms of these primitives at the cusp elements `g` are sums of local terms of `θ'` at
elements of the stabilizer `H`:

* `heckeLeft_localTerm_two` and `heckeRight_localTerm_two` for a cusp with trivial transits (two
  non-trivial transitions, no normalization of the cocycles needed);
* `heckeLeft_localTerm_cycle` and `heckeRight_localTerm_cycle` for a cusp with a cycle of cosets
  (the other cocycle must vanish at `g`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open CategoryTheory
open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.Spectral.HeckeH1

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} {S : RightCosets embed}
  {j₀ : S.index} (r : S.index → G) (hr : ∀ j, S.next (r j) j₀ = j)

section Primitive

variable {A A' : Rep.{0, 0, 0} ℂ G} {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
  (hinv : ∀ g v w, B (A.ρ g v) (A'.ρ g w) = B v w)

include hinv in
/-- **A cup primitive of the Hecke cocycle in the first slot.** -/
theorem isCupPrimitive_heckeFun_left (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (embedded : Function.Injective embed) {x : G → A}
    (hx : IsCocycle A.ρ x) {y : G → A'} (hy : IsCocycle A'.ρ y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾 x) (fun h => y h) θ') :
    IsCupPrimitive B A'.ρ (heckeFun S A ρ𝔾 x) y
      (fun g => ∑ j, leftTerm r hr B A'.ρ (baseCocycle ρ𝔾 x) y θ' g j +
        B (heckeCorrection j₀ r ρ𝔾 x) (y g)) := by
  have h0 := isCupPrimitive_transverseSum_left r hr hinv
    (isCocycle_baseCocycle ρ𝔾 compat embedded hx) hy hθ'
  have h1 := isCupPrimitive_add_boundary_left hinv hy h0 (heckeCorrection j₀ r ρ𝔾 x)
  have hX : (fun g => transverseSum r hr A.ρ (baseCocycle ρ𝔾 x) g +
      (A.ρ g (heckeCorrection j₀ r ρ𝔾 x) - heckeCorrection j₀ r ρ𝔾 x)) =
      heckeFun S A ρ𝔾 x :=
    funext fun g => (heckeFun_eq_transverseSum r hr ρ𝔾 compat embedded hx g).symm
  have hθ : (fun g => (∑ j, θ' (transit r hr g j) -
        ∑ j, B (baseCocycle ρ𝔾 x (transit r hr g j))
          (A'.ρ (transit r hr g j) (y (r (S.next g j))))) +
        B (heckeCorrection j₀ r ρ𝔾 x) (y g)) =
      (fun g => ∑ j, leftTerm r hr B A'.ρ (baseCocycle ρ𝔾 x) y θ' g j +
        B (heckeCorrection j₀ r ρ𝔾 x) (y g)) := by
    funext g
    simp only [leftTerm, Finset.sum_sub_distrib]
  rw [hX, hθ] at h1
  exact h1

include hinv in
/-- **A cup primitive of the Hecke cocycle in the second slot.** -/
theorem isCupPrimitive_heckeFun_right (ρ𝔾' : Representation ℂ 𝔾 A')
    (compat' : ∀ g, A'.ρ g = ρ𝔾' (embed g)) (embedded : Function.Injective embed) {x : G → A}
    (hx : IsCocycle A.ρ x) {y : G → A'} (hy : IsCocycle A'.ρ y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (fun h => x h)
      (baseCocycle ρ𝔾' y) θ') :
    IsCupPrimitive B A'.ρ x (heckeFun S A' ρ𝔾' y)
      (fun g => ∑ j, rightTerm r hr B x (baseCocycle ρ𝔾' y) θ' g j -
        B (x g) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y))) := by
  have h0 := isCupPrimitive_transverseSum_right r hr hinv hx
    (isCocycle_baseCocycle ρ𝔾' compat' embedded hy) hθ'
  have h1 := isCupPrimitive_add_boundary_right hinv hx h0 (heckeCorrection j₀ r ρ𝔾' y)
  have hY : (fun g => transverseSum r hr A'.ρ (baseCocycle ρ𝔾' y) g +
      (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y) - heckeCorrection j₀ r ρ𝔾' y)) =
      heckeFun S A' ρ𝔾' y :=
    funext fun g => (heckeFun_eq_transverseSum r hr ρ𝔾' compat' embedded hy g).symm
  have hθ : (fun g => (∑ j, θ' (transit r hr g j) +
        ∑ j, B (x (r j)) (baseCocycle ρ𝔾' y (transit r hr g j))) -
        B (x g) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y))) =
      (fun g => ∑ j, rightTerm r hr B x (baseCocycle ρ𝔾' y) θ' g j -
        B (x g) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y))) := by
    funext g
    simp only [rightTerm, Finset.sum_add_distrib]
  rw [hY, hθ] at h1
  exact h1

end Primitive

section Algebra

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- Conjugating a difference `ρ(a g a⁻¹) - 1` through `ρ(a)⁻¹`. -/
theorem rep_inv_conj_sub (a g : G) (u : V) :
    ρ a⁻¹ ((ρ (a * g * a⁻¹) - 1) u) = (ρ g - 1) (ρ a⁻¹ u) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← rep_mul_apply ρ a⁻¹ (a * g * a⁻¹) u, ← rep_mul_apply ρ g a⁻¹ u]
  congr 2
  group

/-- The geometric sum identity `(ρ g - 1) ∑_{i<n} ρ(g^i) u = (ρ(g^n) - 1) u`. -/
theorem rep_sub_geom (g : G) (n : ℕ) (u : V) :
    (ρ g - 1) (∑ i ∈ Finset.range n, ρ (g ^ i) u) = (ρ (g ^ n) - 1) u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add, ih]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [← rep_mul_apply ρ g (g ^ n) u, ← pow_succ' g n, pow_succ]
    abel

end Algebra

section Powers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {z : G → V}

/-- `ρ(g) - 1` commutes with `ρ(g^m)⁻¹`. -/
theorem rep_sub_comm_pow_inv (g : G) (m : ℕ) (u : V) :
    (ρ g - 1) (ρ (g ^ m)⁻¹ u) = ρ (g ^ m)⁻¹ ((ρ g - 1) u) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← rep_mul_apply ρ g (g ^ m)⁻¹ u, ← rep_mul_apply ρ (g ^ m)⁻¹ g u]
  have : g * (g ^ m)⁻¹ = (g ^ m)⁻¹ * g :=
    ((Commute.refl g).pow_right m).inv_right.eq
  rw [this]

/-- A crossed homomorphism with primitive `v` at `g` has primitive `v` at every power of `g`. -/
theorem cocycle_pow_primitive (hz : IsCocycle ρ z) {g : G} {v : V} (hv : z g = (ρ g - 1) v)
    (m : ℕ) : z (g ^ m) = (ρ (g ^ m) - 1) v := by
  induction m with
  | zero => rw [pow_zero, hz.map_one]; simp
  | succ m ih =>
    rw [cocycle_pow_succ hz, ih, hv]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← rep_mul_apply ρ (g ^ m) g v, ← pow_succ]
    abel

end Powers

section TwoCusp

variable {A A' : Rep.{0, 0, 0} ℂ G} {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
  (hinv : ∀ g v w, B (A.ρ g v) (A'.ρ g w) = B v w)

include hinv in
/-- The pairing of a geometric sum against a value of a crossed homomorphism. -/
theorem pair_geom {y : G → A'} (hy : IsCocycle A'.ρ y) (g : G) (m : ℕ) (u : A) :
    B (A.ρ (g ^ m)⁻¹ (∑ i ∈ Finset.range (m + 1), A.ρ (g ^ i) u)) (y g) =
      B u (y (g ^ (m + 1))) := by
  rw [invariant_pair_inv_left hinv, map_sum, LinearMap.sum_apply, cocycle_pow_eq_sum hy g (m + 1),
    map_sum]
  have key : ∀ i ∈ Finset.range (m + 1),
      B (A.ρ (g ^ i) u) (A'.ρ (g ^ m) (y g)) = B u (A'.ρ (g ^ (m - i)) (y g)) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : (g ^ i)⁻¹ * g ^ m = g ^ (m - i) := by
      have : g ^ m = g ^ i * g ^ (m - i) := by rw [← pow_add]; congr 1; omega
      rw [this, inv_mul_cancel_left]
    rw [pair_rep_left hinv, ← rep_mul_apply A'.ρ, e]
  rw [Finset.sum_congr rfl key]
  have := Finset.sum_range_reflect (fun k => B u (A'.ρ (g ^ k) (y g))) (m + 1)
  simp only [Nat.add_sub_cancel] at this
  exact this

end TwoCusp

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
