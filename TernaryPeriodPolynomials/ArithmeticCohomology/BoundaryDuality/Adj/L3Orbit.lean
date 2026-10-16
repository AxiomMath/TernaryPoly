module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreCores
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Cycle

@[expose] public section


/-!
# Orbit sums of the corestriction primitives at a cusp element

Let `G ⊆ 𝔾`, `S` the Hecke cosets, `j₀` the base coset, `r` a transversal and `H` the stabilizer of
`j₀`.  For crossed homomorphisms `X'` of `H` and `y` of `G` and a cup primitive `θ'` of `(X', y|_H)`
the projection formula (`AdjCore.isCupPrimitive_transverseSum_left`) writes the cup primitive of
`(cor X', y)` as the sum over the cosets `j` of `leftTerm g j`; for crossed homomorphisms `x` of
`G` and `Y'` of `H` and a cup primitive `θ'` of `(x|_H, Y')` the cup primitive of `(x, cor Y')` is
the sum of `rightTerm g j` (`AdjCore.isCupPrimitive_transverseSum_right`).

This file evaluates these sums at the two kinds of cusp elements `g` of the Hecke
correspondences of `Γ₁(3)`:

* **a cusp with a cycle** (`g` has a unique fixed coset `f` and `g ^ p` acts trivially on the
  `p + 1` cosets, `p` prime): when `y g = 0` the sum of `leftTerm g j` is the local term of `θ'` at
  the transition of `g` at `f` plus the local term at the transition of `g ^ p` at any other coset
  (`leftTerm_sum_cycle`); when `x g = 0` the same holds for `rightTerm` (`rightTerm_sum_cycle`);
* **a cusp with trivial transits** (the transversal along the cycle is `r (j) = g ^ i` and the
  transitions are trivial except at two cosets `jl`, `ji`): the sum has two terms
  (`leftTerm_sum_two`, `rightTerm_sum_two`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.Spectral.HeckeH1

section Cocycle

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {z : G → V}

/-- The value of a crossed homomorphism at a conjugate. -/
theorem cocycle_conj (hz : IsCocycle ρ z) (a c : G) :
    z (a * c * a⁻¹) = z a + ρ a (z c) - ρ (a * c * a⁻¹) (z a) := by
  have h1 := hz (a * c) a⁻¹
  have h2 := hz a c
  have h3 := isCocycle_map_inv hz a
  have h4 : ρ (a * c) (ρ a⁻¹ (z a)) = ρ (a * c * a⁻¹) (z a) :=
    (rep_mul_apply ρ (a * c) a⁻¹ _).symm
  rw [h1, h2, h3, map_neg, h4]
  abel

/-- The value of a crossed homomorphism at a power. -/
theorem cocycle_pow_succ (hz : IsCocycle ρ z) (g : G) (k : ℕ) :
    z (g ^ (k + 1)) = z (g ^ k) + ρ (g ^ k) (z g) := by
  rw [pow_succ]
  exact hz (g ^ k) g

/-- A crossed homomorphism vanishing at `g` vanishes at the powers of `g`. -/
theorem cocycle_pow_eq_zero (hz : IsCocycle ρ z) {g : G} (hg : z g = 0) (k : ℕ) :
    z (g ^ k) = 0 := by
  induction k with
  | zero => rw [pow_zero]; exact hz.map_one
  | succ k ih => rw [cocycle_pow_succ hz, ih, hg, map_zero, add_zero]

/-- The value of a crossed homomorphism at a power is the geometric sum. -/
theorem cocycle_pow_eq_sum (hz : IsCocycle ρ z) (g : G) (n : ℕ) :
    z (g ^ n) = ∑ i ∈ Finset.range n, ρ (g ^ i) (z g) := by
  induction n with
  | zero => rw [pow_zero, Finset.sum_range_zero]; exact hz.map_one
  | succ n ih => rw [cocycle_pow_succ hz, ih, Finset.sum_range_succ]

end Cocycle

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} {S : RightCosets embed}
  {j₀ : S.index} (r : S.index → G) (hr : ∀ j, S.next (r j) j₀ = j)

section Left

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {X' : stab S j₀ → V} {y : G → W} {θ' : stab S j₀ → ℂ}

/-- The summand of the projection formula at the identity vanishes. -/
theorem leftTerm_one (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') (j : S.index) :
    leftTerm r hr B ρ' X' y θ' 1 j = 0 := by
  have h1 : θ' 1 = 0 := hθ'.map_one hX'
  have h2 : X' 1 = 0 := hX'.map_one
  unfold leftTerm
  rw [transit_one, h1, h2, map_zero, LinearMap.zero_apply, sub_zero]

/-- The summand of the projection formula at an element with trivial transit vanishes. -/
theorem leftTerm_of_transit_eq_one (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') {g : G}
    {j : S.index} (hj : transit r hr g j = 1) : leftTerm r hr B ρ' X' y θ' g j = 0 := by
  have h1 : θ' 1 = 0 := hθ'.map_one hX'
  have h2 : X' 1 = 0 := hX'.map_one
  unfold leftTerm
  rw [hj, h1, h2, map_zero, LinearMap.zero_apply, sub_zero]

/-- The summands of the projection formula are additive along the powers of an element at which
`y` vanishes. -/
theorem leftTerm_pow_succ (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') (hy : IsCocycle ρ' y)
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') {g : G}
    (hg : y g = 0) (k : ℕ) (j : S.index) :
    leftTerm r hr B ρ' X' y θ' (g ^ (k + 1)) j =
      leftTerm r hr B ρ' X' y θ' (g ^ k) j + leftTerm r hr B ρ' X' y θ' g (S.next (g ^ k) j) := by
  have e := leftTerm_identity r hr hinv hX' hy hθ' (g ^ k) g j
  rw [hg, map_zero, map_zero, ← pow_succ] at e
  linear_combination e

/-- The sum of the summands along the powers of `g`. -/
theorem leftTerm_pow_eq_sum (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') (hy : IsCocycle ρ' y)
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') {g : G}
    (hg : y g = 0) (k : ℕ) (j : S.index) :
    leftTerm r hr B ρ' X' y θ' (g ^ k) j =
      ∑ i ∈ Finset.range k, leftTerm r hr B ρ' X' y θ' g (S.next (g ^ i) j) := by
  induction k with
  | zero =>
    rw [pow_zero, Finset.sum_range_zero]
    exact leftTerm_one r hr hX' hθ' j
  | succ k ih =>
    rw [leftTerm_pow_succ r hr hinv hX' hy hθ' hg, ih, Finset.sum_range_succ]

/-- **The summand at a fixed coset is a local term.**  If `g` fixes the coset `j` and `X'` takes
the value `(t - 1) u` at the transition `t = r_j g r_j⁻¹`, then the summand of the projection
formula is the local term of `θ'` at `t`, plus the correction `B (r_j⁻¹ u, y g)` which vanishes
when `y g = 0`. -/
theorem leftTerm_fixed (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hy : IsCocycle ρ' y)
    {g : G} {j : S.index} (hj : S.next g j = j) {u : V}
    (hu : X' (transit r hr g j) = (ρ (transit r hr g j : G) - 1) u) :
    leftTerm r hr B ρ' X' y θ' g j =
      localTerm B θ' (fun h => y h) (transit r hr g j) u + B (ρ (r j)⁻¹ u) (y g) := by
  have ht : (transit r hr g j : G) = r j * g * (r j)⁻¹ := by
    rw [transit_val, hj]
  have hyt : y (transit r hr g j : G) =
      y (r j) + ρ' (r j) (y g) - ρ' (transit r hr g j : G) (y (r j)) := by
    rw [ht]
    exact cocycle_conj hy (r j) g
  have hu' : X' (transit r hr g j) = ρ (transit r hr g j : G) u - u := by
    rw [hu]; simp
  unfold leftTerm
  rw [localTerm_def, hj, hu', hyt]
  have i1 : B (ρ (transit r hr g j : G) u) (ρ' (transit r hr g j : G) (y (r j))) =
      B u (y (r j)) := hinv _ _ _
  have i2 : B (ρ (r j)⁻¹ u) (y g) = B u (ρ' (r j) (y g)) := invariant_pair_inv_left hinv _ _ _
  simp only [map_sub, map_add, LinearMap.sub_apply, i1, i2]
  ring

/-- **The sum over the cosets at a cusp with a cycle** (left slot).  Let `y g = 0`, `g` have the
unique fixed coset `f` and `g ^ p` act trivially on the `p + 1` cosets.  Then the sum of the
summands of the projection formula is the local term at the transition of `g` at `f` plus the
local term at the transition of `g ^ p` at any other coset `j₁`. -/
theorem leftTerm_sum_cycle {p : ℕ} (hp : p.Prime) (hcard : Fintype.card S.index = p + 1)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') (hy : IsCocycle ρ' y)
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') {g : G}
    (hg : y g = 0) {f : S.index} (hfix : ∀ j, S.next g j = j ↔ j = f)
    (hpow : ∀ j, S.next (g ^ p) j = j) {j₁ : S.index} (hj₁ : j₁ ≠ f) {u₀ u₁ : V}
    (hu₀ : X' (transit r hr g f) = (ρ (transit r hr g f : G) - 1) u₀)
    (hu₁ : X' (transit r hr (g ^ p) j₁) = (ρ (transit r hr (g ^ p) j₁ : G) - 1) u₁) :
    ∑ j, leftTerm r hr B ρ' X' y θ' g j =
      localTerm B θ' (fun h => y h) (transit r hr g f) u₀ +
        localTerm B θ' (fun h => y h) (transit r hr (g ^ p) j₁) u₁ := by
  classical
  have hperm : (S.nextEquiv g) ^ p = 1 := by
    ext j
    rw [← next_pow_eq S g p j]
    exact hpow j
  have hfix' : ∀ j, (S.nextEquiv g) j = j ↔ j = f := hfix
  rw [sum_eq_fixed_add_cycle (S.nextEquiv g) hp hperm hcard hfix' _ hj₁]
  have e1 : ∑ i : Fin p, leftTerm r hr B ρ' X' y θ' g (((S.nextEquiv g) ^ (i : ℕ)) j₁) =
      leftTerm r hr B ρ' X' y θ' (g ^ p) j₁ := by
    rw [leftTerm_pow_eq_sum r hr hinv hX' hy hθ' hg, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [next_pow_eq S g i j₁]
  rw [e1]
  have hgp : y (g ^ p) = 0 := cocycle_pow_eq_zero hy hg p
  have hf := leftTerm_fixed (θ' := θ') r hr hinv hy ((hfix f).mpr rfl) hu₀
  have h1 := leftTerm_fixed (θ' := θ') r hr hinv hy (hpow j₁) hu₁
  rw [hf, h1, hg, hgp, map_zero, map_zero, add_zero, add_zero]

/-- **The sum of the summands at a cusp with trivial transits** (left slot): the transit of `g`
is trivial except at two cosets `jl ≠ ji`; the base coset has the trivial representative; `g` maps
`jl` to the base coset and fixes `ji`. -/
theorem leftTerm_sum_two (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') (hy : IsCocycle ρ' y)
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') {g : G}
    {jl ji : S.index} (hne : jl ≠ ji)
    (hother : ∀ j, j ≠ jl → j ≠ ji → transit r hr g j = 1) (hr0 : r j₀ = 1)
    (hnl : S.next g jl = j₀) (hni : S.next g ji = ji) {u : V}
    (hu : X' (transit r hr g ji) = (ρ (transit r hr g ji : G) - 1) u) :
    ∑ j, leftTerm r hr B ρ' X' y θ' g j =
      θ' (transit r hr g jl) +
        (localTerm B θ' (fun h => y h) (transit r hr g ji) u + B (ρ (r ji)⁻¹ u) (y g)) := by
  rw [Finset.sum_eq_add_of_mem jl ji (Finset.mem_univ _) (Finset.mem_univ _) hne
    (fun c _ hc => leftTerm_of_transit_eq_one r hr hX' hθ' (hother c hc.1 hc.2))]
  have h1 : leftTerm r hr B ρ' X' y θ' g jl = θ' (transit r hr g jl) := by
    unfold leftTerm
    rw [hnl, hr0, hy.map_one, map_zero, map_zero, sub_zero]
  rw [h1, leftTerm_fixed (θ' := θ') r hr hinv hy hni hu]

end Left

section Right

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {x : G → V} {Y' : stab S j₀ → W} {θ' : stab S j₀ → ℂ}

/-- The summand of the second-slot projection formula is a local term with the primitive
`-x (r_j)`. -/
theorem rightTerm_eq_localTerm (g : G) (j : S.index) :
    rightTerm r hr B x Y' θ' g j =
      localTerm B θ' Y' (transit r hr g j) (-x (r j)) := by
  simp only [rightTerm, localTerm_def, map_neg, LinearMap.neg_apply, sub_neg_eq_add]

/-- The summand of the second-slot projection formula at an element with trivial transit
vanishes when `x` is a crossed homomorphism. -/
theorem rightTerm_of_transit_eq_one (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') {g : G}
    {j : S.index} (hj : transit r hr g j = 1) : rightTerm r hr B x Y' θ' g j = 0 := by
  have h1 : θ' 1 = 0 := by
    have e := hθ' 1 1
    rw [mul_one, hY'.map_one] at e
    simp only [map_zero] at e
    linear_combination e
  have h2 : Y' 1 = 0 := hY'.map_one
  unfold rightTerm
  rw [hj, h1, h2, map_zero, add_zero]

/-- The summands of the second-slot projection formula are additive along the powers of an
element at which `x` vanishes. -/
theorem rightTerm_pow_succ (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hx : IsCocycle ρ x)
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') {g : G}
    (hg : x g = 0) (k : ℕ) (j : S.index) :
    rightTerm r hr B x Y' θ' (g ^ (k + 1)) j =
      rightTerm r hr B x Y' θ' (g ^ k) j + rightTerm r hr B x Y' θ' g (S.next (g ^ k) j) := by
  have e := rightTerm_identity r hr hinv hx hY' hθ' (g ^ k) g j
  rw [cocycle_pow_eq_zero hx hg k, map_zero, LinearMap.zero_apply, ← pow_succ] at e
  linear_combination e

/-- The sum of the second-slot summands along the powers of `g`. -/
theorem rightTerm_pow_eq_sum (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hx : IsCocycle ρ x)
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') {g : G}
    (hg : x g = 0) (k : ℕ) (j : S.index) :
    rightTerm r hr B x Y' θ' (g ^ k) j =
      ∑ i ∈ Finset.range k, rightTerm r hr B x Y' θ' g (S.next (g ^ i) j) := by
  induction k with
  | zero =>
    rw [pow_zero, Finset.sum_range_zero]
    have e := rightTerm_of_transit_eq_one r hr hY' hθ' (g := 1) (j := j) (transit_one r hr j)
    exact e
  | succ k ih =>
    rw [rightTerm_pow_succ r hr hinv hx hY' hθ' hg, ih, Finset.sum_range_succ]

/-- **The sum over the cosets at a cusp with a cycle** (right slot). -/
theorem rightTerm_sum_cycle {p : ℕ} (hp : p.Prime) (hcard : Fintype.card S.index = p + 1)
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (hx : IsCocycle ρ x)
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') {g : G}
    (hg : x g = 0) {f : S.index} (hfix : ∀ j, S.next g j = j ↔ j = f)
    (hpow : ∀ j, S.next (g ^ p) j = j) {j₁ : S.index} (hj₁ : j₁ ≠ f) :
    ∑ j, rightTerm r hr B x Y' θ' g j =
      localTerm B θ' Y' (transit r hr g f) (-x (r f)) +
        localTerm B θ' Y' (transit r hr (g ^ p) j₁) (-x (r j₁)) := by
  classical
  have hperm : (S.nextEquiv g) ^ p = 1 := by
    ext j
    rw [← next_pow_eq S g p j]
    exact hpow j
  have hfix' : ∀ j, (S.nextEquiv g) j = j ↔ j = f := hfix
  rw [sum_eq_fixed_add_cycle (S.nextEquiv g) hp hperm hcard hfix' _ hj₁]
  have e1 : ∑ i : Fin p, rightTerm r hr B x Y' θ' g (((S.nextEquiv g) ^ (i : ℕ)) j₁) =
      rightTerm r hr B x Y' θ' (g ^ p) j₁ := by
    rw [rightTerm_pow_eq_sum r hr hinv hx hY' hθ' hg, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [next_pow_eq S g i j₁]
  rw [e1, rightTerm_eq_localTerm, rightTerm_eq_localTerm]

/-- **The sum of the second-slot summands at a cusp with trivial transits.** -/
theorem rightTerm_sum_two (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y')
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') {g : G}
    {jl ji : S.index} (hne : jl ≠ ji)
    (hother : ∀ j, j ≠ jl → j ≠ ji → transit r hr g j = 1) :
    ∑ j, rightTerm r hr B x Y' θ' g j =
      rightTerm r hr B x Y' θ' g jl + rightTerm r hr B x Y' θ' g ji :=
  Finset.sum_eq_add_of_mem jl ji (Finset.mem_univ _) (Finset.mem_univ _) hne
    (fun c _ hc => rightTerm_of_transit_eq_one r hr hY' hθ' (hother c hc.1 hc.2))

end Right

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
