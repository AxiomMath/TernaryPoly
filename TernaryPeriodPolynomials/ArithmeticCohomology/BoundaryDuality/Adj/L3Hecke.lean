module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Cusp

@[expose] public section


/-!
# Local terms of the Hecke cocycles at the cusp elements

This file evaluates the local terms of the cup primitives of `(T x, y)` and `(x, T y)` (see
`AdjL3Cusp`) at a cusp element `g` of the group `G`, as sums of local terms of the cup primitive
`θ'` on the stabilizer `H` of the base coset:

* `heckeLeft_localTerm_two`, `heckeRight_localTerm_two`: `g` has trivial transits (the
  transversal along the `g`-orbit of the base coset is `r (j) = g ^ i`), so only the cosets `jl`
  (carried to the base coset) and `ji` (fixed by `g`) contribute; the primitives of the cocycles
  at `g` are explicit.
* `heckeLeft_localTerm_cycle`, `heckeRight_localTerm_cycle`: `g` has a unique fixed coset `f`,
  `g ^ p` acts trivially on the `p + 1` cosets, and the other cocycle vanishes at `g`.

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

section Left

variable {A A' : Rep.{0, 0, 0} ℂ G} {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
  (hinv : ∀ g v w, B (A.ρ g v) (A'.ρ g w) = B v w) (ρ𝔾 : Representation ℂ 𝔾 A)
  (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (embedded : Function.Injective embed)

variable (j₀) in
/-- The explicit primitive of the Hecke cocycle at a cusp with trivial transits. -/
def twoPrimitive (x : G → A) (g : G) (m : ℕ) (ji : S.index) (u₁ u₂ : A) : A :=
  heckeCorrection j₀ r ρ𝔾 x + A.ρ (g ^ m)⁻¹ (∑ i ∈ Finset.range (m + 1), A.ρ (g ^ i) u₁) +
    A.ρ (r ji)⁻¹ u₂

include compat embedded in
/-- **The Hecke cocycle at a cusp with trivial transits** has the explicit primitive
`twoPrimitive`. -/
theorem heckeFun_two {x : G → A} (hx : IsCocycle A.ρ x) {g : G} {m : ℕ} {jl ji : S.index}
    (hne : jl ≠ ji) (hother : ∀ j, j ≠ jl → j ≠ ji → transit r hr g j = 1)
    (hr0 : r j₀ = 1) (hnl : S.next g jl = j₀) (hni : S.next g ji = ji) (hrl : r jl = g ^ m)
    {u₁ u₂ : A}
    (hu₁ : baseCocycle ρ𝔾 x (transit r hr g jl) = (A.ρ (transit r hr g jl : G) - 1) u₁)
    (hu₂ : baseCocycle ρ𝔾 x (transit r hr g ji) = (A.ρ (transit r hr g ji : G) - 1) u₂) :
    heckeFun S A ρ𝔾 x g = (A.ρ g - 1) (twoPrimitive j₀ r ρ𝔾 x g m ji u₁ u₂) := by
  have hx' := isCocycle_baseCocycle (S := S) (j₀ := j₀) ρ𝔾 compat embedded hx
  have ht1 : (transit r hr g jl : G) = g ^ (m + 1) := by
    rw [transit_val, hnl, hr0, hrl, inv_one, mul_one, pow_succ]
  have ht2 : (transit r hr g ji : G) = r ji * g * (r ji)⁻¹ := by
    rw [transit_val, hni]
  rw [heckeFun_eq_transverseSum r hr ρ𝔾 compat embedded hx g]
  have hsum : transverseSum r hr A.ρ (baseCocycle ρ𝔾 x) g =
      A.ρ (r jl)⁻¹ (baseCocycle ρ𝔾 x (transit r hr g jl)) +
        A.ρ (r ji)⁻¹ (baseCocycle ρ𝔾 x (transit r hr g ji)) := by
    unfold transverseSum
    refine Finset.sum_eq_add_of_mem jl ji (Finset.mem_univ _) (Finset.mem_univ _) hne ?_
    intro c _ hc
    rw [hother c hc.1 hc.2, hx'.map_one, map_zero]
  rw [hsum, hu₁, hu₂, ht1, ht2, hrl, rep_inv_conj_sub (ρ := A.ρ) (r ji) g u₂]
  have e1 : A.ρ (g ^ m)⁻¹ ((A.ρ (g ^ (m + 1)) - 1) u₁) =
      (A.ρ g - 1) (A.ρ (g ^ m)⁻¹ (∑ i ∈ Finset.range (m + 1), A.ρ (g ^ i) u₁)) := by
    rw [rep_sub_comm_pow_inv, rep_sub_geom]
  rw [e1]
  unfold twoPrimitive
  simp only [map_add, LinearMap.sub_apply, Module.End.one_apply]
  abel

include hinv compat embedded in
/-- **The local term of the Hecke primitive in the first slot at a cusp with trivial transits.** -/
theorem heckeLeft_localTerm_two {x : G → A} (hx : IsCocycle A.ρ x) {y : G → A'}
    (hy : IsCocycle A'.ρ y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾 x) (fun h => y h) θ')
    {g : G} {m : ℕ} {jl ji : S.index} (hne : jl ≠ ji)
    (hother : ∀ j, j ≠ jl → j ≠ ji → transit r hr g j = 1)
    (hr0 : r j₀ = 1) (hnl : S.next g jl = j₀) (hni : S.next g ji = ji) (hrl : r jl = g ^ m)
    {u₁ u₂ : A}
    (hu₂ : baseCocycle ρ𝔾 x (transit r hr g ji) = (A.ρ (transit r hr g ji : G) - 1) u₂) :
    localTerm B (fun g => ∑ j, leftTerm r hr B A'.ρ (baseCocycle ρ𝔾 x) y θ' g j +
        B (heckeCorrection j₀ r ρ𝔾 x) (y g)) y g (twoPrimitive j₀ r ρ𝔾 x g m ji u₁ u₂) =
      localTerm B θ' (fun h => y h) (transit r hr g jl) u₁ +
        localTerm B θ' (fun h => y h) (transit r hr g ji) u₂ := by
  have hx' := isCocycle_baseCocycle (S := S) (j₀ := j₀) ρ𝔾 compat embedded hx
  have ht1 : (transit r hr g jl : G) = g ^ (m + 1) := by
    rw [transit_val, hnl, hr0, hrl, inv_one, mul_one, pow_succ]
  have hsum := leftTerm_sum_two (θ' := θ') r hr hinv hx' hy hθ' hne hother hr0 hnl hni hu₂
  rw [localTerm_def, hsum]
  have hpair := pair_geom hinv hy g m u₁
  rw [localTerm_def, localTerm_def]
  unfold twoPrimitive
  simp only [map_add, LinearMap.add_apply]
  rw [ht1]
  linear_combination -hpair

include hinv in
/-- **The local term of the Hecke primitive in the first slot at a cusp with a cycle** (the second
cocycle vanishes at `g`). -/
theorem heckeLeft_localTerm_cycle {p : ℕ} (hp : p.Prime) (hcard : Fintype.card S.index = p + 1)
    {x : G → A} {y : G → A'} (hy : IsCocycle A'.ρ y) {θ' : stab S j₀ → ℂ}
    (hX' : IsCocycle (A.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾 x))
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾 x) (fun h => y h) θ')
    {g : G} (hg : y g = 0) {f : S.index} (hfix : ∀ j, S.next g j = j ↔ j = f)
    (hpow : ∀ j, S.next (g ^ p) j = j) {j₁ : S.index} (hj₁ : j₁ ≠ f) {u₀ u₁ : A}
    (hu₀ : baseCocycle ρ𝔾 x (transit r hr g f) = (A.ρ (transit r hr g f : G) - 1) u₀)
    (hu₁ : baseCocycle ρ𝔾 x (transit r hr (g ^ p) j₁) =
      (A.ρ (transit r hr (g ^ p) j₁ : G) - 1) u₁) (v : A) :
    localTerm B (fun g => ∑ j, leftTerm r hr B A'.ρ (baseCocycle ρ𝔾 x) y θ' g j +
        B (heckeCorrection j₀ r ρ𝔾 x) (y g)) y g v =
      localTerm B θ' (fun h => y h) (transit r hr g f) u₀ +
        localTerm B θ' (fun h => y h) (transit r hr (g ^ p) j₁) u₁ := by
  rw [localTerm_def, hg, map_zero, map_zero, add_zero, sub_zero]
  exact leftTerm_sum_cycle (θ' := θ') r hr hp hcard hinv hX' hy hθ' hg hfix hpow hj₁ hu₀ hu₁

end Left

section Right

variable {A A' : Rep.{0, 0, 0} ℂ G} {B : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
  (hinv : ∀ g v w, B (A.ρ g v) (A'.ρ g w) = B v w) (ρ𝔾' : Representation ℂ 𝔾 A')
  (compat' : ∀ g, A'.ρ g = ρ𝔾' (embed g)) (embedded : Function.Injective embed)

include hinv compat' embedded in
/-- **The local term of the Hecke primitive in the second slot at a cusp with trivial transits.** -/
theorem heckeRight_localTerm_two {x : G → A} (hx : IsCocycle A.ρ x) {y : G → A'}
    (hy : IsCocycle A'.ρ y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (fun h => x h)
      (baseCocycle ρ𝔾' y) θ') {g : G} {m : ℕ} {jl ji : S.index} (hne : jl ≠ ji)
    (hother : ∀ j, j ≠ jl → j ≠ ji → transit r hr g j = 1) (hrl : r jl = g ^ m) {v : A}
    (hv : x g = (A.ρ g - 1) v) :
    localTerm B (fun g => ∑ j, rightTerm r hr B x (baseCocycle ρ𝔾' y) θ' g j -
        B (x g) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y))) (heckeFun S A' ρ𝔾' y) g v =
      localTerm B θ' (baseCocycle ρ𝔾' y) (transit r hr g jl) v +
        localTerm B θ' (baseCocycle ρ𝔾' y) (transit r hr g ji) (A.ρ (r ji) v - x (r ji)) := by
  have hy' := isCocycle_baseCocycle (S := S) (j₀ := j₀) ρ𝔾' compat' embedded hy
  have hsumY : transverseSum r hr A'.ρ (baseCocycle ρ𝔾' y) g =
      A'.ρ (r jl)⁻¹ (baseCocycle ρ𝔾' y (transit r hr g jl)) +
        A'.ρ (r ji)⁻¹ (baseCocycle ρ𝔾' y (transit r hr g ji)) := by
    unfold transverseSum
    refine Finset.sum_eq_add_of_mem jl ji (Finset.mem_univ _) (Finset.mem_univ _) hne ?_
    intro c _ hc
    rw [hother c hc.1 hc.2, hy'.map_one, map_zero]
  have hY := heckeFun_eq_transverseSum r hr ρ𝔾' compat' embedded hy g
  have hsumR := rightTerm_sum_two (θ' := θ') (x := x) r hr hy' hθ' hne hother
  have hxl : x (r jl) = (A.ρ (r jl) - 1) v := by
    rw [hrl]; exact cocycle_pow_primitive hx hv m
  rw [localTerm_def, localTerm_def, localTerm_def, hY, hsumY, hsumR]
  unfold rightTerm
  have i1 : B v (A'.ρ (r jl)⁻¹ (baseCocycle ρ𝔾' y (transit r hr g jl))) =
      B (A.ρ (r jl) v) (baseCocycle ρ𝔾' y (transit r hr g jl)) :=
    invariant_pair_inv_right hinv _ _ _
  have i2 : B v (A'.ρ (r ji)⁻¹ (baseCocycle ρ𝔾' y (transit r hr g ji))) =
      B (A.ρ (r ji) v) (baseCocycle ρ𝔾' y (transit r hr g ji)) :=
    invariant_pair_inv_right hinv _ _ _
  have i3 : B (A.ρ g v) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y)) =
      B v (heckeCorrection j₀ r ρ𝔾' y) := hinv _ _ _
  have hxg : x g = A.ρ g v - v := by rw [hv]; simp
  rw [hxl] at *
  simp only [map_add, map_sub, LinearMap.sub_apply, Module.End.one_apply, hxg, i1, i2, i3]
  ring

include hinv in
/-- **The local term of the Hecke primitive in the second slot at a cusp with a cycle** (the first
cocycle vanishes at `g`; the second cocycle `Y` is a coboundary at `g`). -/
theorem heckeRight_localTerm_cycle {p : ℕ} (hp : p.Prime) (hcard : Fintype.card S.index = p + 1)
    {x : G → A} (hx : IsCocycle A.ρ x) {θ' : stab S j₀ → ℂ} {y : G → A'}
    (hY' : IsCocycle (A'.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾' y))
    (hθ' : IsCupPrimitive B (A'.ρ.comp (stab S j₀).subtype) (fun h => x h)
      (baseCocycle ρ𝔾' y) θ') {g : G} (hg : x g = 0) {f : S.index}
    (hfix : ∀ j, S.next g j = j ↔ j = f) (hpow : ∀ j, S.next (g ^ p) j = j) {j₁ : S.index}
    (hj₁ : j₁ ≠ f) {w : A'} (hw : heckeFun S A' ρ𝔾' y g = (A'.ρ g - 1) w) {v : A}
    (hv : x g = (A.ρ g - 1) v) :
    localTerm B (fun g => ∑ j, rightTerm r hr B x (baseCocycle ρ𝔾' y) θ' g j -
        B (x g) (A'.ρ g (heckeCorrection j₀ r ρ𝔾' y))) (heckeFun S A' ρ𝔾' y) g v =
      localTerm B θ' (baseCocycle ρ𝔾' y) (transit r hr g f) (-x (r f)) +
        localTerm B θ' (baseCocycle ρ𝔾' y) (transit r hr (g ^ p) j₁) (-x (r j₁)) := by
  have hv0 : x g = (A.ρ g - 1) (0 : A) := by rw [hg]; simp
  rw [localTerm_eq_of_primitive (B := B) (ρ := A.ρ) (ρ' := A'.ρ) hinv hv hv0 hw, localTerm_def,
    map_zero, LinearMap.zero_apply, sub_zero, hg, map_zero, LinearMap.zero_apply, sub_zero]
  exact rightTerm_sum_cycle (θ' := θ') (x := x) r hr hp hcard hinv hx hY' hθ' hg hfix hpow hj₁

end Right

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
