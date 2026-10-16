module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreStab

@[expose] public section


/-!
# Corestriction along a transversal, projection formulas and the Hecke operator in transversal form

Let `G ⊆ 𝔾` act on finitely many right cosets `G α_j`, let `H` be the stabilizer of the coset `j₀`
and let `r_j ∈ G` carry `j₀` to `j`.  For a representation `ρ` of `G` and a crossed homomorphism
`X'` of `H` (for the restriction of `ρ`) the *transversal sum*

  `(cor X') (g) = ∑_j r_j⁻¹ • X' (r_j g r_{j g}⁻¹)`

is a crossed homomorphism of `G` (`isCocycle_transverseSum`), the corestriction of `X'`.

* **Projection formula, first slot.**  If `θ'` is a cup primitive of `(X', y|_H)` for a crossed
  homomorphism `y` of `G`, then
  `∑_j θ'(k_j g) - ∑_j B(X'(k_j g), k_j(g) • y(r_{j g}))`, with `k_j(g) = r_j g r_{j g}⁻¹`, is a
  cup primitive of `(cor X', y)` (`isCupPrimitive_transverseSum_left`).
* **Projection formula, second slot.**  If `θ'` is a cup primitive of `(x|_H, Y')` for a crossed
  homomorphism `x` of `G`, then `∑_j θ'(k_j g) + ∑_j B(x(r_j), Y'(k_j g))` is a cup primitive of
  `(x, cor Y')` (`isCupPrimitive_transverseSum_right`).
* **The Hecke formula in transversal form.**  For a crossed homomorphism `x` of `G`, the Hecke
  cocycle `(T x)(g) = ∑_j ρ(α_j)⁻¹ x(δ(g, j))` equals the corestriction of the crossed homomorphism
  `h ↦ ρ(α_{j₀})⁻¹ x(δ(h, j₀))` of the stabilizer up to the coboundary `(g - 1) w`, where
  `w = ∑_j ρ(α_{j₀} r_j)⁻¹ x(δ(r_j, j₀))` (`heckeFun_eq_transverseSum`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.Spectral.HeckeH1

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} {S : RightCosets embed}
  {j₀ : S.index} (r : S.index → G) (hr : ∀ j, S.next (r j) j₀ = j)

section Pairing

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- For an invariant pairing, `B (a⁻¹ • v, w) = B (v, a • w)`. -/
theorem invariant_pair_inv_left (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (a : G) (v : V)
    (w : W) : B (ρ a⁻¹ v) w = B v (ρ' a w) := by
  have e := hinv a (ρ a⁻¹ v) w
  rw [rep_apply_inv ρ] at e
  exact e.symm

/-- For an invariant pairing, `B (v, a⁻¹ • w) = B (a • v, w)`. -/
theorem invariant_pair_inv_right (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) (a : G) (v : V)
    (w : W) : B v (ρ' a⁻¹ w) = B (ρ a v) w := by
  have e := hinv a v (ρ' a⁻¹ w)
  rw [rep_apply_inv ρ'] at e
  exact e.symm

end Pairing

section Transverse

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- **The transversal sum** `∑_j r_j⁻¹ • X' (r_j g r_{j g}⁻¹)`: the corestriction from the
stabilizer of `j₀` to `G` of a function `X'` on the stabilizer, computed along the transversal
`r`. -/
def transverseSum (ρ : Representation ℂ G V) (X' : stab S j₀ → V) (g : G) : V :=
  ∑ j, ρ (r j)⁻¹ (X' (transit r hr g j))

/-- `r_j⁻¹ · (r_j g r_{j g}⁻¹) = g · r_{j g}⁻¹`. -/
theorem inv_rep_mul_transit (g : G) (j : S.index) :
    (r j)⁻¹ * (transit r hr g j : G) = g * (r (S.next g j))⁻¹ := by
  rw [transit_val]
  group

/-- `r_j⁻¹ • (r_j g r_{j g}⁻¹) • v = g • r_{j g}⁻¹ • v`. -/
theorem rep_inv_rep_transit (ρ : Representation ℂ G V) (g : G) (j : S.index) (v : V) :
    ρ (r j)⁻¹ (ρ (transit r hr g j : G) v) = ρ g (ρ (r (S.next g j))⁻¹ v) := by
  rw [← rep_mul_apply ρ (r j)⁻¹ (transit r hr g j : G) v, inv_rep_mul_transit r hr g j,
    rep_mul_apply ρ g (r (S.next g j))⁻¹ v]

/-- The cocycle rule of a crossed homomorphism of the stabilizer, with the action written through
`G`. -/
theorem cocycle_stab_mul {ρ : Representation ℂ G V} {X' : stab S j₀ → V}
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') (a b : stab S j₀) :
    X' (a * b) = X' a + ρ (a : G) (X' b) :=
  hX' a b

/-- **The corestriction of a crossed homomorphism of the stabilizer is a crossed homomorphism.** -/
theorem isCocycle_transverseSum {ρ : Representation ℂ G V} {X' : stab S j₀ → V}
    (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X') :
    IsCocycle ρ (transverseSum r hr ρ X') := by
  intro g h
  have key : ∀ j, ρ (r j)⁻¹ (X' (transit r hr (g * h) j)) =
      ρ (r j)⁻¹ (X' (transit r hr g j)) +
        ρ g (ρ (r (S.next g j))⁻¹ (X' (transit r hr h (S.next g j)))) := by
    intro j
    rw [transit_mul r hr g h j, cocycle_stab_mul hX', map_add (ρ (r j)⁻¹),
      rep_inv_rep_transit r hr ρ g j]
  have hsum : ∑ j, ρ g (ρ (r (S.next g j))⁻¹ (X' (transit r hr h (S.next g j)))) =
      ∑ j, ρ g (ρ (r j)⁻¹ (X' (transit r hr h j))) :=
    Equiv.sum_comp (S.nextEquiv g) (fun k => ρ g (ρ (r k)⁻¹ (X' (transit r hr h k))))
  simp only [transverseSum]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, hsum, map_sum (ρ g)]

/-- The summand of the cup primitive of the projection formula in the first slot. -/
def leftTerm (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W) (X' : stab S j₀ → V)
    (y : G → W) (θ' : stab S j₀ → ℂ) (g : G) (j : S.index) : ℂ :=
  θ' (transit r hr g j) - B (X' (transit r hr g j)) (ρ' (transit r hr g j) (y (r (S.next g j))))

/-- **The local identity of the projection formula in the first slot**, in terms of the elements
`k = r_j g r_{j g}⁻¹`, `l = r_{j g} h r_{j g h}⁻¹` and the representatives `a = r_j`, `b = r_{j g}`,
`c = r_{j g h}`. -/
theorem leftTerm_core {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {X' : stab S j₀ → V} (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X')
    {y : G → W} (hy : IsCocycle ρ' y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ')
    (g h a b c : G) (k l : stab S j₀) (hk : (k : G) * b = a * g) (hl : (l : G) * c = b * h) :
    B (ρ a⁻¹ (X' k)) (ρ' g (y h)) =
      (θ' k - B (X' k) (ρ' (k : G) (y b))) + (θ' l - B (X' l) (ρ' (l : G) (y c))) -
        (θ' (k * l) - B (X' (k * l)) (ρ' ((k * l : stab S j₀) : G) (y c))) := by
  have F3 : B (ρ a⁻¹ (X' k)) (ρ' g (y h)) = B (X' k) (ρ' ((k : G) * b) (y h)) := by
    rw [invariant_pair_inv_left hinv, ← rep_mul_apply ρ' a g (y h), ← hk]
  have F5 : ρ' b (y h) = y (l : G) + ρ' (l : G) (y c) - y b := by
    have e := hy b h
    rw [← hl, hy (l : G) c] at e
    rw [e]
    abel
  have L1 : B (X' k) (ρ' ((k : G) * b) (y h)) =
      B (X' k) (ρ' (k : G) (y (l : G))) + B (X' k) (ρ' (k : G) (ρ' (l : G) (y c))) -
        B (X' k) (ρ' (k : G) (y b)) := by
    rw [rep_mul_apply ρ' (k : G) b (y h), F5]
    simp only [map_add, map_sub]
  have F6 : θ' k + θ' l - θ' (k * l) = B (X' k) (ρ' (k : G) (y (l : G))) := hθ' k l
  have F7 : B (X' (k * l)) (ρ' ((k * l : stab S j₀) : G) (y c)) =
      B (X' k) (ρ' (k : G) (ρ' (l : G) (y c))) + B (X' l) (ρ' (l : G) (y c)) := by
    rw [cocycle_stab_mul hX' k l, Subgroup.coe_mul, rep_mul_apply ρ' (k : G) (l : G) (y c),
      map_add, LinearMap.add_apply, hinv]
  linear_combination F3 + L1 - F6 - F7

/-- The local identity of the projection formula in the first slot, at the coset `j`. -/
theorem leftTerm_identity {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {X' : stab S j₀ → V} (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X')
    {y : G → W} (hy : IsCocycle ρ' y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ')
    (g h : G) (j : S.index) :
    B (ρ (r j)⁻¹ (X' (transit r hr g j))) (ρ' g (y h)) =
      leftTerm r hr B ρ' X' y θ' g j + leftTerm r hr B ρ' X' y θ' h (S.next g j) -
        leftTerm r hr B ρ' X' y θ' (g * h) j := by
  have c := leftTerm_core hinv hX' hy hθ' g h (r j) (r (S.next g j))
    (r (S.next h (S.next g j))) (transit r hr g j) (transit r hr h (S.next g j))
    (transit_mul_rep r hr g j) (transit_mul_rep r hr h (S.next g j))
  simp only [leftTerm]
  rw [transit_mul r hr g h j, S.next_mul]
  exact c

/-- **Projection formula, first slot.**  If `θ'` is a cup primitive of `(X', y|_H)` then
`g ↦ ∑_j θ'(k_j g) - ∑_j B (X'(k_j g), k_j(g) • y(r_{j g}))` is a cup primitive of the
corestriction of `X'` and `y`. -/
theorem isCupPrimitive_transverseSum_left {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {X' : stab S j₀ → V} (hX' : IsCocycle (ρ.comp (stab S j₀).subtype) X')
    {y : G → W} (hy : IsCocycle ρ' y) {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) X' (fun h => y h) θ') :
    IsCupPrimitive B ρ' (transverseSum r hr ρ X') y
      (fun g => ∑ j, θ' (transit r hr g j) -
        ∑ j, B (X' (transit r hr g j)) (ρ' (transit r hr g j) (y (r (S.next g j))))) := by
  have hΘ : ∀ g, (∑ j, θ' (transit r hr g j) -
        ∑ j, B (X' (transit r hr g j)) (ρ' (transit r hr g j) (y (r (S.next g j))))) =
      ∑ j, leftTerm r hr B ρ' X' y θ' g j := by
    intro g
    simp only [leftTerm, Finset.sum_sub_distrib]
  intro g h
  have hB : B (transverseSum r hr ρ X' g) (ρ' g (y h)) =
      ∑ j, B (ρ (r j)⁻¹ (X' (transit r hr g j))) (ρ' g (y h)) := by
    simp only [transverseSum, map_sum, LinearMap.sum_apply]
  have hsum : ∑ j, leftTerm r hr B ρ' X' y θ' h (S.next g j) =
      ∑ j, leftTerm r hr B ρ' X' y θ' h j :=
    Equiv.sum_comp (S.nextEquiv g) (fun k => leftTerm r hr B ρ' X' y θ' h k)
  simp only [hΘ]
  rw [hB, Finset.sum_congr rfl (fun j _ => leftTerm_identity r hr hinv hX' hy hθ' g h j),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]

/-- The summand of the cup primitive of the projection formula in the second slot. -/
def rightTerm (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (x : G → V) (Y' : stab S j₀ → W)
    (θ' : stab S j₀ → ℂ) (g : G) (j : S.index) : ℂ :=
  θ' (transit r hr g j) + B (x (r j)) (Y' (transit r hr g j))

/-- **The local identity of the projection formula in the second slot**, in terms of the elements
`k = r_j g r_{j g}⁻¹`, `l = r_{j g} h r_{j g h}⁻¹` and the representatives `a = r_j`,
`b = r_{j g}`. -/
theorem rightTerm_core {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {x : G → V} (hx : IsCocycle ρ x) {Y' : stab S j₀ → W}
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y') {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ')
    (g a b : G) (k l : stab S j₀) (hk : (k : G) * b = a * g) :
    B (x g) (ρ' g (ρ' b⁻¹ (Y' l))) =
      (θ' k + B (x a) (Y' k)) + (θ' l + B (x b) (Y' l)) -
        (θ' (k * l) + B (x a) (Y' (k * l))) := by
  have hg : g = a⁻¹ * ((k : G) * b) := by
    rw [hk, inv_mul_cancel_left]
  have hgb : g * b⁻¹ = a⁻¹ * (k : G) := by
    rw [hg]
    group
  have G1 : ρ' g (ρ' b⁻¹ (Y' l)) = ρ' a⁻¹ (ρ' (k : G) (Y' l)) := by
    rw [← rep_mul_apply ρ' g b⁻¹ (Y' l), hgb, rep_mul_apply ρ' a⁻¹ (k : G) (Y' l)]
  have G3 : ρ a (x g) = x (k : G) + ρ (k : G) (x b) - x a := by
    have e := hx a g
    rw [← hk, hx (k : G) b] at e
    rw [e]
    abel
  have M1 : B (ρ (k : G) (x b)) (ρ' (k : G) (Y' l)) = B (x b) (Y' l) := hinv _ _ _
  have L1 : B (x g) (ρ' g (ρ' b⁻¹ (Y' l))) =
      B (x (k : G)) (ρ' (k : G) (Y' l)) + B (x b) (Y' l) - B (x a) (ρ' (k : G) (Y' l)) := by
    rw [G1, invariant_pair_inv_right hinv, G3]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, M1]
  have F6 : θ' k + θ' l - θ' (k * l) = B (x (k : G)) (ρ' (k : G) (Y' l)) := hθ' k l
  have E : B (x a) (Y' (k * l)) = B (x a) (Y' k) + B (x a) (ρ' (k : G) (Y' l)) := by
    rw [cocycle_stab_mul hY' k l, map_add]
  linear_combination L1 - F6 + E

/-- The local identity of the projection formula in the second slot, at the coset `j`. -/
theorem rightTerm_identity {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ} (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {x : G → V} (hx : IsCocycle ρ x) {Y' : stab S j₀ → W}
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y') {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ')
    (g h : G) (j : S.index) :
    B (x g) (ρ' g (ρ' (r (S.next g j))⁻¹ (Y' (transit r hr h (S.next g j))))) =
      rightTerm r hr B x Y' θ' g j + rightTerm r hr B x Y' θ' h (S.next g j) -
        rightTerm r hr B x Y' θ' (g * h) j := by
  have c := rightTerm_core hinv hx hY' hθ' g (r j) (r (S.next g j)) (transit r hr g j)
    (transit r hr h (S.next g j)) (transit_mul_rep r hr g j)
  simp only [rightTerm]
  rw [transit_mul r hr g h j]
  exact c

/-- **Projection formula, second slot.**  If `θ'` is a cup primitive of `(x|_H, Y')` then
`g ↦ ∑_j θ'(k_j g) + ∑_j B (x (r_j), Y'(k_j g))` is a cup primitive of `x` and the corestriction
of `Y'`. -/
theorem isCupPrimitive_transverseSum_right {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
    (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    {x : G → V} (hx : IsCocycle ρ x) {Y' : stab S j₀ → W}
    (hY' : IsCocycle (ρ'.comp (stab S j₀).subtype) Y') {θ' : stab S j₀ → ℂ}
    (hθ' : IsCupPrimitive B (ρ'.comp (stab S j₀).subtype) (fun h => x h) Y' θ') :
    IsCupPrimitive B ρ' x (transverseSum r hr ρ' Y')
      (fun g => ∑ j, θ' (transit r hr g j) + ∑ j, B (x (r j)) (Y' (transit r hr g j))) := by
  have hΘ : ∀ g, (∑ j, θ' (transit r hr g j) + ∑ j, B (x (r j)) (Y' (transit r hr g j))) =
      ∑ j, rightTerm r hr B x Y' θ' g j := by
    intro g
    simp only [rightTerm, Finset.sum_add_distrib]
  intro g h
  have hsum : ∑ j, rightTerm r hr B x Y' θ' h (S.next g j) =
      ∑ j, rightTerm r hr B x Y' θ' h j :=
    Equiv.sum_comp (S.nextEquiv g) (fun k => rightTerm r hr B x Y' θ' h k)
  have hB : B (x g) (ρ' g (transverseSum r hr ρ' Y' h)) =
      ∑ j, B (x g) (ρ' g (ρ' (r (S.next g j))⁻¹ (Y' (transit r hr h (S.next g j))))) := by
    have e : ∑ j, B (x g) (ρ' g (ρ' (r (S.next g j))⁻¹ (Y' (transit r hr h (S.next g j))))) =
        ∑ j, B (x g) (ρ' g (ρ' (r j)⁻¹ (Y' (transit r hr h j)))) :=
      Equiv.sum_comp (S.nextEquiv g)
        (fun k => B (x g) (ρ' g (ρ' (r k)⁻¹ (Y' (transit r hr h k)))))
    rw [e]
    simp only [transverseSum, map_sum]
  simp only [hΘ]
  rw [hB, Finset.sum_congr rfl (fun j _ => rightTerm_identity r hr hinv hx hY' hθ' g h j),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]

end Transverse

section Hecke

open CategoryTheory

/-- The representation `ρ𝔾` of `𝔾` restricts to the representation `A.ρ` of `G`: the action of
`ρ𝔾 M` after `A.ρ u` is the action of `M · u`. -/
theorem rep_mul_embed {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (M : 𝔾) (u : G) (v : A) :
    ρ𝔾 M (A.ρ u v) = ρ𝔾 (M * embed u) v := by
  rw [compat u]
  exact (rep_mul_apply ρ𝔾 M (embed u) v).symm

/-- `ρ(α_{j₀} u)⁻¹ v = u⁻¹ • ρ(α_{j₀})⁻¹ v`. -/
theorem rep_mul_embed_inv {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (a : G) (v : A) :
    ρ𝔾 (S.rep j₀ * embed a)⁻¹ v = A.ρ a⁻¹ (ρ𝔾 (S.rep j₀)⁻¹ v) := by
  rw [compat a⁻¹, map_inv embed a, mul_inv_rev, rep_mul_apply ρ𝔾]

/-- **The base cocycle** `h ↦ ρ(α_{j₀})⁻¹ x(δ(h, j₀))` of the stabilizer of the coset `j₀`, built
from a function `x` on `G`. -/
def baseCocycle {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A) (x : G → A)
    (h : stab S j₀) : A :=
  ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta h j₀))

/-- **The base cocycle of a crossed homomorphism is a crossed homomorphism** of the stabilizer. -/
theorem isCocycle_baseCocycle {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (embedded : Function.Injective embed)
    {x : G → A} (hx : IsCocycle A.ρ x) :
    IsCocycle (A.ρ.comp (stab S j₀).subtype) (baseCocycle ρ𝔾 x) := by
  intro h k
  have hmul : S.delta ((h * k : stab S j₀) : G) j₀ = S.delta h j₀ * S.delta k j₀ := by
    rw [Subgroup.coe_mul]
    exact delta_stab_mul (k := (k : G)) embedded h.2
  have hconj : ∀ w : A, ρ𝔾 (S.rep j₀)⁻¹ (A.ρ (S.delta (h : G) j₀) w) =
      A.ρ (h : G) (ρ𝔾 (S.rep j₀)⁻¹ w) := by
    intro w
    have e : (S.rep j₀)⁻¹ * embed (S.delta (h : G) j₀) = embed (h : G) * (S.rep j₀)⁻¹ := by
      rw [embed_delta_stab h.2]
      group
    rw [rep_mul_embed ρ𝔾 compat, e, compat (h : G), rep_mul_apply ρ𝔾]
  show ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta ((h * k : stab S j₀) : G) j₀)) =
    ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (h : G) j₀)) +
      A.ρ (h : G) (ρ𝔾 (S.rep j₀)⁻¹ (x (S.delta (k : G) j₀)))
  rw [hmul, hx (S.delta h j₀) (S.delta k j₀), map_add (ρ𝔾 (S.rep j₀)⁻¹), hconj]

variable (j₀) in
/-- The vector `w_j = ρ(α_{j₀} r_j)⁻¹ x(δ(r_j, j₀))`. -/
def heckeShift {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A) (x : G → A)
    (j : S.index) : A :=
  ρ𝔾 (S.rep j₀ * embed (r j))⁻¹ (x (S.delta (r j) j₀))

variable (j₀) in
/-- **The correction vector** `w = ∑_j ρ(α_{j₀} r_j)⁻¹ x(δ(r_j, j₀))`: the Hecke cocycle is the
corestriction of the base cocycle up to the coboundary `(g - 1) w`. -/
def heckeCorrection {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A) (x : G → A) : A :=
  ∑ j, ρ𝔾 (S.rep j₀ * embed (r j))⁻¹ (x (S.delta (r j) j₀))

/-- The correction vector is the sum of the vectors `w_j`. -/
theorem heckeCorrection_eq {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A) (x : G → A) :
    heckeCorrection j₀ r ρ𝔾 x = ∑ j, heckeShift j₀ r ρ𝔾 x j :=
  rfl

/-- The transition of `r_j g r_{j g}⁻¹` at `j₀` factors as `γ_j · δ(g, j) · γ_{j g}⁻¹`, where
`γ_j = δ(r_j, j₀)`. -/
theorem delta_transit (embedded : Function.Injective embed) (g : G) (j : S.index) :
    S.delta (transit r hr g j : G) j₀ =
      S.delta (r j) j₀ * S.delta g j * (S.delta (r (S.next g j)) j₀)⁻¹ := by
  apply embedded
  rw [embed_delta_stab (transit r hr g j).2]
  simp only [transit_val, map_mul, map_inv, S.delta_spec, hr]
  group

/-- **The algebraic core of the Hecke formula in transversal form.** -/
theorem heckeShift_core {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) {x : G → A} (hx : IsCocycle A.ρ x)
    {M M' p p' : 𝔾} {g γ d γ' : G} (hγ : M * embed γ = p⁻¹) (hγ' : embed γ' = M'⁻¹ * p'⁻¹)
    (hd : embed d = p * embed g * p'⁻¹) :
    ρ𝔾 M (x (γ * d * γ'⁻¹)) = ρ𝔾 p⁻¹ (x d) + ρ𝔾 M (x γ) - A.ρ g (ρ𝔾 M' (x γ')) := by
  have e1 : x (γ * d * γ'⁻¹) =
      x γ + A.ρ γ (x d) + A.ρ (γ * d) (-A.ρ γ'⁻¹ (x γ')) := by
    rw [hx (γ * d) γ'⁻¹, hx γ d, isCocycle_map_inv hx γ']
  have hgrp : M * embed (γ * d) * embed γ'⁻¹ = embed g * M' := by
    have h1 : M * (embed γ * embed d) = p⁻¹ * embed d := by
      rw [← mul_assoc, hγ]
    rw [map_mul embed γ d, h1, map_inv embed γ', hγ', hd]
    group
  have t1 : ρ𝔾 M (A.ρ γ (x d)) = ρ𝔾 p⁻¹ (x d) := by
    rw [rep_mul_embed ρ𝔾 compat M γ (x d), hγ]
  have t2 : ρ𝔾 M (A.ρ (γ * d) (-A.ρ γ'⁻¹ (x γ'))) = -A.ρ g (ρ𝔾 M' (x γ')) := by
    rw [rep_mul_embed ρ𝔾 compat M (γ * d), map_neg (ρ𝔾 (M * embed (γ * d))),
      rep_mul_embed ρ𝔾 compat (M * embed (γ * d)) γ'⁻¹ (x γ'), hgrp, compat g,
      ← rep_mul_apply ρ𝔾 (embed g) M' (x γ')]
  rw [e1, map_add (ρ𝔾 M), map_add (ρ𝔾 M), t1, t2]
  abel

/-- The Hecke summand at the coset `j`, in terms of the base cocycle at the transition
`r_j g r_{j g}⁻¹`. -/
theorem heckeShift_term {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (embedded : Function.Injective embed)
    {x : G → A} (hx : IsCocycle A.ρ x) (g : G) (j : S.index) :
    ρ𝔾 (S.rep j₀ * embed (r j))⁻¹ (x (S.delta (transit r hr g j : G) j₀)) =
      ρ𝔾 (S.rep j)⁻¹ (x (S.delta g j)) + heckeShift j₀ r ρ𝔾 x j -
        A.ρ g (heckeShift j₀ r ρ𝔾 x (S.next g j)) := by
  have hγ : (S.rep j₀ * embed (r j))⁻¹ * embed (S.delta (r j) j₀) = (S.rep j)⁻¹ := by
    rw [S.delta_spec, hr]
    group
  have hγ' : embed (S.delta (r (S.next g j)) j₀) =
      ((S.rep j₀ * embed (r (S.next g j)))⁻¹)⁻¹ * (S.rep (S.next g j))⁻¹ := by
    rw [S.delta_spec, hr]
    group
  have hd : embed (S.delta g j) = S.rep j * embed g * (S.rep (S.next g j))⁻¹ :=
    S.delta_spec g j
  rw [delta_transit r hr embedded g j]
  exact heckeShift_core ρ𝔾 compat hx hγ hγ' hd

/-- **The Hecke operator in transversal form.**  For a crossed homomorphism `x` of `G`, the Hecke
cocycle `g ↦ ∑_j ρ(α_j)⁻¹ x(δ(g, j))` is the corestriction of the base cocycle of the stabilizer
of `j₀`, plus the coboundary `(g - 1) w` of the correction vector `w`. -/
theorem heckeFun_eq_transverseSum {A : Rep.{0, 0, 0} ℂ G} (ρ𝔾 : Representation ℂ 𝔾 A)
    (compat : ∀ g, A.ρ g = ρ𝔾 (embed g)) (embedded : Function.Injective embed)
    {x : G → A} (hx : IsCocycle A.ρ x) (g : G) :
    heckeFun S A ρ𝔾 x g = transverseSum r hr A.ρ (baseCocycle ρ𝔾 x) g +
      (A.ρ g (heckeCorrection j₀ r ρ𝔾 x) - heckeCorrection j₀ r ρ𝔾 x) := by
  have key : ∀ j, ρ𝔾 (S.rep j)⁻¹ (x (S.delta g j)) =
      A.ρ (r j)⁻¹ (baseCocycle ρ𝔾 x (transit r hr g j)) +
        (A.ρ g (heckeShift j₀ r ρ𝔾 x (S.next g j)) - heckeShift j₀ r ρ𝔾 x j) := by
    intro j
    have h1 := heckeShift_term r hr ρ𝔾 compat embedded hx g j
    have h2 : ρ𝔾 (S.rep j₀ * embed (r j))⁻¹ (x (S.delta (transit r hr g j : G) j₀)) =
        A.ρ (r j)⁻¹ (baseCocycle ρ𝔾 x (transit r hr g j)) :=
      rep_mul_embed_inv ρ𝔾 compat (r j) (x (S.delta (transit r hr g j : G) j₀))
    rw [h2] at h1
    rw [h1]
    abel
  have hreindex : ∑ j, A.ρ g (heckeShift j₀ r ρ𝔾 x (S.next g j)) =
      A.ρ g (heckeCorrection j₀ r ρ𝔾 x) := by
    have e : ∑ j, A.ρ g (heckeShift j₀ r ρ𝔾 x (S.next g j)) =
        ∑ j, A.ρ g (heckeShift j₀ r ρ𝔾 x j) :=
      Equiv.sum_comp (S.nextEquiv g) (fun k => A.ρ g (heckeShift j₀ r ρ𝔾 x k))
    rw [e, heckeCorrection_eq, map_sum (A.ρ g)]
  rw [heckeFun_apply S A ρ𝔾 x g, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hreindex]
  rfl

end Hecke

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
