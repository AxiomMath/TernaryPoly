module

public import Mathlib

@[expose] public section


/-!
# The alternation of the cup product of two cocycles on an abelian group

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, ("the two-generator Koszul
complex for the radical pairs degree one with degree one into its top orientation line").

For an abelian group `N`, crossed homomorphisms `c : N → V`, `c' : N → W` (for `ρ`, `ρ'`) and an invariant pairing `e : V × W → ℂ`, the cup product
`ζ(u, v) = e(c u, ρ'(u) c' v)` is a `ℂ`-valued 2-cocycle and its alternation `a(u, v) = ζ(u, v) - ζ(v, u)` is bi-additive and alternating
(`altForm_mul`); on `ℤ²` it therefore transforms by the determinant under automorphisms (`altForm_hom`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section Alt

variable {N V W : Type} [CommGroup N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ N V) (ρ' : Representation ℂ N W) (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

/-- The alternation of the cup product of two crossed homomorphisms. -/
def altForm (c : N → V) (c' : N → W) (u v : N) : ℂ :=
  e (c u) (ρ' u (c' v)) - e (c v) (ρ' v (c' u))

variable {ρ ρ' e}

theorem altForm_swap (c : N → V) (c' : N → W) (u v : N) :
    altForm ρ' e c c' u v = - altForm ρ' e c c' v u := by
  unfold altForm; ring

theorem altForm_self (c : N → V) (c' : N → W) (u : N) : altForm ρ' e c c' u u = 0 := by
  unfold altForm; ring

theorem altForm_mul (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (u w v : N) :
    altForm ρ' e c c' (u * w) v = altForm ρ' e c c' u v + altForm ρ' e c c' w v := by
  have comm' : ∀ (x y : N) (b : W), ρ' x (ρ' y b) = ρ' y (ρ' x b) := fun x y b => by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hcw : ρ' w (c' v) + c' w = ρ' v (c' w) + c' v := by
    rw [← hc' w v, ← hc' v w, mul_comm]
  have hcu : ρ u (c v) + c u = ρ v (c u) + c v := by
    rw [← hc u v, ← hc v u, mul_comm]
  set x := c' w with hx
  set z := ρ' u (ρ' v x) with hz
  have hz' : ρ' v (ρ' u x) = z := comm' v u x
  -- applying the invariant pairing to `hcu` paired with `z`
  have h1 := congrArg (fun a => e a z) hcu
  simp only [map_add, LinearMap.add_apply] at h1
  have h1a : e (ρ u (c v)) z = e (c v) (ρ' v x) := by
    have := he u (c v) (ρ' v x)
    rw [← this]
  have h1b : e (ρ v (c u)) z = e (c u) (ρ' u x) := by
    have := he v (c u) (ρ' u x)
    rw [← hz'] ; exact this
  -- applying `ρ' u` to `hcw` paired with `c u`
  have h2 := congrArg (fun b => e (c u) (ρ' u b)) hcw
  simp only [map_add] at h2
  have e1 : e (c (u * w)) (ρ' (u * w) (c' v)) = e (c w) (ρ' w (c' v)) + e (c u) (ρ' (u * w) (c' v)) := by
    rw [hc, map_add, LinearMap.add_apply, map_mul, Module.End.mul_apply]
    congr 1
    exact he u (c w) (ρ' w (c' v))
  have e2 : e (c v) (ρ' v (c' (u * w))) = e (c v) (ρ' v (ρ' u x)) + e (c v) (ρ' v (c' u)) := by
    rw [hc', map_add, map_add]
  have e3 : ρ' (u * w) (c' v) = ρ' u (ρ' w (c' v)) := by rw [map_mul, Module.End.mul_apply]
  unfold altForm
  rw [e1, e2, e3, hz']
  rw [e3] at e1
  rw [← hz] at h2
  linear_combination h2 + h1 - h1a + h1b

theorem altForm_mul_right (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (u v w : N) :
    altForm ρ' e c c' u (v * w) = altForm ρ' e c c' u v + altForm ρ' e c c' u w := by
  rw [altForm_swap c c' u (v * w), altForm_mul he hc hc', altForm_swap c c' v u, altForm_swap c c' w u]
  ring

theorem altForm_one_left (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (v : N) : altForm ρ' e c c' 1 v = 0 := by
  have := altForm_mul he hc hc' 1 1 v
  rw [mul_one] at this
  linear_combination (-1 : ℂ) * this

theorem altForm_zpow_left (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (u v : N) (k : ℤ) : altForm ρ' e c c' (u ^ k) v = k * altForm ρ' e c c' u v := by
  induction k using Int.induction_on with
  | zero => simp [altForm_one_left he hc hc']
  | succ i ih =>
    rw [zpow_add_one, altForm_mul he hc hc', ih]; push_cast; ring
  | pred i ih =>
    have h := altForm_mul he hc hc' (u ^ (-(i : ℤ) - 1)) u v
    rw [← zpow_add_one, sub_add_cancel] at h
    rw [ih] at h
    push_cast at h ih ⊢
    linear_combination (-1 : ℂ) * h

theorem altForm_zpow_right (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (u v : N) (k : ℤ) : altForm ρ' e c c' u (v ^ k) = k * altForm ρ' e c c' u v := by
  rw [altForm_swap c c' u, altForm_zpow_left he hc hc', altForm_swap c c' v u]; ring

/-- **Transformation under a change of two generators**: `a(s₁^p s₂^q, s₁^r s₂^t) = (p t - q r) a(s₁, s₂)`. -/
theorem altForm_gen (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)
    {c : N → V} (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) {c' : N → W} (hc' : ∀ x y, c' (x * y) = ρ' x (c' y) + c' x)
    (s1 s2 : N) (p q r t : ℤ) :
    altForm ρ' e c c' (s1 ^ p * s2 ^ q) (s1 ^ r * s2 ^ t) = (p * t - q * r) * altForm ρ' e c c' s1 s2 := by
  have a1 : altForm ρ' e c c' (s1 ^ p) (s1 ^ r * s2 ^ t) = p * (t * altForm ρ' e c c' s1 s2) := by
    rw [altForm_zpow_left he hc hc', altForm_mul_right he hc hc', altForm_zpow_right he hc hc',
      altForm_zpow_right he hc hc', altForm_self]
    ring
  have a2 : altForm ρ' e c c' (s2 ^ q) (s1 ^ r * s2 ^ t) = q * (- r * altForm ρ' e c c' s1 s2) := by
    rw [altForm_zpow_left he hc hc', altForm_mul_right he hc hc', altForm_zpow_right he hc hc',
      altForm_zpow_right he hc hc', altForm_self, altForm_swap c c' s2 s1]
    ring
  rw [altForm_mul he hc hc', a1, a2]
  ring

end Alt

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
