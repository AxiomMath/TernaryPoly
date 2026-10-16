module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.PairAlg
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Induction

@[expose] public section


/-!
# The Koszul value for cocycles with values in `Fun(X, E)`

Formalized by Claude Sonnet 5.5.

Let a commutative group `N` act on a finite set `X`, `ρ, ρ'` representations of `N` with an invariant pairing `e`, and `c, c'` crossed homomorphisms of `N` with values in the induced modules
`Fun(X, E)`, `Fun(X, E')` (`indRepQ`) with the summed pairing (`eindQ`).  For `u, v ∈ N` acting trivially on `X`:
* `AP_ind`: the Koszul value of `c, c'` at `(u, v)` is the sum over `x ∈ X` of the Koszul values of the evaluations `c(·)(x)`, `c'(·)(x)`;
* `AP_fun_smul`: the summand is constant along `N`-orbits.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.CuspidalInduction

variable {N : Type} [CommGroup N] {X : Type} [Fintype X] [MulAction N X] {E E' : Type} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup E'] [Module ℂ E'] {ρ : Representation ℂ N E} {ρ' : Representation ℂ N E'} {e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ}

/-- The Koszul value of the evaluations at `x`. -/
def APx (ρ' : Representation ℂ N E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) (u v : N) (c : N → (X → E)) (c' : N → (X → E')) (x : X) : ℂ :=
  AP ρ' e u v (c u x) (c v x) (c' u x) (c' v x)

theorem AP_ind (u v : N) (hu : ∀ x : X, u • x = x) (hv : ∀ x : X, v • x = x) (c : N → (X → E)) (c' : N → (X → E')) :
    AP (indRepQ (Q := X) ρ') (eindQ e) u v (c u) (c v) (c' u) (c' v) = ∑ x, APx ρ' e u v c c' x := by
  unfold AP APx
  rw [eindQ_apply, eindQ_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [indRepQ_apply, indRepQ_apply, inv_smul_eq_iff.mpr (hu x).symm, inv_smul_eq_iff.mpr (hv x).symm]
  rfl

omit [Fintype X] in
theorem Rel_eval (u v : N) (hu : ∀ x : X, u • x = x) (hv : ∀ x : X, v • x = x) (c : N → (X → E))
    (hc : ∀ a b, c (a * b) = indRepQ (Q := X) ρ a (c b) + c a) (x : X) :
    Rel u v ρ (c u x) (c v x) := by
  have h := congrFun (hc u v) x
  have h' := congrFun (hc v u) x
  rw [mul_comm v u] at h'
  have := h.symm.trans h'
  simp only [Pi.add_apply, indRepQ_apply, inv_smul_eq_iff.mpr (hu x).symm, inv_smul_eq_iff.mpr (hv x).symm] at this
  exact this

omit [Fintype X] in
theorem cocycle_shift (t : N) (ht : ∀ x : X, t • x = x) (c : N → (X → E))
    (hc : ∀ a b, c (a * b) = indRepQ (Q := X) ρ a (c b) + c a) (k : N) (x : X) :
    c t (k • x) = ρ k (c t x) + (c k (k • x) - ρ t (c k (k • x))) := by
  have h := congrFun (hc k t) (k • x)
  have h' := congrFun (hc t k) (k • x)
  rw [mul_comm k t] at h
  have hk : (k⁻¹ • (k • x) : X) = x := inv_smul_smul k x
  have htk : (t⁻¹ • (k • x) : X) = k • x := by
    rw [inv_smul_eq_iff, smul_comm, ht]
  have := h.symm.trans h'
  simp only [Pi.add_apply, indRepQ_apply, hk, htk] at this
  calc c t (k • x) = (ρ t (c k (k • x)) + c t (k • x)) - ρ t (c k (k • x)) := by abel
    _ = (ρ k (c t x) + c k (k • x)) - ρ t (c k (k • x)) := by rw [← this]
    _ = _ := by abel

omit [Fintype X] in
/-- **The summand is constant along `N`-orbits.** -/
theorem APx_smul (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b) (u v : N) (hu : ∀ x : X, u • x = x) (hv : ∀ x : X, v • x = x)
    (c : N → (X → E)) (c' : N → (X → E'))
    (hc : ∀ a b, c (a * b) = indRepQ (Q := X) ρ a (c b) + c a)
    (hc' : ∀ a b, c' (a * b) = indRepQ (Q := X) ρ' a (c' b) + c' a) (k : N) (x : X) :
    APx ρ' e u v c c' (k • x) = APx ρ' e u v c c' x := by
  unfold APx
  rw [cocycle_shift u hu c hc k x, cocycle_shift v hv c hc k x, cocycle_shift u hu c' hc' k x,
    cocycle_shift v hv c' hc' k x]
  have := AP_shift (ρ := ρ) (ρ' := ρ') (e := e) u v he k (Rel_eval u v hu hv c hc x) (Rel_eval u v hu hv c' hc' x)
    (-(c k (k • x))) (-(c' k (k • x)))
  simp only [map_neg, sub_neg_eq_add, neg_add_eq_sub] at this
  exact this

end TernaryPeriodPolynomials.Argument.RadicalInduction
