module

public import Mathlib

@[expose] public section

/-!
# Equivariant functions on a free `Γ`-set with finitely many orbits

Formalized by Claude Sonnet 5.5.

For a group `Γ` acting freely on `X` with a finite system `S.R` of orbit representatives (`RepSystem`) and a `Γ`-module `E`:
* `EqFn Γ X ρ`: the equivariant functions `X → E`; `eq_zero_of_rep_zero`: determined by the representatives;
  `extendFn`, `extendFn_mem`, `extendFn_rep`: every function on the representatives extends (freeness);
  `eqFn_finite`: finite dimensionality;
* `sum_rep_indep`: the orbit sum of an invariant function does not depend on the system of representatives;
* `pairR e S F G = ∑_{r ∈ R} ⟨F r, G r⟩` is a perfect pairing of `EqFn ρ` with `EqFn ρ'` for a perfect invariant pairing `e`
  (`pairR_left_perfect`, `pairR_right_perfect`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open scoped Classical

section Equivariant

variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X]

/-- A system of representatives of the `Γ`-orbits of `X`: every point is a translate of a unique representative. -/
structure RepSystem (Γ X : Type) [Group Γ] [MulAction Γ X] where
  R : Finset X
  cover : ∀ x : X, ∃ r ∈ R, ∃ γ : Γ, γ • r = x
  inj : ∀ r ∈ R, ∀ r' ∈ R, ∀ γ : Γ, γ • r = r' → r = r'

/-- `Γ` acts freely on `X`. -/
def FreeAction (Γ X : Type) [Group Γ] [MulAction Γ X] : Prop := ∀ (γ : Γ) (x : X), γ • x = x → γ = 1

variable {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ Γ E)

/-- The `Γ`-equivariant functions `X → E`. -/
def EqFn (Γ X : Type) [Group Γ] [MulAction Γ X] {E : Type} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ Γ E) : Submodule ℂ (X → E) where
  carrier := {F | ∀ (γ : Γ) (x : X), F (γ • x) = ρ γ (F x)}
  add_mem' := fun {a b} ha hb γ x => by simp [ha γ x, hb γ x]
  zero_mem' := fun γ x => by simp
  smul_mem' := fun c {a} ha γ x => by simp [ha γ x]

theorem mem_EqFn {F : X → E} : F ∈ EqFn Γ X ρ ↔ ∀ (γ : Γ) (x : X), F (γ • x) = ρ γ (F x) := Iff.rfl

variable (S : RepSystem Γ X)

theorem eq_zero_of_rep_zero {F : X → E} (hF : F ∈ EqFn Γ X ρ) (h : ∀ r ∈ S.R, F r = 0) : F = 0 := by
  funext x
  obtain ⟨r, hr, γ, rfl⟩ := S.cover x
  rw [hF, h r hr, map_zero]
  rfl

theorem decomp_unique (hfree : FreeAction Γ X) {p p' : S.R × Γ} (h : p.2 • (p.1 : X) = p'.2 • (p'.1 : X)) :
    p = p' := by
  have h1 : (p'.2⁻¹ * p.2) • (p.1 : X) = (p'.1 : X) := by
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have h2 : p.1 = p'.1 := Subtype.ext (S.inj _ p.1.2 _ p'.1.2 _ h1)
  have h3 : p'.2⁻¹ * p.2 = 1 := hfree _ _ (by rw [← h2] at h1; exact h1)
  have h4 : p.2 = p'.2 := by
    calc p.2 = p'.2 * (p'.2⁻¹ * p.2) := by group
      _ = p'.2 := by rw [h3, mul_one]
  exact Prod.ext h2 h4

theorem exists_decomp (x : X) : ∃ p : S.R × Γ, p.2 • (p.1 : X) = x := by
  obtain ⟨r, hr, γ, rfl⟩ := S.cover x
  exact ⟨(⟨r, hr⟩, γ), rfl⟩

/-- The decomposition `x = γ • r` of a point into a representative and a group element. -/
def dec (x : X) : S.R × Γ := Classical.choose (exists_decomp S x)

theorem dec_spec (x : X) : (dec S x).2 • ((dec S x).1 : X) = x := Classical.choose_spec (exists_decomp S x)

theorem dec_eq (hfree : FreeAction Γ X) {x : X} {p : S.R × Γ} (h : p.2 • (p.1 : X) = x) : dec S x = p :=
  decomp_unique S hfree ((dec_spec S x).trans h.symm)

/-- Extension of a function on the representatives to an equivariant function. -/
def extendFn (f : X → E) : X → E := fun x => ρ (dec S x).2 (f (dec S x).1)

theorem extendFn_mem (hfree : FreeAction Γ X) (f : X → E) : extendFn ρ S f ∈ EqFn Γ X ρ := by
  intro γ x
  have h : dec S (γ • x) = ((dec S x).1, γ * (dec S x).2) :=
    dec_eq S hfree (by simp only [mul_smul, dec_spec])
  unfold extendFn
  rw [h, map_mul]
  rfl

theorem extendFn_rep (hfree : FreeAction Γ X) (f : X → E) {r : X} (hr : r ∈ S.R) :
    extendFn ρ S f r = f r := by
  have h : dec S r = (⟨r, hr⟩, 1) := dec_eq S hfree (by simp)
  unfold extendFn
  rw [h]
  simp


theorem sum_rep_indep (hfree : FreeAction Γ X) (S S' : RepSystem Γ X) (ψ : X → ℂ)
    (hψ : ∀ (γ : Γ) (x : X), ψ (γ • x) = ψ x) : ∑ r ∈ S.R, ψ r = ∑ r ∈ S'.R, ψ r := by
  refine Finset.sum_bij (fun a _ => ((dec S' a).1 : X)) (fun a _ => (dec S' a).1.2) ?_ ?_ ?_
  · intro a ha a' ha' h
    have e1 := dec_spec S' a
    have e2 := dec_spec S' a'
    have : ((dec S' a').2 * (dec S' a).2⁻¹) • a = a' := by
      calc ((dec S' a').2 * (dec S' a).2⁻¹) • a
          = ((dec S' a').2 * (dec S' a).2⁻¹) • ((dec S' a).2 • ((dec S' a).1 : X)) := by rw [e1]
        _ = (dec S' a').2 • ((dec S' a).1 : X) := by rw [← mul_smul]; group
        _ = (dec S' a').2 • ((dec S' a').1 : X) := by rw [h]
        _ = a' := e2
    exact S.inj a ha a' ha' _ this
  · intro b hb
    have hb' := dec_spec S b
    obtain ⟨⟨a, g⟩, hag⟩ : ∃ p, dec S b = p := ⟨_, rfl⟩
    rw [hag] at hb'
    have ha : (a : X) ∈ S.R := a.2
    refine ⟨a, ha, ?_⟩
    have : dec S' (a : X) = (⟨b, hb⟩, g⁻¹) := by
      apply dec_eq S' hfree
      change g⁻¹ • b = a
      have : g • (a : X) = b := hb'
      rw [← this, ← mul_smul, inv_mul_cancel, one_smul]
    rw [this]
  · intro a ha
    have e1 := dec_spec S' a
    have := hψ (dec S' a).2 ((dec S' a).1 : X)
    rw [e1] at this
    exact this


section Perfect

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  (ρ : Representation ℂ Γ E) (ρ' : Representation ℂ Γ E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) (S : RepSystem Γ X)

/-- The orbit-sum pairing of two functions on `X`: `∑_{r ∈ R} ⟨F r, G r⟩`. -/
def pairR (F : X → E) (G : X → E') : ℂ := ∑ r ∈ S.R, e (F r) (G r)

theorem pairR_left_perfect (hfree : FreeAction Γ X) (hL : ∀ v, (∀ w, e v w = 0) → v = 0) {F : X → E}
    (hF : F ∈ EqFn Γ X ρ) (h : ∀ G ∈ EqFn Γ X ρ', pairR e S F G = 0) : F = 0 := by
  apply eq_zero_of_rep_zero ρ S hF
  intro r₀ hr₀
  apply hL
  intro w
  have h1 := h _ (extendFn_mem ρ' S hfree (fun x => if x = r₀ then w else 0))
  unfold pairR at h1
  rw [Finset.sum_eq_single r₀] at h1
  · rwa [extendFn_rep ρ' S hfree _ hr₀, ite_eq_left rfl] at h1
  · intro r hr hne
    rw [extendFn_rep ρ' S hfree _ hr, ite_eq_right hne, map_zero]
  · intro hn
    exact absurd hr₀ hn

theorem pairR_right_perfect (hfree : FreeAction Γ X) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) {G : X → E'}
    (hG : G ∈ EqFn Γ X ρ') (h : ∀ F ∈ EqFn Γ X ρ, pairR e S F G = 0) : G = 0 := by
  apply eq_zero_of_rep_zero ρ' S hG
  intro r₀ hr₀
  apply hR
  intro v
  have h1 := h _ (extendFn_mem ρ S hfree (fun x => if x = r₀ then v else 0))
  unfold pairR at h1
  rw [Finset.sum_eq_single r₀] at h1
  · rwa [extendFn_rep ρ S hfree _ hr₀, ite_eq_left rfl] at h1
  · intro r hr hne
    rw [extendFn_rep ρ S hfree _ hr, ite_eq_right hne, map_zero, LinearMap.zero_apply]
  · intro hn
    exact absurd hr₀ hn

include S in
/-- The space of equivariant functions is finite dimensional when the orbits are finite. -/
theorem eqFn_finite [FiniteDimensional ℂ E] : FiniteDimensional ℂ (EqFn Γ X ρ) := by
  let f : EqFn Γ X ρ →ₗ[ℂ] (S.R → E) :=
    (LinearMap.pi fun r : S.R => LinearMap.proj (r : X)) ∘ₗ (EqFn Γ X ρ).subtype
  have hinj : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    have hd : (F.1 - G.1) = 0 := by
      apply eq_zero_of_rep_zero ρ S ((EqFn Γ X ρ).sub_mem F.2 G.2)
      intro r hr
      have := congrFun h ⟨r, hr⟩
      simpa [f, sub_eq_zero] using this
    exact sub_eq_zero.mp hd
  exact Module.Finite.of_injective f hinj

end Perfect

end Equivariant

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
