module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Equivariant

@[expose] public section


/-!
# Twisted equivariant functions on a `G`-set from a cocycle that is a coboundary on the stabilizers

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open scoped Classical

section Twisted

variable {G X E : Type} [Group G] [MulAction G X] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E)

/-- **Cusp potentials.**  If a crossed homomorphism `f` is the coboundary of a vector `u r` on the stabilizer of each orbit
representative `r`, then there is a function `Φ` on the `G`-set with `Φ (g x) = g Φ(x) + f g` for all `g`, `x`. -/
theorem exists_twisted (S : RepSystem G X) (f : G → E) (hf : ∀ g h, f (g * h) = ρ g (f h) + f g)
    (hcusp : ∀ r ∈ S.R, ∃ u : E, ∀ g : G, g • r = r → f g = ρ g u - u) :
    ∃ Φ : X → E, ∀ (g : G) (x : X), Φ (g • x) = ρ g (Φ x) + f g := by
  choose! u hu using hcusp
  choose! r hr γ hγ using S.cover
  let Φ : X → E := fun x => ρ (γ x) (-u (r x)) + f (γ x)
  have key : ∀ (x : X) (h : G), Φ (h • x) = ρ h (Φ x) + f h := by
    intro x h
    have e1 : (h * γ x) • r x = h • x := by rw [mul_smul, hγ]
    -- the representative of `h • x` is `r x`, and `γ (h • x) = h * γ x * s` with `s` in the stabilizer
    have e2 : γ (h • x) • r (h • x) = h • x := hγ _
    have hrr : r (h • x) = r x := by
      have : ((γ x)⁻¹ * h⁻¹ * γ (h • x)) • r (h • x) = r x := by
        calc ((γ x)⁻¹ * h⁻¹ * γ (h • x)) • r (h • x)
            = ((γ x)⁻¹ * h⁻¹) • (γ (h • x) • r (h • x)) := by rw [mul_smul]
          _ = ((γ x)⁻¹ * h⁻¹) • (h • x) := by rw [e2]
          _ = (γ x)⁻¹ • x := by rw [mul_smul, inv_smul_smul]
          _ = r x := inv_smul_eq_iff.2 (hγ x).symm
      exact S.inj (r (h • x)) (hr _) (r x) (hr _) _ this
    obtain ⟨s, hs⟩ : ∃ s : G, s = (h * γ x)⁻¹ * γ (h • x) := ⟨_, rfl⟩
    have hsr : s • r x = r x := by
      have : γ (h • x) • r x = h • x := by rw [← hrr]; exact e2
      calc s • r x = (h * γ x)⁻¹ • (γ (h • x) • r x) := by rw [hs, mul_smul]
        _ = (h * γ x)⁻¹ • (h • x) := by rw [this]
        _ = (h * γ x)⁻¹ • ((h * γ x) • r x) := by rw [e1]
        _ = r x := inv_smul_smul _ _
    have hγeq : γ (h • x) = (h * γ x) * s := by rw [hs]; group
    have hfs := hu (r x) (hr x) s hsr
    show ρ (γ (h • x)) (-u (r (h • x))) + f (γ (h • x)) = ρ h (ρ (γ x) (-u (r x)) + f (γ x)) + f h
    rw [hrr, hγeq, hf, hf, hfs]
    simp only [map_mul, Module.End.mul_apply, map_add, map_neg, map_sub]
    abel
  exact ⟨Φ, fun g x => key x g⟩


/-- A function supported on one orbit, determined by an invariant value at the base point. -/
theorem exists_eqfn_of_invariant (c₀ : X) (w : E) (hw : ∀ γ : G, γ • c₀ = c₀ → ρ γ w = w) :
    ∃ Φ : X → E, Φ ∈ EqFn G X ρ ∧ Φ c₀ = w ∧ ∀ x, x ∉ MulAction.orbit G c₀ → Φ x = 0 := by
  let Φ : X → E := fun x =>
    if h : x ∈ MulAction.orbit G c₀ then ρ (Classical.choose (MulAction.mem_orbit_iff.mp h)) w else 0
  have key : ∀ g : G, Φ (g • c₀) = ρ g w := by
    intro g
    have h : g • c₀ ∈ MulAction.orbit G c₀ := ⟨g, rfl⟩
    have hΦ : Φ (g • c₀) = ρ (Classical.choose (MulAction.mem_orbit_iff.mp h)) w := dite_eq_left h
    rw [hΦ]
    set g₁ := Classical.choose (MulAction.mem_orbit_iff.mp h) with hg₁
    have hg₁s : g₁ • c₀ = g • c₀ := Classical.choose_spec (MulAction.mem_orbit_iff.mp h)
    have hst : (g⁻¹ * g₁) • c₀ = c₀ := by rw [mul_smul, hg₁s, inv_smul_smul]
    have := hw _ hst
    calc ρ g₁ w = ρ g (ρ (g⁻¹ * g₁) w) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ g w := by rw [this]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro γ x
    by_cases hx : x ∈ MulAction.orbit G c₀
    · obtain ⟨g, rfl⟩ := hx
      rw [← mul_smul, key, key, map_mul]
      rfl
    · have hx' : γ • x ∉ MulAction.orbit G c₀ := by
        intro h
        apply hx
        obtain ⟨g, hg⟩ := h
        exact ⟨γ⁻¹ * g, by
          have hg' : g • c₀ = γ • x := hg
          show (γ⁻¹ * g) • c₀ = x
          rw [mul_smul, hg', inv_smul_smul]⟩
      have e1 : Φ x = 0 := dite_eq_right hx
      have e2 : Φ (γ • x) = 0 := dite_eq_right hx'
      rw [e1, e2, map_zero]
  · have := key 1
    simpa using this
  · intro x hx
    exact dite_eq_right hx

end Twisted


section Cyclic

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E)

theorem cocycle_one (f : G → E) (hf : ∀ g h, f (g * h) = ρ g (f h) + f g) : f 1 = 0 := by
  have := hf 1 1
  rw [mul_one, map_one, Module.End.one_apply] at this
  have h2 : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact this.trans (add_comm _ _)
  exact (add_left_cancel h2).symm

/-- A crossed homomorphism that is a coboundary on a generator is a coboundary on the whole cyclic group. -/
theorem cocycle_zpow (f : G → E) (hf : ∀ g h, f (g * h) = ρ g (f h) + f g) (σ : G) (u : E)
    (h : f σ = ρ σ u - u) (j : ℤ) : f (σ ^ j) = ρ (σ ^ j) u - u := by
  induction j using Int.induction_on with
  | zero => simp [cocycle_one ρ f hf]
  | succ i ih =>
    have e : σ ^ ((i : ℤ) + 1) = σ ^ (i : ℤ) * σ := zpow_add_one _ _
    rw [e, hf, h, ih, map_mul]
    simp only [Module.End.mul_apply, map_sub]
    abel
  | pred i ih =>
    have e : σ ^ (-(i : ℤ)) = σ ^ (-(i : ℤ) - 1) * σ := by rw [zpow_sub_one, inv_mul_cancel_right]
    have h1 := hf (σ ^ (-(i : ℤ) - 1)) σ
    rw [← e, h, ih] at h1
    have e2 : σ ^ (-(i : ℤ)) = σ ^ (-(i : ℤ) - 1) * σ := e
    rw [e2, map_mul] at h1
    simp only [Module.End.mul_apply, map_sub] at h1
    linear_combination (norm := module) (-1 : ℂ) • h1

theorem rep_zpow_fix (σ : G) (w : E) (h : ρ σ w = w) (j : ℤ) : ρ (σ ^ j) w = w := by
  induction j using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, map_mul, Module.End.mul_apply, h, ih]
  | pred i ih =>
    have e : σ ^ (-(i : ℤ) - 1) = σ ^ (-(i : ℤ)) * σ⁻¹ := zpow_sub_one _ _
    have hinv : ρ σ⁻¹ w = w := by
      calc ρ σ⁻¹ w = ρ σ⁻¹ (ρ σ w) := by rw [h]
        _ = w := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [e, map_mul, Module.End.mul_apply, hinv, ih]

end Cyclic

section Translate

variable {G X E : Type} [Group G] [MulAction G X] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E)

/-- If a crossed homomorphism is a coboundary on the stabilizer of `x`, it is one on the stabilizer of `γ x`. -/
theorem stab_coboundary_translate (f : G → E) (hf : ∀ g h, f (g * h) = ρ g (f h) + f g) (x : X) (u : E)
    (hu : ∀ s : G, s • x = x → f s = ρ s u - u) (γ : G) :
    ∀ s : G, s • (γ • x) = γ • x → f s = ρ s (ρ γ u - f γ) - (ρ γ u - f γ) := by
  intro s hs
  have ht : (γ⁻¹ * s * γ) • x = x := by
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  have h1 := hu _ ht
  have h2 := hf γ (γ⁻¹ * s * γ)
  have h3 := hf s γ
  have e : γ * (γ⁻¹ * s * γ) = s * γ := by group
  rw [e, h3, h1] at h2
  simp only [map_mul, Module.End.mul_apply, map_sub] at h2 ⊢
  have h5 : ∀ y : E, ρ γ (ρ γ⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [h5] at h2
  linear_combination (norm := module) h2

end Translate

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
