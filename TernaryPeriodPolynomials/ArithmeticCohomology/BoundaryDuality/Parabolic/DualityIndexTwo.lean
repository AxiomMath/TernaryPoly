module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityCochain

@[expose] public section


/-!
# From an index-two subgroup to the full group

Let `Γ` be a group containing the image of `ι : N → Γ` with index two: `Γ` is the union of `ι N` and
`ι N · ε` for an involution `ε ∉ ι N` which normalises `ι N`, acting on `N` as the involution `σ`.
Over the complex numbers:

* a crossed homomorphism of `Γ` is cohomologous to one vanishing at `ε`
  (`exists_normalized`), and such a crossed homomorphism restricts to a `σ`-invariant crossed
  homomorphism of `N` (`reflect_restrict`);
* conversely a `σ`-invariant crossed homomorphism of `N` extends to a crossed homomorphism of `Γ`
  vanishing at `ε` (`exists_extension`).

Consequently a left nondegeneracy statement for the `σ`-invariant parabolic crossed homomorphisms of
`N` (a pairing odd under `ε`) gives the same statement for all parabolic crossed homomorphisms of
`Γ` (`cochainNondegenerate_of_nd`): the cup pairing of `Γ`-classes is the cup pairing of their
restrictions to `N`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

open TripleModel LinearDuality CocycleBridge EpsilonSplit

/-- The index-two situation: `ι` is injective, `ε` is an involution outside the image of `ι`,
`Γ = ι N ∪ ι N ε`, and conjugation by `ε` restricts to the involution `σ` of `N`. -/
structure IndexTwo {Γ N : Type} [Group Γ] [Group N] (ι : N →* Γ) (ε : Γ) (σ : N →* N) : Prop where
  inj : Function.Injective ι
  sq : ε * ε = 1
  conj : ∀ n, ι (σ n) = ε * ι n * ε
  cover : ∀ g : Γ, (∃ n, ι n = g) ∨ ∃ n, ι n * ε = g
  not_mem : ∀ n, ι n ≠ ε

section Basic

variable {Γ N : Type} [Group Γ] [Group N] {ι : N →* Γ} {ε : Γ} {σ : N →* N}

/-- Conjugation by `ε` on `ι N`: `ε ι(n) = ι(σ n) ε`. -/
theorem IndexTwo.comm (H : IndexTwo ι ε σ) (n : N) : ε * ι n = ι (σ n) * ε := by
  calc ε * ι n = ε * ι n * (ε * ε) := by rw [H.sq, mul_one]
    _ = ι (σ n) * ε := by
      rw [H.conj n]
      simp only [mul_assoc]

/-- Elements of the coset `ι N ε` are not in the image of `ι`. -/
theorem IndexTwo.not_mul_mem (H : IndexTwo ι ε σ) (n m : N) : ι n * ε ≠ ι m := by
  intro h
  apply H.not_mem (n⁻¹ * m)
  rw [map_mul, map_inv, ← h, inv_mul_cancel_left]

/-- Every element of `Γ` is `ι n` or `ι n * ε`. -/
theorem IndexTwo.exists_proj (H : IndexTwo ι ε σ) (g : Γ) : ∃ n : N, ι n = g ∨ ι n * ε = g := by
  rcases H.cover g with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, Or.inl hn⟩
  · exact ⟨n, Or.inr hn⟩

/-- A choice of `n` with `g = ι n` or `g = ι n * ε`. -/
def IndexTwo.proj (H : IndexTwo ι ε σ) (g : Γ) : N :=
  Classical.choose (H.exists_proj g)

/-- The projection recovers `n` from `ι n`. -/
theorem IndexTwo.proj_ι (H : IndexTwo ι ε σ) (n : N) : H.proj (ι n) = n := by
  have h := Classical.choose_spec (H.exists_proj (ι n))
  rcases h with h | h
  · exact H.inj h
  · exact absurd h (H.not_mul_mem _ n)

/-- The projection recovers `n` from `ι n * ε`. -/
theorem IndexTwo.proj_ιε (H : IndexTwo ι ε σ) (n : N) : H.proj (ι n * ε) = n := by
  have h := Classical.choose_spec (H.exists_proj (ι n * ε))
  rcases h with h | h
  · exact absurd h.symm (H.not_mul_mem n _)
  · exact H.inj (mul_right_cancel h)

end Basic

section Cocycles

variable {Γ N V : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] {ι : N →* Γ} {ε : Γ}
  {σ : N →* N} {ρ : Representation ℂ Γ V}

/-- The involution `ε` acts as an involution on any representation. -/
theorem rep_sq (H : IndexTwo ι ε σ) (x : V) : ρ ε (ρ ε x) = x := by
  rw [← rep_mul_apply, H.sq, map_one, Module.End.one_apply]

/-- A crossed homomorphism of `Γ` is cohomologous to one vanishing at `ε`. -/
theorem exists_normalized (H : IndexTwo ι ε σ) {Z : Γ → V} (hZ : IsCocycle ρ Z) :
    ∃ u : V, Z ε = ρ ε u - u := by
  have h := hZ ε ε
  rw [H.sq, hZ.map_one] at h
  have h2 : ρ ε (Z ε) = -Z ε := by
    linear_combination (norm := module) (-1 : ℂ) • h
  refine ⟨(-(1 / 2 : ℂ)) • Z ε, ?_⟩
  rw [map_smul, h2]
  module

/-- A crossed homomorphism of `Γ` vanishing at `ε` restricts to a `σ`-invariant crossed
homomorphism of `N`. -/
theorem reflect_restrict (H : IndexTwo ι ε σ) {Z : Γ → V} (hZ : IsCocycle ρ Z) (h0 : Z ε = 0) :
    reflect σ (ρ ε) (fun n => Z (ι n)) = fun n => Z (ι n) := by
  funext n
  show ρ ε (Z (ι (σ n))) = Z (ι n)
  have a1 := hZ ε (ι n * ε)
  have a2 := hZ (ι n) ε
  rw [← mul_assoc] at a1
  have e1 : Z (ε * ι n * ε) = ρ ε (Z (ι n)) := by
    rw [a1, h0, zero_add, a2, h0, map_zero, add_zero]
  rw [H.conj n, e1, rep_sq (ρ := ρ) H]

/-- A `σ`-invariant crossed homomorphism of `N` extends to a crossed homomorphism of `Γ`
vanishing at `ε`. -/
theorem exists_extension (H : IndexTwo ι ε σ) {z : N → V} (hz : IsCocycle (ρ.comp ι) z)
    (hinv : reflect σ (ρ ε) z = z) :
    ∃ Z : Γ → V, IsCocycle ρ Z ∧ Z ε = 0 ∧ ∀ n, Z (ι n) = z n := by
  have hz' : ∀ n, z (σ n) = ρ ε (z n) := by
    intro n
    have h : ρ ε (z (σ n)) = z n := congrFun hinv n
    calc z (σ n) = ρ ε (ρ ε (z (σ n))) := (rep_sq (ρ := ρ) H _).symm
      _ = ρ ε (z n) := by rw [h]
  have hcases : ∀ g : Γ, (∃ n, g = ι n) ∨ ∃ n, g = ι n * ε := by
    intro g
    rcases H.cover g with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ⟨n, hn.symm⟩
    · exact Or.inr ⟨n, hn.symm⟩
  have step : ∀ n m : N, z (n * σ m) = z n + ρ (ι n * ε) (z m) := by
    intro n m
    calc z (n * σ m) = z n + ρ (ι n) (z (σ m)) := hz n (σ m)
      _ = z n + ρ (ι n) (ρ ε (z m)) := by rw [hz' m]
      _ = z n + ρ (ι n * ε) (z m) := by rw [map_mul, Module.End.mul_apply]
  refine ⟨fun g => z (H.proj g), ?_, ?_, ?_⟩
  · intro g h
    rcases hcases g with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> rcases hcases h with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · show z (H.proj (ι n * ι m)) = z (H.proj (ι n)) + ρ (ι n) (z (H.proj (ι m)))
      rw [← map_mul ι n m, H.proj_ι (n * m), H.proj_ι n, H.proj_ι m]
      exact hz n m
    · show z (H.proj (ι n * (ι m * ε))) =
        z (H.proj (ι n)) + ρ (ι n) (z (H.proj (ι m * ε)))
      rw [← mul_assoc, ← map_mul ι n m, H.proj_ιε (n * m), H.proj_ι n, H.proj_ιε m]
      exact hz n m
    · show z (H.proj (ι n * ε * ι m)) =
        z (H.proj (ι n * ε)) + ρ (ι n * ε) (z (H.proj (ι m)))
      have e : ι n * ε * ι m = ι (n * σ m) * ε := by
        rw [mul_assoc, H.comm m, ← mul_assoc, ← map_mul ι n (σ m)]
      rw [e, H.proj_ιε (n * σ m), H.proj_ιε n, H.proj_ι m]
      exact step n m
    · show z (H.proj (ι n * ε * (ι m * ε))) =
        z (H.proj (ι n * ε)) + ρ (ι n * ε) (z (H.proj (ι m * ε)))
      have e : ι n * ε * (ι m * ε) = ι (n * σ m) := by
        calc ι n * ε * (ι m * ε) = ι n * (ε * ι m) * ε := by simp only [mul_assoc]
          _ = ι n * (ι (σ m) * ε) * ε := by rw [H.comm m]
          _ = ι n * ι (σ m) * (ε * ε) := by simp only [mul_assoc]
          _ = ι (n * σ m) := by rw [H.sq, mul_one, ← map_mul ι n (σ m)]
      rw [e, H.proj_ι (n * σ m), H.proj_ιε n, H.proj_ιε m]
      exact step n m
  · have hp : H.proj ε = 1 := by
      have h := H.proj_ιε 1
      rwa [map_one, one_mul] at h
    show z (H.proj ε) = 0
    rw [hp]
    exact hz.map_one
  · intro n
    show z (H.proj (ι n)) = z n
    rw [H.proj_ι n]

end Cocycles

section Descent

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- **Left nondegeneracy for the `σ`-invariant parabolic crossed homomorphisms of `N`**, the
hypothesis transferred to `Γ`. -/
def NLevelND (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N) (ε : Γ) (σ : N →* N) : Prop :=
  ∀ z : N → V, IsCocycle (ρ.comp ι) z → ∀ v : V × V × V, IsPrimitive (ρ.comp ι) a g₂ z v →
    reflect σ (ρ ε) z = z →
    (∀ (z' : N → W) (v' : W × W × W), IsCocycle (ρ'.comp ι) z' →
      IsPrimitive (ρ'.comp ι) a g₂ z' v' → reflect σ (ρ' ε) z' = z' →
      cupFormula B (ρ'.comp ι) a g₂ z z' v = 0) →
    ∃ u : V, ρ ε u = u ∧ ∀ n, z n = ρ (ι n) u - u

/-- **Left nondegeneracy on `Γ`** from left nondegeneracy of the `σ`-invariant parabolic crossed
homomorphisms of the index-two subgroup `N`. -/
theorem cochainNondegenerate_of_nd {ι : N →* Γ} {ε : Γ} {σ : N →* N} (H : IndexTwo ι ε σ)
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w)
    (hnd : NLevelND ι ρ ρ' B a g₂ ε σ) : CochainNondegenerate ι ρ ρ' B a g₂ := by
  intro Z hZm hzero
  obtain ⟨hZ, v, hv⟩ := mem_parabolicCochains.mp hZm
  have hinvc : ∀ (n : N) (x : V) (y : W), B ((ρ.comp ι) n x) ((ρ'.comp ι) n y) = B x y := hinv
  obtain ⟨u₀, hu₀⟩ := exists_normalized H hZ
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Γ → V, Z₀ = fun g => Z g - (ρ g u₀ - u₀) := ⟨_, rfl⟩
  have hc₀ : IsCocycle ρ Z₀ := by
    rw [hZ₀]
    exact isCocycle_sub hZ (isCocycle_boundary ρ u₀)
  have h0 : Z₀ ε = 0 := by
    rw [hZ₀]
    show Z ε - (ρ ε u₀ - u₀) = 0
    rw [hu₀, sub_self]
  have hp₀ : IsPrimitive (ρ.comp ι) a g₂ (fun n => Z₀ (ι n)) (v - (u₀, u₀, u₀)) := by
    rw [hZ₀]
    exact isPrimitive_sub hv (isPrimitive_boundary (ρ.comp ι) a g₂ u₀)
  have hz : IsCocycle (ρ.comp ι) (fun n => Z₀ (ι n)) := isCocycle_comp hc₀ ι
  have hinvz : reflect σ (ρ ε) (fun n => Z₀ (ι n)) = fun n => Z₀ (ι n) :=
    reflect_restrict H hc₀ h0
  have zero' : ∀ (z' : N → W) (v' : W × W × W), IsCocycle (ρ'.comp ι) z' →
      IsPrimitive (ρ'.comp ι) a g₂ z' v' → reflect σ (ρ' ε) z' = z' →
      cupFormula B (ρ'.comp ι) a g₂ (fun n => Z₀ (ι n)) z' (v - (u₀, u₀, u₀)) = 0 := by
    intro z' v' hz' hv' hinv'
    obtain ⟨Z', hZ', _, hres⟩ := exists_extension H hz' hinv'
    have hfun : (fun n => Z' (ι n)) = z' := funext hres
    have hv'' : IsPrimitive (ρ'.comp ι) a g₂ (fun n => Z' (ι n)) v' := by
      rw [hfun]
      exact hv'
    have h1 := hzero Z' (mem_parabolicCochains.mpr ⟨hZ', v', hv''⟩)
    rw [pairFun_eq ι ρ ρ' B a g₂ hinv hZ hv hv''] at h1
    rw [cupFormula_eq_tripleForm hinvc hz hp₀ hv', map_sub, LinearMap.sub_apply,
      tripleForm_boundary_left hz' hv' u₀, sub_zero]
    exact h1
  obtain ⟨u, huε, hu⟩ := hnd (fun n => Z₀ (ι n)) hz (v - (u₀, u₀, u₀)) hp₀ hinvz zero'
  have key : ∀ g, Z₀ g = ρ g u - u := by
    intro g
    rcases H.cover g with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact hu n
    · have e := hc₀ (ι n) ε
      rw [h0, map_zero, add_zero] at e
      have hn : Z₀ (ι n) = ρ (ι n) u - u := hu n
      rw [e, hn, map_mul, Module.End.mul_apply, huε]
  refine ⟨u + u₀, fun g => ?_⟩
  have h : Z g - (ρ g u₀ - u₀) = ρ g u - u := by
    have h' := key g
    rw [hZ₀] at h'
    exact h'
  rw [map_add]
  linear_combination (norm := module) h

end Descent

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
