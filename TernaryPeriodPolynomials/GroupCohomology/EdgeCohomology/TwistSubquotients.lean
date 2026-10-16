module

public import TernaryPeriodPolynomials.GroupCohomology.EdgeCohomology.SemidirectSequence

@[expose] public section


/-!
# The two subquotients of `H¹(N ⋊ ℤ, A)` and the action of a twist

Formalized by Claude Sonnet 5.5.

On top of `SemidirectSequence` (`0 → H¹(ℤ, A^N) → H¹(N ⋊ ℤ, A) → H¹(N, A)^ℤ → 0`), a `Twist` is an automorphism `σ = ψ ⋊ (q ↦ q^s)`,
`s = ±1`, of `N ⋊ ℤ` together with a linear map `T` on the coefficients intertwining `σ` with the identity (in the application:
conjugation by `diag(η₁, η₂, 1)`).  It acts on `H¹(N ⋊ ℤ, A)` (`Twist.twistG`) and on `H¹(N, A)` (`Twist.twistN`), compatibly with the
restriction (`Twist.resp_twist`).  The main results, `edge_basis` and `Twist.twist_right` (with `Twist.twist_left`), say: if `w₀ ∈ A^N` spans the `ℤ`-coinvariants of `A^N`
(fixed by `T`) and `v₀` spans the `ℤ`-invariants of `H¹(N, A)` (an eigenvector of the twist), then `H¹(N ⋊ ℤ, A)` has a basis
`x₁, x₂`, `x₁` spans `ker (resp) = range (infl)` and the twist acts on it by `s` (`Twist.twist_left`), `resp x₂ = v₀`, and the twist acts
on `x₂` by the eigenvalue of `v₀` modulo `x₁`.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EdgeCohomology

open CategoryTheory groupCohomology TernaryPoly.LowDegreeHochschildSerre

section Twist

variable {N : Type} [Group N] (φ : Multiplicative ℤ →* MulAut N) (A : Rep.{0} ℚ (G φ))

/-- An automorphism datum of `N ⋊ ℤ` and of its coefficients: `ψ` on `N`, `q ↦ q^s` on `ℤ` (`s = ±1`), and a linear map
`T` on `A` intertwining `σ = ψ ⋊ (·^s)` with the identity. -/
structure Twist where
  ψ : N →* N
  s : ℤ
  hs : s = 1 ∨ s = -1
  hψ : Function.Surjective ψ
  compat : ∀ q : Multiplicative ℤ,
    ψ.comp (φ q).toMonoidHom = (φ (zpowGroupHom s q)).toMonoidHom.comp ψ
  T : A →ₗ[ℚ] A
  hT : ∀ (g : G φ) (v : A),
    T (A.ρ (SemidirectProduct.map ψ (zpowGroupHom s) compat g) v) = A.ρ g (T v)

variable {φ A}

/-- The automorphism of `N ⋊ ℤ`. -/
def Twist.σ (tw : Twist φ A) : G φ →* G φ :=
  SemidirectProduct.map tw.ψ (zpowGroupHom tw.s) tw.compat

/-- The coefficient morphism of the automorphism. -/
def Twist.Tm (tw : Twist φ A) : Rep.res tw.σ A ⟶ A :=
  Rep.ofHom ⟨tw.T, fun g => LinearMap.ext (tw.hT g)⟩

/-- The action on `H¹(G, A)`. -/
def Twist.twistG (tw : Twist φ A) : groupCohomology A 1 ⟶ groupCohomology A 1 :=
  groupCohomology.map tw.σ tw.Tm 1

/-- The coefficient morphism on the radical. -/
def Twist.TN (tw : Twist φ A) : Rep.res tw.ψ (radicalRep φ A) ⟶ radicalRep φ A :=
  Rep.ofHom ⟨tw.T, fun n => LinearMap.ext fun v => by
    have h := tw.hT (nIn φ n) v
    rw [SemidirectProduct.map_inl] at h
    exact h⟩

/-- The action on `H¹(N, A)`. -/
def Twist.twistN (tw : Twist φ A) : groupCohomology (radicalRep φ A) 1 ⟶ groupCohomology (radicalRep φ A) 1 :=
  groupCohomology.map tw.ψ tw.TN 1

theorem Twist.restrictOne_map (tw : Twist φ A) (c : cocycles₁ A) :
    restrictOne φ A (mapCocycles₁ tw.σ tw.Tm c) = mapCocycles₁ tw.ψ tw.TN (restrictOne φ A c) := by
  apply Subtype.ext
  funext n
  change tw.T (c (tw.σ (nIn φ n))) = tw.T (c (nIn φ (tw.ψ n)))
  unfold Twist.σ
  rw [SemidirectProduct.map_inl]

theorem Twist.resp_twist (tw : Twist φ A) (x : groupCohomology A 1) :
    resp φ A (tw.twistG x) = tw.twistN (resp φ A x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [Twist.twistG, H1π_comp_map_apply, resp_H1π, resp_H1π, Twist.twistN, H1π_comp_map_apply,
    tw.restrictOne_map]

end Twist

section Left

variable {N : Type} [Group N] (φ : Multiplicative ℤ →* MulAut N) (A : Rep.{0} ℚ (G φ))

/-- A one-cocycle vanishing on the radical and at the generator of `ℤ` is zero. -/
theorem cocycle_zero_of_generator (c : cocycles₁ A) (hN : ∀ n : N, c (nIn φ n) = 0)
    (ht : (c (qIn φ (Multiplicative.ofAdd 1)) : A) = 0) : c = 0 := by
  have hQ : mapCocycles₁ (qIn φ) (𝟙 (Rep.res (qIn φ) A)) c = 0 := by
    apply cocycle_ext_cyclic (Rep.res (qIn φ) A)
    exact ht
  apply Subtype.ext
  funext g
  have h1 := one_value_quotient φ A c hN g
  have h2 := congrFun (congrArg Subtype.val hQ) g.right
  exact h1.trans h2

theorem exists_left_cocycle (w₀ : A) (hw₀ : w₀ ∈ (radicalRep φ A).ρ.invariants) :
    ∃ c₁ : cocycles₁ A, (∀ n : N, c₁ (nIn φ n) = 0) ∧ (c₁ (qIn φ (Multiplicative.ofAdd 1)) : A) = w₀ := by
  obtain ⟨c, hc, ht⟩ := exists_extension φ A 0 w₀ (fun n => by
    have h := (Representation.mem_invariants _ _).mp hw₀ n
    change A.ρ (nIn φ n) w₀ = w₀ at h
    change A.ρ (qIn φ (Multiplicative.ofAdd 1)) 0 - 0 = _
    rw [h]; simp)
  exact ⟨c, hc, ht⟩

theorem edge_left (w₀ : A)
    (hspan : ∀ v ∈ (radicalRep φ A).ρ.invariants, ∃ (c : ℚ) (u : A), u ∈ (radicalRep φ A).ρ.invariants ∧
      v = c • w₀ + (A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u))
    (hnz : ∀ u ∈ (radicalRep φ A).ρ.invariants, A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u ≠ w₀)
    (c₁ : cocycles₁ A) (hc₁N : ∀ n : N, c₁ (nIn φ n) = 0)
    (hc₁t : (c₁ (qIn φ (Multiplicative.ofAdd 1)) : A) = w₀) :
    H1π A c₁ ≠ 0 ∧ LinearMap.ker (resp φ A).hom = Submodule.span ℚ {H1π A c₁} := by
  constructor
  · intro h0
    obtain ⟨u, hu⟩ := (H1π_eq_zero_iff _).mp h0
    have hinv : u ∈ (radicalRep φ A).ρ.invariants := by
      rw [Representation.mem_invariants]
      intro n
      have h1 := congrFun hu (nIn φ n)
      change A.ρ (nIn φ n) u - u = c₁ (nIn φ n) at h1
      rw [hc₁N] at h1
      exact sub_eq_zero.mp h1
    have h1 := congrFun hu (qIn φ (Multiplicative.ofAdd 1))
    change A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u = c₁ (qIn φ (Multiplicative.ofAdd 1)) at h1
    exact hnz u hinv (h1.trans hc₁t)
  · apply le_antisymm
    · intro x hx
      induction x using H1_induction_on with | h c => ?_
      have h0 : H1π (radicalRep φ A) (restrictOne φ A c) = 0 := by
        rw [← resp_H1π]; exact hx
      obtain ⟨u₀, hu₀⟩ := (H1π_eq_zero_iff _).mp h0
      let c' : cocycles₁ A := c - ⟨d₀₁ A u₀, d₀₁_apply_mem_cocycles₁ (A := A) u₀⟩
      have hc' : ∀ n : N, c' (nIn φ n) = 0 := by
        intro n
        have h1 := congrFun hu₀ n
        change A.ρ (nIn φ n) u₀ - u₀ = c (nIn φ n) at h1
        change c (nIn φ n) - (A.ρ (nIn φ n) u₀ - u₀) = 0
        rw [h1, sub_self]
      have hv := one_value_invariants φ A c' hc' (Multiplicative.ofAdd 1)
      obtain ⟨k, u, hu, hk⟩ := hspan _ hv
      let δu : cocycles₁ A := ⟨d₀₁ A u, d₀₁_apply_mem_cocycles₁ (A := A) u⟩
      have hδN : ∀ n : N, δu (nIn φ n) = 0 := by
        intro n
        have h := (Representation.mem_invariants _ _).mp hu n
        change A.ρ (nIn φ n) u - u = 0
        change A.ρ (nIn φ n) u = u at h
        rw [h, sub_self]
      have hzero : c' - k • c₁ - δu = 0 := by
        apply cocycle_zero_of_generator φ A
        · intro n
          change c' (nIn φ n) - k • c₁ (nIn φ n) - δu (nIn φ n) = 0
          rw [hc', hc₁N, hδN]; simp
        · change (c' (qIn φ (Multiplicative.ofAdd 1)) : A) - k • (c₁ (qIn φ (Multiplicative.ofAdd 1)) : A) -
            (A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u) = 0
          rw [hc₁t, hk]
          abel
      have hc'eq : c' = k • c₁ + δu := by
        rw [← sub_eq_zero, sub_add_eq_sub_sub]; exact hzero
      have hcc' : H1π A c' = H1π A c := by
        rw [H1π_eq_iff]
        refine ⟨-u₀, ?_⟩
        funext g
        change (d₀₁ A (-u₀)) g = (c g - (d₀₁ A u₀) g) - c g
        rw [map_neg]
        change -(d₀₁ A u₀ g) = _
        abel
      rw [Submodule.mem_span_singleton]
      refine ⟨k, ?_⟩
      rw [← hcc', hc'eq, map_add, map_smul]
      have : (H1π A).hom δu = 0 := (H1π_eq_zero_iff _).mpr ⟨u, rfl⟩
      rw [this, add_zero]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      change resp φ A (H1π A c₁) = 0
      rw [resp_H1π]
      have : restrictOne φ A c₁ = 0 := by
        apply Subtype.ext
        funext n
        exact hc₁N n
      rw [this]
      exact map_zero (H1π (radicalRep φ A)).hom


variable {φ A}

theorem Twist.twist_left (tw : Twist φ A) (w₀ : A) (hw₀ : w₀ ∈ (radicalRep φ A).ρ.invariants)
    (hTw : tw.T w₀ = w₀) (c₁ : cocycles₁ A) (hc₁N : ∀ n : N, c₁ (nIn φ n) = 0)
    (hc₁t : (c₁ (qIn φ (Multiplicative.ofAdd 1)) : A) = w₀) :
    tw.twistG (H1π A c₁) = (tw.s : ℚ) • H1π A c₁ := by
  set t : Multiplicative ℤ := Multiplicative.ofAdd 1 with ht
  let c₁' : cocycles₁ A := mapCocycles₁ tw.σ tw.Tm c₁
  have hc₁'N : ∀ n : N, c₁' (nIn φ n) = 0 := by
    intro n
    change tw.T (c₁ (tw.σ (nIn φ n))) = 0
    unfold Twist.σ
    rw [SemidirectProduct.map_inl, hc₁N, map_zero]
  have hσt : tw.σ (qIn φ t) = qIn φ (t ^ tw.s) := by
    unfold Twist.σ
    rw [SemidirectProduct.map_inr]; rfl
  have hinvt : ∀ u : A, u ∈ (radicalRep φ A).ρ.invariants → ∀ n : N, A.ρ (nIn φ n) u = u := fun u hu n =>
    (Representation.mem_invariants _ _).mp hu n
  have hext : ∀ (e : cocycles₁ A) (u : A), u ∈ (radicalRep φ A).ρ.invariants →
      (∀ n : N, e (nIn φ n) = 0) → (e (qIn φ t) : A) = A.ρ (qIn φ t) u - u →
      ∀ g : G φ, (e g : A) = A.ρ g u - u := by
    intro e u hu hN ht g
    let δu : cocycles₁ A := ⟨d₀₁ A u, d₀₁_apply_mem_cocycles₁ (A := A) u⟩
    have h0 : e - δu = 0 := by
      apply cocycle_zero_of_generator φ A
      · intro n
        change e (nIn φ n) - (A.ρ (nIn φ n) u - u) = 0
        rw [hN, hinvt u hu n, sub_self, sub_zero]
      · change (e (qIn φ t) : A) - (A.ρ (qIn φ t) u - u) = 0
        rw [ht, sub_self]
    have h1 := congrFun (congrArg Subtype.val h0) g
    exact sub_eq_zero.mp h1
  let e : cocycles₁ A := c₁' - (tw.s : ℚ) • c₁
  have heN : ∀ n : N, e (nIn φ n) = 0 := by
    intro n
    change c₁' (nIn φ n) - (tw.s : ℚ) • c₁ (nIn φ n) = 0
    rw [hc₁'N, hc₁N]; simp
  have hc₁'t : (c₁' (qIn φ t) : A) = tw.T (c₁ (qIn φ (t ^ tw.s))) := by
    change tw.T (c₁ (tw.σ (qIn φ t))) = _
    rw [hσt]
  have hcl : ∃ u ∈ (radicalRep φ A).ρ.invariants, ∀ g : G φ, (e g : A) = A.ρ g u - u := by
    rcases tw.hs with h | h
    · refine ⟨0, Submodule.zero_mem _, hext e 0 (Submodule.zero_mem _) heN ?_⟩
      change (c₁' (qIn φ t) : A) - (tw.s : ℚ) • (c₁ (qIn φ t) : A) = A.ρ (qIn φ t) 0 - 0
      rw [hc₁'t, h, zpow_one, hc₁t, hTw]; simp
    · refine ⟨-w₀, Submodule.neg_mem _ hw₀, hext e (-w₀) (Submodule.neg_mem _ hw₀) heN ?_⟩
      change (c₁' (qIn φ t) : A) - (tw.s : ℚ) • (c₁ (qIn φ t) : A) = A.ρ (qIn φ t) (-w₀) - -w₀
      have hinvc : (c₁ (qIn φ t⁻¹) : A) = - A.ρ (qIn φ t⁻¹) w₀ := by
        have h1 := (mem_cocycles₁_iff _).mp c₁.property (qIn φ t⁻¹) (qIn φ t)
        have h0 : (c₁ (qIn φ t⁻¹ * qIn φ t) : A) = 0 := by
          rw [← map_mul, inv_mul_cancel, map_one]
          exact cocycles₁_map_one c₁
        have h2 : A.ρ (qIn φ t⁻¹) (c₁ (qIn φ t) : A) + (c₁ (qIn φ t⁻¹) : A) = 0 := h1.symm.trans h0
        rw [hc₁t] at h2
        exact eq_neg_of_add_eq_zero_right h2
      have hTρ : tw.T (A.ρ (qIn φ t⁻¹) w₀) = A.ρ (qIn φ t) w₀ := by
        have h2 := tw.hT (qIn φ t) w₀
        rw [hTw] at h2
        have hs' : SemidirectProduct.map tw.ψ (zpowGroupHom tw.s) tw.compat (qIn φ t) = qIn φ t⁻¹ := by
          rw [SemidirectProduct.map_inr, h]
          rfl
        rw [hs'] at h2
        exact h2
      rw [hc₁'t, h, zpow_neg_one, hinvc, map_neg, hTρ, hc₁t, map_neg]
      simp
  obtain ⟨u, hu, hcu⟩ := hcl
  have hclass : H1π A e = 0 := (H1π_eq_zero_iff _).mpr ⟨u, by funext g; exact (hcu g).symm⟩
  have hlin : H1π A e = H1π A c₁' - (tw.s : ℚ) • H1π A c₁ := by
    change (H1π A).hom (c₁' - (tw.s : ℚ) • c₁) = _
    rw [map_sub, map_smul]
  rw [hlin] at hclass
  have : tw.twistG (H1π A c₁) = H1π A c₁' := by
    rw [Twist.twistG, H1π_comp_map_apply]
  rw [this]
  exact sub_eq_zero.mp hclass

/-- **The basis of `H¹(N ⋊ ℤ, A)` adapted to the inflation-restriction sequence.** Let `w₀ ∈ A^N` span the `ℤ`-coinvariants of `A^N`
(every invariant is a multiple of `w₀` modulo `(t-1)A^N`, and `w₀` itself is not in `(t-1)A^N`), and let `v₀` span the
`ℤ`-invariants of `H¹(N, A)`.  Then there is a cocycle `c₁` vanishing on `N` with `c₁(t) = w₀` and a class `x₂` restricting to `v₀`, such
that `x₁ = [c₁]` and `x₂` form a basis of `H¹(G, A)`, with `x₁` spanning `ker (resp) = range (infl)`, and `resp` has image `ℚ v₀`. -/
theorem edge_basis (w₀ : A) (hw₀ : w₀ ∈ (radicalRep φ A).ρ.invariants)
    (hspan : ∀ v ∈ (radicalRep φ A).ρ.invariants, ∃ (c : ℚ) (u : A), u ∈ (radicalRep φ A).ρ.invariants ∧
      v = c • w₀ + (A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u))
    (hnz : ∀ u ∈ (radicalRep φ A).ρ.invariants, A.ρ (qIn φ (Multiplicative.ofAdd 1)) u - u ≠ w₀)
    (v₀ : groupCohomology (radicalRep φ A) 1) (hv₀ : v₀ ≠ 0)
    (hinv : ∀ x : groupCohomology (radicalRep φ A) 1,
      (cohomologyRep φ A 1).ρ (Multiplicative.ofAdd 1) x = x ↔ ∃ c : ℚ, x = c • v₀) :
    ∃ (c₁ : cocycles₁ A) (x₂ : groupCohomology A 1),
      (∀ n : N, c₁ (nIn φ n) = 0) ∧ (c₁ (qIn φ (Multiplicative.ofAdd 1)) : A) = w₀ ∧
      H1π A c₁ ≠ 0 ∧
      Function.Injective (infl φ A).hom ∧
      LinearMap.range (infl φ A).hom = Submodule.span ℚ {H1π A c₁} ∧
      LinearMap.ker (resp φ A).hom = Submodule.span ℚ {H1π A c₁} ∧
      LinearMap.range (resp φ A).hom = Submodule.span ℚ {v₀} ∧
      resp φ A x₂ = v₀ ∧
      (∀ x : groupCohomology A 1, ∃ a b : ℚ, x = a • H1π A c₁ + b • x₂) ∧
      (∀ a b : ℚ, a • H1π A c₁ + b • x₂ = 0 → a = 0 ∧ b = 0) := by
  obtain ⟨c₁, hc₁N, hc₁t⟩ := exists_left_cocycle φ A w₀ hw₀
  obtain ⟨hx₁, hker⟩ := edge_left φ A w₀ hspan hnz c₁ hc₁N hc₁t
  have hv₀inv : (cohomologyRep φ A 1).ρ (Multiplicative.ofAdd 1) v₀ = v₀ := (hinv v₀).mpr ⟨1, (one_smul _ _).symm⟩
  have hrange : LinearMap.range (resp φ A).hom = Submodule.span ℚ {v₀} := by
    ext x
    rw [mem_range_resp_iff, hinv, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  obtain ⟨x₂, hx₂⟩ : v₀ ∈ LinearMap.range (resp φ A).hom := by
    rw [hrange]; exact Submodule.mem_span_singleton_self _
  have hres₁ : resp φ A (H1π A c₁) = 0 := by
    have : H1π A c₁ ∈ LinearMap.ker (resp φ A).hom := by
      rw [hker]; exact Submodule.mem_span_singleton_self _
    exact this
  refine ⟨c₁, x₂, hc₁N, hc₁t, hx₁, infl_injective φ A, ?_, hker, hrange, hx₂, ?_, ?_⟩
  · rw [← ker_resp_eq_range_infl, hker]
  · intro x
    have hx : resp φ A x ∈ LinearMap.range (resp φ A).hom := ⟨x, rfl⟩
    rw [hrange, Submodule.mem_span_singleton] at hx
    obtain ⟨b, hb⟩ := hx
    have hk : x - b • x₂ ∈ LinearMap.ker (resp φ A).hom := by
      change resp φ A (x - b • x₂) = 0
      rw [map_sub, map_smul, hx₂, hb, sub_self]
    rw [hker, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    exact ⟨a, b, by rw [ha]; abel⟩
  · intro a b hab
    have h1 : resp φ A (a • H1π A c₁ + b • x₂) = 0 := by rw [hab]; exact map_zero _
    rw [map_add, map_smul, map_smul, hres₁, hx₂, smul_zero, zero_add] at h1
    have hb : b = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hv₀
    subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hx₁, rfl⟩

/-- The twist acts on the second basis class by the eigenvalue of `v₀`, modulo the first. -/
theorem Twist.twist_right (tw : Twist φ A) (x₁ x₂ : groupCohomology A 1) (v₀ : groupCohomology (radicalRep φ A) 1)
    (hker : LinearMap.ker (resp φ A).hom = Submodule.span ℚ {x₁}) (hx₂ : resp φ A x₂ = v₀)
    (χ : ℚ) (hχ : tw.twistN v₀ = χ • v₀) : ∃ μ : ℚ, tw.twistG x₂ = χ • x₂ + μ • x₁ := by
  have hk : tw.twistG x₂ - χ • x₂ ∈ LinearMap.ker (resp φ A).hom := by
    change resp φ A (tw.twistG x₂ - χ • x₂) = 0
    rw [map_sub, map_smul, tw.resp_twist, hx₂, hχ, sub_self]
  rw [hker, Submodule.mem_span_singleton] at hk
  obtain ⟨μ, hμ⟩ := hk
  exact ⟨μ, by rw [hμ]; abel⟩

end Left

end TernaryPeriodPolynomials.Argument.EdgeCohomology
