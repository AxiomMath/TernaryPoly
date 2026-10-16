module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.Schur

@[expose] public section


/-!
# Hecke operators on fixed vectors of a cuspidal representation

For a subgroup `K` of `GL₂(𝔸)` and a finite double coset `K g K = ⊔ rᵢ K`, the operator
`T v = Σ π(rᵢ) v` preserves the `K`-fixed vectors of a `CuspidalRepresentation`. These are the
local Hecke operators whose eigenvalues define the Hecke character of the inducing data.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RepresentationTheory

/-- A finite double coset `K g K` with a complete set of left-coset representatives. -/
structure DoubleCoset {G : Type*} [Group G] (K : Subgroup G) where
  g : G
  reps : Finset G
  inDouble : ∀ r ∈ reps, ∃ a b : K, r = a.val * g * b.val
  complete : ∀ a b : K, ∃ r ∈ reps, r⁻¹ * (a.val * g * b.val) ∈ K
  disjoint : ∀ r ∈ reps, ∀ t ∈ reps, r⁻¹ * t ∈ K → r = t

/-- Left multiplication by `k ∈ K` permutes the coset representatives. -/
theorem DoubleCoset.exists_rep {G : Type*} [Group G] {K : Subgroup G} (T : DoubleCoset K)
    (k : K) (r : G) (hr : r ∈ T.reps) : ∃ r' ∈ T.reps, r'⁻¹ * (k.val * r) ∈ K := by
  obtain ⟨a, b, rfl⟩ := T.inDouble r hr
  obtain ⟨r', hr', hmem⟩ := T.complete (k * a) b
  refine ⟨r', hr', ?_⟩
  simpa [mul_assoc] using hmem

/-- The `K`-fixed vectors. -/
def fixedVectors (σ : CuspidalRepresentation) (K : Subgroup BinaryAdelicGL) : Submodule ℂ σ.H where
  carrier := {v | ∀ k : K, σ.π k.val v = v}
  add_mem' := by
    intro v w hv hw k
    simp [hv k, hw k]
  zero_mem' := by intro k; simp
  smul_mem' := by
    intro c v hv k
    simp [hv k]

theorem fixedVectors_isClosed (σ : CuspidalRepresentation) (K : Subgroup BinaryAdelicGL) :
    IsClosed (fixedVectors σ K : Set σ.H) := by
  have : (fixedVectors σ K : Set σ.H) = ⋂ k : K, {v | cuspOperator σ k.val v = v} := by
    ext v; simp [fixedVectors, cuspOperator_apply]
  rw [this]
  exact isClosed_iInter fun k => isClosed_eq (cuspOperator σ k.val).continuous continuous_id

/-- The Hecke operator `v ↦ Σ π(rᵢ) v`. -/
def heckeOperator (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL} (T : DoubleCoset K) :
    σ.H →L[ℂ] σ.H :=
  ∑ r ∈ T.reps, cuspOperator σ r

theorem heckeOperator_apply (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL}
    (T : DoubleCoset K) (v : σ.H) : heckeOperator σ T v = ∑ r ∈ T.reps, σ.π r v := by
  simp [heckeOperator, cuspOperator_apply]

/-- Hecke operators preserve the `K`-fixed vectors. -/
theorem heckeOperator_mem_fixed (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL}
    (T : DoubleCoset K) {v : σ.H} (hv : v ∈ fixedVectors σ K) :
    heckeOperator σ T v ∈ fixedVectors σ K := by
  intro k
  classical
  rw [heckeOperator_apply, map_sum]
  choose! φ hφ hφK using fun r (hr : r ∈ T.reps) => T.exists_rep k r hr
  have hterm : ∀ r ∈ T.reps, σ.π k.val (σ.π r v) = σ.π (φ r) v := by
    intro r hr
    have hk : σ.π ((φ r)⁻¹ * (k.val * r)) v = v := hv ⟨_, hφK r hr⟩
    calc σ.π k.val (σ.π r v) = σ.π (k.val * r) v := by rw [map_mul]; rfl
      _ = σ.π (φ r * ((φ r)⁻¹ * (k.val * r))) v := by rw [mul_inv_cancel_left]
      _ = σ.π (φ r) (σ.π ((φ r)⁻¹ * (k.val * r)) v) := by rw [map_mul]; rfl
      _ = σ.π (φ r) v := by rw [hk]
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn φ T.reps := by
    intro r₁ h₁ r₂ h₂ heq
    apply T.disjoint r₁ h₁ r₂ h₂
    have m₁ := hφK r₁ h₁
    have m₂ := hφK r₂ h₂
    rw [heq] at m₁
    have := K.mul_mem (K.inv_mem m₁) m₂
    simpa [mul_assoc] using this
  have hmaps : ∀ r ∈ T.reps, φ r ∈ T.reps := hφ
  have hsurj : Set.SurjOn φ T.reps T.reps :=
    Finset.surj_on_of_inj_on_of_card_le (fun r hr => φ r) (fun r hr => hmaps r hr)
      (fun a b ha hb h => hinj ha hb h) le_rfl |> fun h => by
        intro b hb
        obtain ⟨a, ha, hab⟩ := h b hb
        exact ⟨a, ha, hab.symm⟩
  exact Finset.sum_nbij φ hmaps hinj hsurj (fun _ _ => rfl)

theorem DoubleCoset.reps_nonempty {G : Type*} [Group G] {K : Subgroup G} (T : DoubleCoset K) :
    T.reps.Nonempty := by
  obtain ⟨r, hr, _⟩ := T.complete 1 1
  exact ⟨r, hr⟩

theorem inner_pi_fixed (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL} (a : K)
    (x : σ.H) {u : σ.H} (hu : u ∈ fixedVectors σ K) :
    inner ℂ (σ.π a.val x) u = inner ℂ x u := by
  have hu' : σ.π a.val (σ.π a⁻¹.val u) = σ.π a.val u := by rw [hu a⁻¹, hu a]
  have : u = σ.π a.val u := (hu a).symm
  calc inner ℂ (σ.π a.val x) u = inner ℂ (σ.π a.val x) (σ.π a.val u) := by rw [← this]
    _ = inner ℂ x u := cuspOperator_inner σ a.val x u

/-- Each coset representative pairs with fixed vectors like the double-coset element. -/
theorem inner_rep_fixed (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL}
    (T : DoubleCoset K) {r : BinaryAdelicGL} (hr : r ∈ T.reps) {v u : σ.H}
    (hv : v ∈ fixedVectors σ K) (hu : u ∈ fixedVectors σ K) :
    inner ℂ (σ.π r v) u = inner ℂ (σ.π T.g v) u := by
  obtain ⟨a, b, rfl⟩ := T.inDouble r hr
  have : σ.π (a.val * T.g * b.val) v = σ.π a.val (σ.π T.g v) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv b]
  rw [this, inner_pi_fixed σ a _ hu]

/-- **Projection formula.** On `K`-fixed vectors, the Hecke operator pairs with fixed vectors as
`(number of cosets) · π(g)`; equivalently it is that multiple of the compression of `π(g)`. -/
theorem inner_heckeOperator_fixed (σ : CuspidalRepresentation) {K : Subgroup BinaryAdelicGL}
    (T : DoubleCoset K) {v u : σ.H} (hv : v ∈ fixedVectors σ K) (hu : u ∈ fixedVectors σ K) :
    inner ℂ (heckeOperator σ T v) u = (T.reps.card : ℂ) * inner ℂ (σ.π T.g v) u := by
  rw [heckeOperator_apply, sum_inner, Finset.sum_congr rfl (fun r hr => inner_rep_fixed σ T hr hv hu),
    Finset.sum_const, nsmul_eq_mul]

end TernaryPeriodPolynomials.RepresentationTheory
