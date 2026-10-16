module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.Schur

@[expose] public section


/-!
# Irreducibility of cyclic spans of Hecke-eigen fixed vectors

Let `π` be a unitary representation of a group `G` on a Hilbert space `H`, `K ≤ G`, and `φ` a
nonzero `K`-fixed vector such that the orthogonal projection of every `π(g) φ` onto `H^K` is a
multiple of `φ` ("`φ` is an eigenvector of every compression"). Then the closed span of the
orbit `π(G) φ` has no nontrivial closed invariant subspaces.

This is the standard route from a Hecke eigenform to an irreducible automorphic representation.
It is needed to build `CuspidalRepresentation`s, as in `inner_bad_line_cuspidal_span`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.RepresentationTheory

variable {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A unitary action by bounded operators. -/
structure UnitaryAction (G : Type*) [Group G] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : G →* (H →L[ℂ] H)
  inner_op : ∀ g x y, inner ℂ (op g x) (op g y) = inner ℂ x y

variable (π : UnitaryAction G H)

theorem UnitaryAction.op_inv_apply (g : G) (x : H) : π.op g (π.op g⁻¹ x) = x := by
  have := congrArg (fun F : H →L[ℂ] H => F x)
    (show π.op g * π.op g⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
  exact this

theorem UnitaryAction.inner_op_left (g : G) (x y : H) :
    inner ℂ (π.op g x) y = inner ℂ x (π.op g⁻¹ y) := by
  conv_lhs => rw [← π.op_inv_apply g y]
  exact π.inner_op g _ _

/-- Orthogonal complements of invariant subspaces are invariant. -/
theorem UnitaryAction.orthogonal_invariant (W : Submodule ℂ H) (hW : ∀ g, ∀ w ∈ W, π.op g w ∈ W)
    (g : G) {u : H} (hu : u ∈ Wᗮ) : π.op g u ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal'] at hu ⊢
  intro w hw
  rw [π.inner_op_left, hu _ (hW g⁻¹ w hw)]

/-- Orthogonal projections onto closed invariant subspaces commute with the action. -/
theorem UnitaryAction.starProjection_comm (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (hW : ∀ g, ∀ w ∈ W, π.op g w ∈ W) (g : G) (x : H) :
    W.starProjection (π.op g x) = π.op g (W.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW g _ (W.starProjection_apply_mem x))
  intro w hw
  rw [← map_sub, π.inner_op_left]
  exact Submodule.starProjection_inner_eq_zero x _ (hW g⁻¹ w hw)

/-- The closed span of an orbit. -/
def orbitSpan (φ : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun g : G => π.op g φ)).topologicalClosure

theorem orbitSpan_invariant (φ : H) (g : G) {w : H} (hw : w ∈ orbitSpan π φ) :
    π.op g w ∈ orbitSpan π φ := by
  have hspan : Submodule.span ℂ (Set.range fun g : G => π.op g φ) ≤
      (orbitSpan π φ).comap (π.op g : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨g * h, by simp [map_mul]⟩
  have hclosed : IsClosed (((orbitSpan π φ).comap (π.op g : H →ₗ[ℂ] H)) : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (π.op g).continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hw

/-- A continuous linear map sending the orbit into a closed submodule sends the orbit span there. -/
theorem orbitSpan_map_le (φ : H) (T : H →L[ℂ] H) (S : Submodule ℂ H) (hS : IsClosed (S : Set H))
    (hT : ∀ g, T (π.op g φ) ∈ S) {w : H} (hw : w ∈ orbitSpan π φ) : T w ∈ S := by
  have hspan : Submodule.span ℂ (Set.range fun g : G => π.op g φ) ≤ S.comap (T : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hT g
  exact Submodule.topologicalClosure_minimal _ hspan (hS.preimage T.continuous) hw

theorem mem_orbitSpan_self (φ : H) : φ ∈ orbitSpan π φ := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- The fixed vectors of a subgroup. -/
def fixedSpace (K : Subgroup G) : Submodule ℂ H where
  carrier := {x | ∀ k ∈ K, π.op k x = x}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k hk; simp
  smul_mem' := by intro c a ha k hk; simp [ha k hk]

theorem fixedSpace_isClosed (K : Subgroup G) : IsClosed (fixedSpace π K : Set H) := by
  have : (fixedSpace π K : Set H) = ⋂ k ∈ K, {x | π.op k x = x} := by
    ext x; simp [fixedSpace]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (π.op k).continuous continuous_id

/-- **Cyclic irreducibility.** The closed span of the orbit of a nonzero `K`-fixed vector that is an
eigenvector of every compression has no nontrivial closed invariant subspace. -/
theorem orbitSpan_irreducible (K : Subgroup G) (φ : H) (hφK : φ ∈ fixedSpace π K) (hφ0 : φ ≠ 0)
    (eigen : ∀ g, ∃ c : ℂ, (haveI : CompleteSpace (fixedSpace π K) :=
        (fixedSpace_isClosed π K).completeSpace_coe
      (fixedSpace π K).starProjection (π.op g φ)) = c • φ)
    (W : Submodule ℂ H) (hWc : IsClosed (W : Set H)) (hWi : ∀ g, ∀ w ∈ W, π.op g w ∈ W)
    (hWle : W ≤ orbitSpan π φ) : W = ⊥ ∨ orbitSpan π φ ≤ W := by
  have : CompleteSpace (fixedSpace π K) := (fixedSpace_isClosed π K).completeSpace_coe
  have : CompleteSpace W := hWc.completeSpace_coe
  set V := fixedSpace π K
  set P := W.starProjection
  -- `P φ` is `K`-fixed and lies in the orbit span, hence is a multiple of `φ`
  have hPφV : P φ ∈ V := by
    intro k hk
    rw [← π.starProjection_comm W hWi k φ, hφK k hk]
  have hline : IsClosed ((Submodule.span ℂ {φ} : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hproj : ∀ w ∈ orbitSpan π φ, V.starProjection w ∈ Submodule.span ℂ {φ} := by
    intro w hw
    apply orbitSpan_map_le π φ V.starProjection _ hline _ hw
    intro g
    obtain ⟨c, hc⟩ := eigen g
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)
  have hPφ : P φ ∈ Submodule.span ℂ {φ} := by
    have := hproj (P φ) (hWle (W.starProjection_apply_mem φ))
    rwa [Submodule.starProjection_eq_self_iff.mpr hPφV] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPφ
  -- `P = c` on the orbit span
  have hPc : ∀ w ∈ orbitSpan π φ, P w = c • w := by
    intro w hw
    have := orbitSpan_map_le π φ (P - c • (1 : H →L[ℂ] H)) ⊥ isClosed_singleton (fun g => ?_) hw
    · simpa [sub_eq_zero] using this
    · change P (π.op g φ) - c • π.op g φ ∈ (⊥ : Submodule ℂ H)
      rw [Submodule.mem_bot, π.starProjection_comm W hWi g φ, ← hc, map_smul, sub_self]
  -- `c` is idempotent
  have hidem : c * c = c := by
    have h1 : P (P φ) = P φ := Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem φ)
    rw [← hc, map_smul, ← hc, smul_smul] at h1
    exact smul_left_injective ℂ hφ0 h1
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hidem, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hc01 with h0 | h1
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have := hPc w (hWle hw)
    rw [Submodule.starProjection_eq_self_iff.mpr hw, h0, zero_smul] at this
    exact this
  · right
    intro w hw
    have := hPc w hw
    rw [h1, one_smul] at this
    rw [← this]
    exact W.starProjection_apply_mem w

end TernaryPeriodPolynomials.RepresentationTheory
