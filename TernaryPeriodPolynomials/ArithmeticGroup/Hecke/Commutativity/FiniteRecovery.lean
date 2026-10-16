module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AlgebraProjector

@[expose] public section


/-!
# Finite spectral recovery from algebra membership and constituent separation

If every isotypical projection `p D` lies in the (common) away-from-three Hecke
algebra, and two associate pairs are either equal or intersect trivially, then
every boundary vector whose line coordinate lies in `automorphicLineSpan n` is
recovered on the line side by a finite sum of the projections `p D`.

The proof is elementary linear algebra: elements of the algebra are block
diagonal for the plane/line decomposition and commute, distinct projections are
orthogonal on each other's ranges, and a span induction collects the finitely
many distinct projections needed.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- Block diagonality for the plane/line decomposition. -/
def BlockDiagonal {n : ℕ} {χ : RankOneCharacter} (f : Module.End ℂ (BoundaryCoordinates n χ)) :
    Prop :=
  (∀ x, (f (x, 0)).2 = 0) ∧ ∀ y, (f (0, y)).1 = 0

theorem blockDiagonal_of_mem {n : ℕ} {D : InducingData n} {hecke : BoundaryHecke n D.chi}
    {f : Module.End ℂ (BoundaryCoordinates n D.chi)} (hf : f ∈ awayThreeHeckeAlgebra D hecke) :
    BlockDiagonal f := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    refine ⟨fun x => ?_, fun y => ?_⟩
    · simp [pairHecke]
    · simp [pairHecke]
  | algebraMap r =>
    refine ⟨fun x => ?_, fun y => ?_⟩
    · simp [Module.algebraMap_end_apply]
    · simp [Module.algebraMap_end_apply]
  | add f g _ _ hf hg =>
    refine ⟨fun x => ?_, fun y => ?_⟩
    · simp [hf.1 x, hg.1 x]
    · simp [hf.2 y, hg.2 y]
  | mul f g _ _ hf hg =>
    refine ⟨fun x => ?_, fun y => ?_⟩
    · have h : g (x, 0) = ((g (x, 0)).1, 0) := Prod.ext rfl (hg.1 x)
      rw [Module.End.mul_apply, h]
      exact hf.1 _
    · have h : g (0, y) = (0, (g (0, y)).2) := Prod.ext (hg.2 y) rfl
      rw [Module.End.mul_apply, h]
      exact hf.2 _

theorem snd_apply_of_blockDiagonal {n : ℕ} {χ : RankOneCharacter}
    {f : Module.End ℂ (BoundaryCoordinates n χ)} (hf : BlockDiagonal f)
    (b : BoundaryCoordinates n χ) : (f b).2 = (f (0, b.2)).2 := by
  have hb : b = (b.1, 0) + (0, b.2) := by ext <;> simp
  conv_lhs => rw [hb]
  rw [map_add, Prod.snd_add, hf.1, zero_add]

/-- Abstract finite recovery: commuting block-diagonal projections onto pairwise
equal-or-independent subspaces recover every vector of the span of the line
parts by a finite sum. -/
theorem finite_recovery_abstract {V₁ V₂ ι : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (A : ι → Submodule ℂ (V₁ × V₂)) (L : ι → Submodule ℂ V₂)
    (hL : ∀ i, ∀ a ∈ L i, ((0 : V₁), a) ∈ A i)
    (p : ι → Module.End ℂ (V₁ × V₂))
    (hrange : ∀ i, LinearMap.range (p i) = A i) (hid : ∀ i, ∀ x ∈ A i, p i x = x)
    (hblock : ∀ i x, (p i (x, 0)).2 = 0)
    (hcomm : ∀ i j, p i * p j = p j * p i)
    (hsep : ∀ i j, A i ⊓ A j = ⊥ ∨ A i = A j)
    (b : V₁ × V₂) (hb : b.2 ∈ Submodule.span ℂ {a | ∃ i, a ∈ L i}) :
    ∃ (m : ℕ) (D : Fin m → ι), ∑ k, (p (D k) b).2 = b.2 := by
  classical
  have hsnd : ∀ i (b : V₁ × V₂), (p i b).2 = (p i (0, b.2)).2 := by
    intro i b
    have hb : b = (b.1, 0) + (0, b.2) := by ext <;> simp
    conv_lhs => rw [hb]
    rw [map_add, Prod.snd_add, hblock, zero_add]
  have horth : ∀ i j, p j ≠ p i → ∀ x ∈ A i, p j x = 0 := by
    intro i j hne x hx
    rcases hsep i j with hbot | heq
    · have hxD : p i x = x := hid i x hx
      have h1 : p j x ∈ A j := by
        rw [← hrange j]; exact LinearMap.mem_range_self _ x
      have h2 : p j x ∈ A i := by
        rw [← hxD, ← Module.End.mul_apply, ← hcomm i j, Module.End.mul_apply, ← hrange i]
        exact LinearMap.mem_range_self _ _
      have h3 : p j x ∈ A i ⊓ A j := ⟨h2, h1⟩
      rw [hbot] at h3
      exact (Submodule.mem_bot ℂ).mp h3
    · exact absurd (TernaryPeriodPolynomials.HeckeStability.eq_of_commute_of_same_range
        (A i) (hrange i) (hid i) ((hrange j).trans heq.symm)
        (fun x hx => hid j x (heq ▸ hx)) (hcomm i j)) hne
  have key : ∀ y, y ∈ Submodule.span ℂ {a | ∃ i, a ∈ L i} → ∃ S : Finset ι,
      ∀ T : Finset (Module.End ℂ (V₁ × V₂)),
        S.image p ⊆ T → (∀ e ∈ T, ∃ i, p i = e) →
        ∑ e ∈ T, (e (0, y)).2 = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, hi⟩ := ha
      refine ⟨{i}, fun T hT hTp => ?_⟩
      have hiT : p i ∈ T := hT (by simp)
      have hmemA : ((0 : V₁), a) ∈ A i := hL i a hi
      rw [← Finset.add_sum_erase T _ hiT, hid i _ hmemA]
      have hrest : ∑ e ∈ T.erase (p i), (e (0, a)).2 = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        obtain ⟨hne, heT⟩ := Finset.mem_erase.mp he
        obtain ⟨j, rfl⟩ := hTp e heT
        rw [horth i j hne _ hmemA]
        rfl
      rw [hrest, add_zero]
    | zero =>
      refine ⟨∅, fun T _ _ => ?_⟩
      apply Finset.sum_eq_zero
      intro e _
      have : ((0 : V₁), (0 : V₂)) = 0 := rfl
      rw [this, map_zero]
      rfl
    | add x y _ _ hx hy =>
      obtain ⟨S₁, h₁⟩ := hx
      obtain ⟨S₂, h₂⟩ := hy
      refine ⟨S₁ ∪ S₂, fun T hT hTp => ?_⟩
      have e1 := h₁ T (fun e he => hT (Finset.image_subset_image Finset.subset_union_left he)) hTp
      have e2 := h₂ T (fun e he => hT (Finset.image_subset_image Finset.subset_union_right he)) hTp
      have hsplit : ∀ e : Module.End ℂ (V₁ × V₂),
          (e (0, x + y)).2 = (e (0, x)).2 + (e (0, y)).2 := by
        intro e
        have : ((0 : V₁), x + y) = (0, x) + (0, y) := by ext <;> simp
        rw [this, map_add, Prod.snd_add]
      simp only [hsplit, Finset.sum_add_distrib, e1, e2]
    | smul c x _ hx =>
      obtain ⟨S, h⟩ := hx
      refine ⟨S, fun T hT hTp => ?_⟩
      have e1 := h T hT hTp
      have hsplit : ∀ e : Module.End ℂ (V₁ × V₂), (e (0, c • x)).2 = c • (e (0, x)).2 := by
        intro e
        have : ((0 : V₁), c • x) = c • (0, x) := by ext <;> simp
        rw [this, map_smul]
        rfl
      simp only [hsplit, ← Finset.smul_sum, e1]
  obtain ⟨S, hS⟩ := key b.2 hb
  have hT := hS (S.image p) (subset_refl _) (fun e he => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i, rfl⟩)
  have hchoose : ∀ e : S.image p, ∃ i, p i = e.val := fun e => by
    obtain ⟨i, -, h⟩ := Finset.mem_image.mp e.property
    exact ⟨i, h⟩
  refine ⟨(S.image p).card, fun k => (hchoose ((S.image p).equivFin.symm k)).choose, ?_⟩
  have hspec : ∀ k, p (hchoose ((S.image p).equivFin.symm k)).choose =
      ((S.image p).equivFin.symm k).val :=
    fun k => (hchoose ((S.image p).equivFin.symm k)).choose_spec
  conv_rhs => rw [← hT, ← Finset.sum_coe_sort (S.image p), ← Equiv.sum_comp (S.image p).equivFin.symm]
  apply Finset.sum_congr rfl
  intro k _
  rw [hsnd, hspec]

theorem paper_commute {n : ℕ} (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (D D' : CohomologicalCuspData n)
    (f g : Module.End ℂ (BoundaryCoordinates n trivialCharacter))
    (hf : f ∈ awayThreeHeckeAlgebra D.inducingData hecke)
    (hg : g ∈ awayThreeHeckeAlgebra D'.inducingData hecke) : f * g = g * f :=
  (awayThreeHeckeAlgebra_commute D.inducingData hecke hhecke hf hg).eq

theorem paper_block {n : ℕ} (hecke : BoundaryHecke n trivialCharacter) (D : CohomologicalCuspData n)
    (f : Module.End ℂ (BoundaryCoordinates n trivialCharacter))
    (hf : f ∈ awayThreeHeckeAlgebra D.inducingData hecke)
    (x : StratumH2 n trivialCharacter .plane) : (f (x, 0)).2 = 0 :=
  (blockDiagonal_of_mem (D := D.inducingData) hf).1 x

/-- Specialization to paper data with trivial character. -/
theorem finite_recovery {n : ℕ}
    (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
    (p : CohomologicalCuspData n → Module.End ℂ (BoundaryCoordinates n trivialCharacter))
    (hp : ∀ D : CohomologicalCuspData n, IsIsotypicalProjection D.inducingData hecke (p D))
    (hmem : ∀ D : CohomologicalCuspData n, p D ∈ awayThreeHeckeAlgebra D.inducingData hecke)
    (hsep : ∀ D D' : CohomologicalCuspData n,
      associatePair D.inducingData ⊓ associatePair D'.inducingData = ⊥ ∨
        associatePair D.inducingData = associatePair D'.inducingData)
    (b : BoundaryCoordinates n trivialCharacter) (hb : b.2 ∈ automorphicLineSpan n) :
    ∃ (m : ℕ) (D : Fin m → CohomologicalCuspData n), ∑ i, (p (D i) b).2 = b.2 :=
  finite_recovery_abstract
    (V₁ := StratumH2 n trivialCharacter .plane) (V₂ := StratumH2 n trivialCharacter .line)
    (fun D : CohomologicalCuspData n => associatePair D.inducingData)
    (fun D : CohomologicalCuspData n => boundarySummand D.inducingData .line)
    (fun _ _ ha => ⟨Submodule.zero_mem _, ha⟩) p (fun D => (hp D).1) (fun D => (hp D).2.1)
    (fun D => paper_block hecke D (p D) (hmem D))
    (fun D D' => paper_commute hecke hhecke D D' (p D) (p D') (hmem D) (hmem D'))
    hsep b hb

end TernaryPeriodPolynomials.HeckeCommutativity
