module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedLinear
public import TernaryPeriodPolynomials.BoundaryComparison.EichlerShimura

@[expose] public section


/-!
# Seed surjectivity at level `Γ(N)` and `eisensteinP` from the plane constant terms alone

Formalized by Claude Sonnet 5.5.
* `faceSeedKerClass_add/_smul`, `faceSeedConjKerClass_add/_smul` (assembled from the `SeedLinear`), `seedLinearity`, `classicalLinearity` (`GammaNSeedLinear.lean`).
* `holSeedRange`, `conjSeedRange`, `exists_seed_sum`: every class of `faceCuspidalInH2` is `[seed f] + [conjugate seed g]` (Eichler-Shimura spanning for `Γ(N)`, unconditional, plus linearity).
* **`seedBoundary_surjective`**: every `ξ ∈ 𝒞_P(E)` is the seed vector of a tuple of cusp forms.
* **`eisensteinP_of_planeConstantTerms`**: the `eisensteinP` follows from `ClassicalPlaneConstantTerms` alone.
-/

open scoped MatrixGroups DirectSum
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The classes of the holomorphic seeds of cusp forms at the plane cusp `h`, as a submodule of `H²(Γ_{h⁻¹Ph}, E_n)`. -/
def holSeedRange (h : SL(3, ℤ)) : Submodule ℂ (groupCohomology.H2 (faceRep N h n)) where
  carrier := {y | ∃ f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), y = (faceSeedKerClass N h n f).1}
  zero_mem' := ⟨0, by
    have := faceSeedKerClass_smul N n h (0 : ℂ) (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    rw [zero_smul, zero_smul] at this
    rw [this]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, by rw [faceSeedKerClass_add, Submodule.coe_add]⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨c • f, by rw [faceSeedKerClass_smul, Submodule.coe_smul]⟩

/-- The classes of the antiholomorphic seeds. -/
def conjSeedRange (h : SL(3, ℤ)) : Submodule ℂ (groupCohomology.H2 (faceRep N h n)) where
  carrier := {y | ∃ f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), y = (faceSeedConjKerClass N h n f).1}
  zero_mem' := ⟨0, by
    have := faceSeedConjKerClass_smul N n h (0 : ℂ) (0 : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    rw [zero_smul, map_zero, zero_smul] at this
    rw [this]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, by rw [faceSeedConjKerClass_add, Submodule.coe_add]⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    refine ⟨(starRingEnd ℂ c) • f, ?_⟩
    rw [faceSeedConjKerClass_smul, Submodule.coe_smul]
    simp

theorem faceSeedSpan_le_sup (h : SL(3, ℤ)) :
    faceSeedSpan N h n ≤ holSeedRange N n h ⊔ conjSeedRange N n h := by
  unfold faceSeedSpan
  rw [Submodule.map_le_iff_le_comap]
  unfold faceSeedKerSpan
  rw [Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · exact Submodule.mem_sup_left ⟨f, rfl⟩
  · exact Submodule.mem_sup_right ⟨f, rfl⟩

/-- **Every cuspidal class of a plane cusp is the sum of a holomorphic and an antiholomorphic seed class** (Eichler-Shimura spanning,
unconditional for `Γ(N)`). -/
theorem exists_seed_sum (h : SL(3, ℤ)) (y : groupCohomology.H2 (faceRep N h n)) (hy : y ∈ faceCuspidalInH2 N h n) :
    ∃ f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ),
      y = (faceSeedKerClass N h n f).1 + (faceSeedConjKerClass N h n g).1 := by
  have hES := Statements.EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [← faceSeedSpan_eq_cuspidalInH2 N h n hES] at hy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (faceSeedSpan_le_sup N n h hy)
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  exact ⟨f, g, hab.symm⟩

open scoped Classical in
theorem seedBoundary_apply (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (i : PlaneFaces N) :
    seedBoundary N n f i = (faceSeedKerClass N (planeFaceRepr i) n (f i false)).1 +
      (faceSeedConjKerClass N (planeFaceRepr i) n (f i true)).1 := by
  unfold seedBoundary
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [DirectSum.lof_eq_of]
  · intro j _ hj
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
  · simp

open scoped Classical in
/-- **Seed surjectivity**: every `ξ ∈ 𝒞_P(E)` is the seed vector of a tuple of cusp forms. -/
theorem seedBoundary_surjective (ξ : PlaneCuspSum N n) :
    ∃ f : TwTuple N n, planeCuspSumEmbedding N n ξ = seedBoundary N n f := by
  have h1 : ∀ i : PlaneFaces N, ∃ f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ),
      faceCuspidalEmbedding N n (planeFaceRepr i) (ξ i) =
        (faceSeedKerClass N (planeFaceRepr i) n f).1 + (faceSeedConjKerClass N (planeFaceRepr i) n g).1 := fun i =>
    exists_seed_sum N n _ _ (by
      rw [faceCuspidalInH2_eq_range]; exact ⟨ξ i, rfl⟩)
  choose F G hFG using h1
  refine ⟨fun i b => if b then G i else F i, ?_⟩
  apply DFinsupp.ext
  intro i
  have hl : (planeCuspSumEmbedding N n ξ) i = faceCuspidalEmbedding N n (planeFaceRepr i) (ξ i) := by
    unfold planeCuspSumEmbedding
    simp [DirectSum.lmap_apply]
  have hr : (seedBoundary N n (fun i b => if b then G i else F i)) i =
      (faceSeedKerClass N (planeFaceRepr i) n (F i)).1 + (faceSeedConjKerClass N (planeFaceRepr i) n (G i)).1 :=
    seedBoundary_apply N n _ i
  rw [hl, hr, hFG]

/-- **`eisensteinP` of S1 from the plane constant terms alone**: linearity (S6) and seed surjectivity (Eichler-Shimura spanning) are unconditional. -/
theorem eisensteinP_of_planeConstantTerms (hN : 3 ≤ N) (hn : 4 ≤ n) (hP : ClassicalPlaneConstantTerms N n hn) :
    ∃ T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n,
      ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
        planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
          lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c :=
  eisensteinP_of_section hN hn hP (classicalLinearity N n hn) (seedBoundary_surjective N n)

end TernaryPeriodPolynomials.Argument.FormClassK
