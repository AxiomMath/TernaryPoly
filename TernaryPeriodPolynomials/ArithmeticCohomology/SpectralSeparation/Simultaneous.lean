module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Projector

@[expose] public section


/-!
# Simultaneous spectral projectors and eigencharacter separation

For a commutative subalgebra `𝒜 ≤ End(W)` (`W` finite dimensional over `ℂ`) and an
`𝒜`-stable subspace `A` satisfying eigencharacter separation, we construct `e ∈ 𝒜`
with range `A` that is the identity on `A`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open Polynomial Module

namespace TernaryPeriodPolynomials.SpectralSeparation

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Eigencharacter separation: a vector sharing all simultaneous generalized
eigenvalues with a nonzero vector of `A` lies in `A`. -/
def EigenSeparated (𝒜 : Subalgebra ℂ (Module.End ℂ W)) (A : Submodule ℂ W) : Prop :=
  ∀ a w : W, a ∈ A → a ≠ 0 →
    (∀ f ∈ 𝒜, ∃ μ : ℂ, (∃ k : ℕ, ((f - μ • 1) ^ k) a = 0) ∧ ∃ k : ℕ, ((f - μ • 1) ^ k) w = 0) →
    w ∈ A

omit [FiniteDimensional ℂ W] in
theorem spectralPoly_aeval_mem (𝒜 : Subalgebra ℂ (Module.End ℂ W)) {f : Module.End ℂ W}
    (hf : f ∈ 𝒜) (p : ℂ[X]) : aeval f p ∈ 𝒜 := by
  rw [← Polynomial.aeval_subalgebra_coe p 𝒜 ⟨f, hf⟩]
  exact SetLike.coe_mem _

/-- A finite sum of elements of a commutative ring, each of which has a power in the ideal `I`,
has a power in `I`. -/
private theorem sum_pow_mem {R ι : Type*} [CommRing R] (I : Ideal R) (s : Finset ι) (x : ι → R)
    (h : ∀ i ∈ s, ∃ k : ℕ, x i ^ k ∈ I) : ∃ K : ℕ, (∑ i ∈ s, x i) ^ K ∈ I := by
  have hnil : IsNilpotent (Ideal.Quotient.mk I (∑ i ∈ s, x i)) := by
    rw [map_sum]
    apply isNilpotent_sum
    intro i hi
    obtain ⟨k, hk⟩ := h i hi
    exact ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hk⟩
  obtain ⟨K, hK⟩ := hnil
  exact ⟨K, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hK⟩

theorem exists_spectral_of_separated (𝒜 : Subalgebra ℂ (Module.End ℂ W))
    (hcomm : ∀ f ∈ 𝒜, ∀ g ∈ 𝒜, f * g = g * f)
    (A : Submodule ℂ W) (hA : ∀ f ∈ 𝒜, ∀ a ∈ A, f a ∈ A) (hsep : EigenSeparated 𝒜 A) :
    ∃ e ∈ 𝒜, LinearMap.range e = A ∧ ∀ x ∈ A, e x = x := by
  classical
  let inst : CommRing 𝒜 :=
    { (inferInstance : Ring 𝒜) with
      mul_comm := fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2) }
  -- a finite spanning family of `𝒜`
  set S := Subalgebra.toSubmodule 𝒜
  set d := Module.finrank ℂ S
  let B := Module.finBasis ℂ S
  let b : Fin d → Module.End ℂ W := fun i => ((B i : S) : Module.End ℂ W)
  have hb : ∀ i, b i ∈ 𝒜 := fun i => (B i).2
  have hspan : ∀ f (hf : f ∈ 𝒜), f = ∑ i, (B.repr ⟨f, hf⟩ i) • b i := by
    intro f hf
    have h2 : ((∑ i, B.repr ⟨f, hf⟩ i • B i : S) : Module.End ℂ W) = f := by
      rw [B.sum_repr]
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  -- single-operator spectral projectors, as elements of `𝒜`
  let s : Fin d → Finset ℂ := fun i => (LinearMap.charpoly (b i)).roots.toFinset
  let e1 : Fin d → ℂ → 𝒜 := fun i μ =>
    ⟨aeval (b i) (spectralPoly (b i) μ), spectralPoly_aeval_mem 𝒜 (hb i) _⟩
  have he1sum : ∀ i, ∑ μ ∈ s i, e1 i μ = 1 := by
    intro i
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact sum_spectralPoly (b i)
  -- simultaneous projectors
  let E : (Fin d → ℂ) → 𝒜 := fun l => ∏ i, e1 i (l i)
  let T := Fintype.piFinset s
  have hEsum : ∑ l ∈ T, E l = 1 := by
    simp only [E, T]
    rw [← Finset.prod_univ_sum]
    simp [he1sum]
  have hEmem : ∀ l i (y : W), ((E l : 𝒜) : Module.End ℂ W) y ∈ (b i).maxGenEigenspace (l i) := by
    intro l i y
    have h : E l = e1 i (l i) * ∏ j ∈ Finset.univ.erase i, e1 j (l j) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [h, Subalgebra.coe_mul, Module.End.mul_apply]
    exact spectralPoly_mem (b i) (l i) _
  -- nilpotency of `f - μ` on a simultaneous generalized eigenspace
  have hnil : ∀ (l : Fin d → ℂ), ∀ f ∈ 𝒜, ∃ μ : ℂ, ∃ K : ℕ, ∀ y : W,
      (∀ i, y ∈ (b i).maxGenEigenspace (l i)) → ((f - μ • 1) ^ K) y = 0 := by
    intro l f hf
    set c := B.repr ⟨f, hf⟩
    refine ⟨∑ i, c i * l i, ?_⟩
    let V : Submodule ℂ W := ⨅ i, (b i).maxGenEigenspace (l i)
    have hV : ∀ y, y ∈ V ↔ ∀ i, y ∈ (b i).maxGenEigenspace (l i) := by
      intro y; simp [V, Submodule.mem_iInf]
    let I : Ideal 𝒜 :=
      { carrier := {x | ∀ y ∈ V, (x : Module.End ℂ W) y = 0}
        add_mem' := by
          intro x x' hx hx' y hy
          simp [hx y hy, hx' y hy]
        zero_mem' := by
          intro y _
          rfl
        smul_mem' := by
          intro r x hx y hy
          change ((r * x : 𝒜) : Module.End ℂ W) y = 0
          rw [Subalgebra.coe_mul, Module.End.mul_apply, hx y hy, map_zero] }
    let n : Fin d → 𝒜 := fun i => ⟨b i - l i • 1, by
      refine 𝒜.sub_mem (hb i) ?_
      rw [← Algebra.algebraMap_eq_smul_one]
      exact 𝒜.algebraMap_mem _⟩
    have hn : ∀ i, n i ^ Module.finrank ℂ W ∈ I := by
      intro i y hy
      have hyi := (hV y).mp hy i
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
        Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hyi
      change (((n i) ^ Module.finrank ℂ W : 𝒜) : Module.End ℂ W) y = 0
      rw [SubmonoidClass.coe_pow]
      exact hyi
    let x : 𝒜 := ⟨f - (∑ i, c i * l i) • 1, by
      refine 𝒜.sub_mem hf ?_
      rw [← Algebra.algebraMap_eq_smul_one]
      exact 𝒜.algebraMap_mem _⟩
    have hx : x = ∑ i, algebraMap ℂ 𝒜 (c i) * n i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      have hterm : ∀ i, ((algebraMap ℂ 𝒜 (c i) * n i : 𝒜) : Module.End ℂ W) =
          c i • b i - (c i * l i) • 1 := by
        intro i
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul]
        change c i • (b i - l i • 1) = _
        rw [smul_sub, smul_smul]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
      change f - (∑ i, c i * l i) • 1 = _
      conv_lhs => rw [hspan f hf]
      rw [Finset.sum_smul]
    have hsum := sum_pow_mem I Finset.univ (fun i => algebraMap ℂ 𝒜 (c i) * n i)
      (fun i _ => ⟨Module.finrank ℂ W, by
        rw [mul_pow]
        exact I.mul_mem_left _ (hn i)⟩)
    obtain ⟨K, hK⟩ := hsum
    rw [← hx] at hK
    refine ⟨K, fun y hy => ?_⟩
    have h := hK y ((hV y).mpr hy)
    rw [SubmonoidClass.coe_pow] at h
    exact h
  -- the projector
  let good : Finset (Fin d → ℂ) := T.filter (fun l => ∃ a ∈ A, ((E l : 𝒜) : Module.End ℂ W) a ≠ 0)
  let e : 𝒜 := ∑ l ∈ good, E l
  have hEapply : ∀ y : W, ∑ l ∈ T, ((E l : 𝒜) : Module.End ℂ W) y = y := by
    intro y
    have h := congrArg (fun z : 𝒜 => (z : Module.End ℂ W) y) hEsum
    simpa [AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply] using h
  have heapply : ∀ y : W, (e : Module.End ℂ W) y = ∑ l ∈ good, ((E l : 𝒜) : Module.End ℂ W) y := by
    intro y
    simp [e, LinearMap.sum_apply]
  have hid : ∀ y ∈ A, (e : Module.End ℂ W) y = y := by
    intro y hy
    rw [heapply]
    have hsplit := Finset.sum_filter_add_sum_filter_not T
      (fun l => ∃ a ∈ A, ((E l : 𝒜) : Module.End ℂ W) a ≠ 0)
      (fun l => ((E l : 𝒜) : Module.End ℂ W) y)
    have hzero : ∑ l ∈ T.filter (fun l => ¬ ∃ a ∈ A, ((E l : 𝒜) : Module.End ℂ W) a ≠ 0),
        ((E l : 𝒜) : Module.End ℂ W) y = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      simp only [not_exists, not_and, ne_eq, not_not] at hl'
      exact hl' y hy
    rw [hzero, add_zero, hEapply] at hsplit
    exact hsplit
  have hrange : ∀ y : W, (e : Module.End ℂ W) y ∈ A := by
    intro y
    rw [heapply]
    apply Submodule.sum_mem
    intro l hl
    obtain ⟨a, haA, hane⟩ := (Finset.mem_filter.mp hl).2
    apply hsep (((E l : 𝒜) : Module.End ℂ W) a) (((E l : 𝒜) : Module.End ℂ W) y)
      (hA _ (E l).2 a haA) hane
    intro f hf
    obtain ⟨μ, K, hK⟩ := hnil l f hf
    exact ⟨μ, ⟨K, hK _ (fun i => hEmem l i a)⟩, ⟨K, hK _ (fun i => hEmem l i y)⟩⟩
  refine ⟨(e : Module.End ℂ W), e.2, ?_, hid⟩
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact hrange y
  · intro y hy
    exact ⟨y, hid y hy⟩

end TernaryPeriodPolynomials.SpectralSeparation
