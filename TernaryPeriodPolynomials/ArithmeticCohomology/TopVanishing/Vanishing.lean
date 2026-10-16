module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Comparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Homogeneous

@[expose] public section


/-!
# Top-degree vanishing from a free resolution of length three

If a subgroup `Λ` of `G` has a free resolution of `ℂ` of length three by permutation modules, then
every invariant scalar four-cocycle of the homogeneous model with vertices in `G` is a coboundary:
with `s` the equivariant map satisfying `d s d = d` in index four, the primitive is `f ∘ s`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

open TernaryPeriodPolynomials.Duality

variable {G : Type} [Group G]

/-- A free resolution of length three gives `H⁴(Λ, ℂ) = 0` in the homogeneous model. -/
theorem topVanishing_of_freeResolution {Λ : Subgroup G} (X : FreeResolution Λ 3) :
    IsTopVanishing Λ := by
  intro f hf hcocycle
  have key : ∃ s : ((Fin 4 → G) →₀ ℂ) →ₗ[ℂ] ((Fin 5 → G) →₀ ℂ), Equivariant Λ s ∧
      homogeneousBoundary 4 ∘ₗ s ∘ₗ homogeneousBoundary 4 = homogeneousBoundary (G := G) 4 :=
    exists_splitting X (homogeneousComplex_free Λ) (homogeneousComplex_exact Λ)
  obtain ⟨s, hs, split⟩ := key
  have Finv : ∀ (γ : Λ) (v : (Fin 5 → G) →₀ ℂ),
      Finsupp.linearCombination ℂ f (chainAct Λ γ v) = Finsupp.linearCombination ℂ f v := by
    intro γ v
    have hcomp : (f ∘ fun x => γ • x) = f := funext fun x => hf γ x
    rw [chainAct, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain, hcomp]
  have Fd : Finsupp.linearCombination ℂ f ∘ₗ homogeneousBoundary (G := G) 5 = 0 := by
    apply Finsupp.lhom_ext
    intro x a
    have hx : Finsupp.single x a = a • Finsupp.single x (1 : ℂ) := by simp
    rw [LinearMap.zero_apply, LinearMap.comp_apply, hx, map_smul, map_smul,
      ← differentialFourRaw_eq, hcocycle x, smul_zero]
  have hΘ : Finsupp.linearCombination ℂ (fun y => Finsupp.linearCombination ℂ f
      (s (Finsupp.single y 1))) = Finsupp.linearCombination ℂ f ∘ₗ s := by
    apply Finsupp.lhom_ext
    intro y a
    have hy : Finsupp.single y a = a • Finsupp.single y (1 : ℂ) := by simp
    rw [Finsupp.linearCombination_single, LinearMap.comp_apply, hy, map_smul, map_smul]
  refine ⟨fun x => Finsupp.linearCombination ℂ f (s (Finsupp.single x 1)), ?_, ?_⟩
  · intro γ x
    have e : (Finsupp.single (γ • x) 1 : (Fin 4 → G) →₀ ℂ) =
        chainAct Λ γ (Finsupp.single x 1) := (chainAct_single γ x 1).symm
    show Finsupp.linearCombination ℂ f (s (Finsupp.single (γ • x) 1)) =
      Finsupp.linearCombination ℂ f (s (Finsupp.single x 1))
    rw [e, hs.apply, Finv]
  · intro x
    rw [differentialThreeRaw_eq, hΘ, LinearMap.comp_apply]
    have hker : Finsupp.single x 1 - s (homogeneousBoundary 4 (Finsupp.single x 1)) ∈
        LinearMap.ker (homogeneousBoundary (G := G) 4) := by
      rw [LinearMap.mem_ker, map_sub]
      have h := LinearMap.congr_fun split (Finsupp.single x 1)
      exact sub_eq_zero.mpr h.symm
    obtain ⟨w, hw⟩ := (homogeneousComplex_exact Λ).2 4 hker
    have hw0 : Finsupp.linearCombination ℂ f (homogeneousBoundary 5 w) = 0 :=
      LinearMap.congr_fun Fd w
    have hw' : homogeneousBoundary 5 w =
        Finsupp.single x 1 - s (homogeneousBoundary 4 (Finsupp.single x 1)) := hw
    calc Finsupp.linearCombination ℂ f (s (homogeneousBoundary 4 (Finsupp.single x 1)))
        = Finsupp.linearCombination ℂ f (Finsupp.single x 1) -
            Finsupp.linearCombination ℂ f
              (Finsupp.single x 1 - s (homogeneousBoundary 4 (Finsupp.single x 1))) := by
          rw [map_sub]
          abel
      _ = Finsupp.linearCombination ℂ f (Finsupp.single x 1) := by
          rw [← hw', hw0, sub_zero]
      _ = f x := by
          rw [Finsupp.linearCombination_single, one_smul]

end TernaryPeriodPolynomials.TopVanishing
