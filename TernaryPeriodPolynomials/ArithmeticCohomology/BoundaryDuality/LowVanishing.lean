module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainDuality
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Vanishing

@[expose] public section


/-!
# `H³ = 0` from a free resolution of length two, and three-cycles modulo a subgroup

If a subgroup `Λ` of `G` has a free resolution of `ℂ` of length two by permutation modules (for
instance a lattice `ℤ²`, with the square tiling of the plane), every invariant scalar three-cocycle
of the homogeneous model is the coboundary of an invariant two-cochain (`topVanishingThree_of_freeResolution`,
the argument of `TopVanishing.topVanishing_of_freeResolution` one degree lower). Dually,
every three-chain which is a cycle modulo `Λ`-null chains is a boundary modulo `Λ`-null chains
(`mem_bdryChains_of_cycle`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LowVanishing

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.ChainDuality

variable {G : Type} [Group G]

/-- `H³(Λ, ℂ) = 0` in the homogeneous model with vertices in `G`: every invariant scalar
three-cocycle is the coboundary of an invariant scalar two-cochain. -/
def TopVanishingThree (Λ : Subgroup G) : Prop :=
  ∀ f : (Fin 4 → G) → ℂ, (∀ (γ : Λ) x, f (fun i => γ.val * x i) = f x) →
    (∀ x, differentialThreeRaw f x = 0) →
    ∃ θ : (Fin 3 → G) → ℂ, (∀ (γ : Λ) x, θ (fun i => γ.val * x i) = θ x) ∧
      ∀ x, differentialTwoRaw θ x = f x

/-- A free resolution of length two gives `H³(Λ, ℂ) = 0` in the homogeneous model. -/
theorem topVanishingThree_of_freeResolution {Λ : Subgroup G} (X : FreeResolution Λ 2) :
    TopVanishingThree Λ := by
  intro f hf hcocycle
  have key : ∃ s : ((Fin 3 → G) →₀ ℂ) →ₗ[ℂ] ((Fin 4 → G) →₀ ℂ), Equivariant Λ s ∧
      homogeneousBoundary 3 ∘ₗ s ∘ₗ homogeneousBoundary 3 = homogeneousBoundary (G := G) 3 :=
    exists_splitting X (homogeneousComplex_free Λ) (homogeneousComplex_exact Λ)
  obtain ⟨s, hs, split⟩ := key
  have Finv : ∀ (γ : Λ) (v : (Fin 4 → G) →₀ ℂ),
      Finsupp.linearCombination ℂ f (chainAct Λ γ v) = Finsupp.linearCombination ℂ f v := by
    intro γ v
    have hcomp : (f ∘ fun x => γ • x) = f := funext fun x => hf γ x
    rw [chainAct, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain, hcomp]
  have Fd : Finsupp.linearCombination ℂ f ∘ₗ homogeneousBoundary (G := G) 4 = 0 := by
    apply Finsupp.lhom_ext
    intro x a
    have hx : Finsupp.single x a = a • Finsupp.single x (1 : ℂ) := by simp
    rw [LinearMap.zero_apply, LinearMap.comp_apply, hx, map_smul, map_smul,
      ← differentialThreeRaw_eq, hcocycle x, smul_zero]
  have hΘ : Finsupp.linearCombination ℂ (fun y => Finsupp.linearCombination ℂ f
      (s (Finsupp.single y 1))) = Finsupp.linearCombination ℂ f ∘ₗ s := by
    apply Finsupp.lhom_ext
    intro y a
    have hy : Finsupp.single y a = a • Finsupp.single y (1 : ℂ) := by simp
    rw [Finsupp.linearCombination_single, LinearMap.comp_apply, hy, map_smul, map_smul]
  refine ⟨fun x => Finsupp.linearCombination ℂ f (s (Finsupp.single x 1)), ?_, ?_⟩
  · intro γ x
    have e : (Finsupp.single (γ • x) 1 : (Fin 3 → G) →₀ ℂ) =
        chainAct Λ γ (Finsupp.single x 1) := (chainAct_single γ x 1).symm
    show Finsupp.linearCombination ℂ f (s (Finsupp.single (γ • x) 1)) =
      Finsupp.linearCombination ℂ f (s (Finsupp.single x 1))
    rw [e, hs.apply, Finv]
  · intro x
    rw [differentialTwoRaw_eq, hΘ, LinearMap.comp_apply]
    have hker : Finsupp.single x 1 - s (homogeneousBoundary 3 (Finsupp.single x 1)) ∈
        LinearMap.ker (homogeneousBoundary (G := G) 3) := by
      rw [LinearMap.mem_ker, map_sub]
      have h := LinearMap.congr_fun split (Finsupp.single x 1)
      exact sub_eq_zero.mpr h.symm
    obtain ⟨w, hw⟩ := (homogeneousComplex_exact Λ).2 3 hker
    have hw0 : Finsupp.linearCombination ℂ f (homogeneousBoundary 4 w) = 0 :=
      LinearMap.congr_fun Fd w
    have hw' : homogeneousBoundary 4 w =
        Finsupp.single x 1 - s (homogeneousBoundary 3 (Finsupp.single x 1)) := hw
    calc Finsupp.linearCombination ℂ f (s (homogeneousBoundary 3 (Finsupp.single x 1)))
        = Finsupp.linearCombination ℂ f (Finsupp.single x 1) -
            Finsupp.linearCombination ℂ f
              (Finsupp.single x 1 - s (homogeneousBoundary 3 (Finsupp.single x 1))) := by
          rw [map_sub]
          abel
      _ = Finsupp.linearCombination ℂ f (Finsupp.single x 1) := by
          rw [← hw', hw0, sub_zero]
      _ = f x := by
          rw [Finsupp.linearCombination_single, one_smul]

/-- **Three-cycles modulo `Λ` are boundaries modulo `Λ`** when `H³(Λ, ℂ) = 0`. -/
theorem mem_bdryChains_of_cycle {Λ : Subgroup G} (h : TopVanishingThree Λ) {c : Chains G 3}
    (hc : homogeneousBoundary 3 c ∈ NullChains Λ 2) : c ∈ BdryChains Λ 3 := by
  refine (mem_bdryChains_iff Λ c).mpr fun κ hκ closed => ?_
  obtain ⟨θ, hθ, hdθ⟩ := h κ hκ closed
  have hκ' : κ = differentialTwoRaw θ := (funext hdθ).symm
  rw [hκ', eval_differentialTwo]
  exact eval_null θ hθ hc

end TernaryPeriodPolynomials.BoundaryDuality.LowVanishing
