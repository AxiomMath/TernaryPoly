module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective

@[expose] public section


/-!
# A vanishing Levi period class forces the weight vector to vanish

Let `I : L3Input σ n` be an Eichler input (a smooth holomorphic level-three vector of weight
`-(n + 3)`) and `E = I.toData stages` its sign-twisted Levi cocycle datum.  The scalar realization of
`I.vector` is a cusp form `g` of weight `n + 3` for `Γ₁(3)` (`levelThreeForm`), and by `L3PeriodAlpha`
the values `E.α(A_ℝ) 1` are the classical Eichler period cocycle of `g`, which by `L3PeriodCore`
is the parity projected, extended period cocycle `levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 g)`.
If the period map `levelPeriodMap (n + 1) 0` is injective (Eichler–Shimura), the vanishing of the
class of `A ↦ (n + 1) E.α(A_ℝ) 1` in `H¹(Γ₁'(3), Sym^{n+1})` therefore gives `g = 0`, hence
`I.vector = 0` since the dictionary `vector ↦ g` is injective.

* `l3Period_vector_eq_zero`: the statement above.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear cuspScalarWeightedRealization)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel binaryArithmeticRepresentation)

/-- **A vanishing level-three Levi period class forces the Eichler input to vanish** (given the
injectivity of the parity-projected period map). -/
theorem l3Period_vector_eq_zero {σ : CuspidalRepresentation} {n : ℕ} (I : L3Input σ n)
    (stages : AnalyticScalar.ContinuousStages σ)
    (hper : Function.Injective
      (LevelThree.LevelThreePeriodParity.levelPeriodMap (n + 1) 0))
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (I.toData stages).α
          (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) :
    I.vector = 0 := by
  have negative : I.halfWeight < 0 := by
    have := I.weight
    omega
  have hmem : I.vector ∈ MultiplicityOne.levelThreeClassicalVectors σ I.halfWeight :=
    MultiplicityOne.levelThreeClassicalVectors_mem_of_holomorphic σ I.halfWeight
      I.vector I.vector_level I.rotation
      (MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ I.halfWeight I.vector
        I.vector_level I.rotation I.holomorphic 1)
  have wt : -2 * I.halfWeight = ((n + 1 : ℕ) : ℤ) + 2 := by
    have := I.weight
    push_cast
    omega
  obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) wt
    (MultiplicityOne.levelThreeForm σ I.halfWeight negative I.vector hmem)
  have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector :=
    hg.trans (MultiplicityOne.levelThreeForm_coe σ I.halfWeight negative I.vector hmem)
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : UpperHalfPlane → ℂ) :=
    LevelThree.LevelThreePeriodCocycle.form_holo g
  have hα : L3PeriodFormula (I.toData stages) ⇑g := fun K =>
    l3p_alpha_one_eq_formula I stages hf hfd K
  have hmap0 := l3p_levelPeriodMap_eq_zero (I.toData stages) g hα hcob
  have hg0 : g = 0 := hper (by rw [hmap0, map_zero])
  by_contra hv0
  obtain ⟨pt, hpt⟩ := MultiplicityOne.levelThree_scalar_exists_nonzero σ
    I.central_positive I.halfWeight I.vector hmem hv0
  apply hpt
  have e1 : (g : UpperHalfPlane → ℂ) pt =
      cuspScalarWeightedRealization σ I.halfWeight I.vector 1 pt := congrFun hf pt
  rw [← e1, hg0]
  try simp

end TernaryPeriodPolynomials.SourceConstruction

end
