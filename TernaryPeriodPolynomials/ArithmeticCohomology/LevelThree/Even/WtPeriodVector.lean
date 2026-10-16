module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPeriodAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodCore

@[expose] public section


/-!
# A vanishing Levi period class forces the weight vector to vanish, for every weight

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twin of `L3PeriodVector` for `I : L3InputWt σ n` (a smooth holomorphic level-three vector of integer
rotation weight `wt = -(n + 3)`, with no parity hypothesis on `n`).  The scalar realization of
`I.vector` is a cusp form `g` of weight `n + 3` for `Γ₁(3)` (`levelThreeFormWt`), and by
`WtPeriodAlpha` the values `E.α(A_ℝ) 1` of `E = I.toData stages` are the classical Eichler period
cocycle of `g`.  If the period map `levelPeriodMap (n + 1) 0` is injective (Eichler–Shimura), the
vanishing of the class of `A ↦ (n + 1) E.α(A_ℝ) 1` in `H¹(Γ₁'(3), Sym^{n+1})` gives `g = 0`, hence
`I.vector = 0` since the dictionary `vector ↦ g` is injective.

* `l3Period_vector_eq_zeroWt`: the statement above.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel binaryArithmeticRepresentation)
open TernaryPeriodPolynomials.SourceConstruction
  (L3PeriodFormula l3p_levelPeriodMap_eq_zero l3p_exists_S_cast)

/-- **A vanishing level-three Levi period class forces the weight-generic Eichler input to
vanish** (given the injectivity of the parity-projected period map). -/
theorem l3Period_vector_eq_zeroWt {σ : CuspidalRepresentation} {n : ℕ} (I : L3InputWt σ n)
    (stages : AnalyticScalar.ContinuousStages σ)
    (hper : Function.Injective
      (LevelThree.LevelThreePeriodParity.levelPeriodMap (n + 1) 0))
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (I.toData stages).α
          (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) :
    I.vector = 0 := by
  have negative : I.wt < 0 := by
    have := I.weight
    omega
  have hmem : I.vector ∈ levelThreeClassicalVectorsWt σ I.wt := by
    refine ⟨I.vector_level, I.rotation, UpperHalfPlane.mdifferentiable_iff.mpr ?_⟩
    apply (cuspScalarWeightedRealization_holomorphicWt σ stages I.wt I.vector I.fixedLevel
      I.holomorphic 1).congr
    intro point positive
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
    rfl
  have weight : -I.wt = ((n + 1 : ℕ) : ℤ) + 2 := by
    have := I.weight
    push_cast
    omega
  obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) weight
    (levelThreeFormWt σ I.wt negative I.vector hmem)
  have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt σ I.wt 1 I.vector :=
    hg.trans (levelThreeForm_coeWt σ I.wt negative I.vector hmem)
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : UpperHalfPlane → ℂ) :=
    LevelThree.LevelThreePeriodCocycle.form_holo g
  have hα : L3PeriodFormula (I.toData stages) ⇑g := fun K =>
    l3p_alpha_one_eq_formulaWt I stages hf hfd K
  have hmap0 := l3p_levelPeriodMap_eq_zero (I.toData stages) g hα hcob
  have hg0 : g = 0 := hper (by rw [hmap0, map_zero])
  by_contra hv0
  obtain ⟨pt, hpt⟩ := levelThree_scalar_exists_nonzeroWt σ I.central_positive I.wt I.vector hmem
    hv0
  apply hpt
  have e1 : (g : UpperHalfPlane → ℂ) pt = cuspScalarWeightedRealizationWt σ I.wt I.vector 1 pt :=
    congrFun hf pt
  rw [← e1]
  simp [hg0]

end TernaryPeriodPolynomials.EvenLevelThree

end
