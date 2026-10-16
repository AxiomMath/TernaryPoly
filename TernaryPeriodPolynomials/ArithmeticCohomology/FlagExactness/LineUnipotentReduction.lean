module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnipotentReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineConditionalFlagExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineBorelTranslate

@[expose] public section


/-!
# Reduction of line stabilizer exactness to the unipotent stabilizer

The line-side analogue of `UnipotentReduction`: if on `unipotentStabilizer q` every rationally
translated line flag cochain is cohomologous to the untranslated one, then `FlagExact` holds at
`q` for the line source.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GraphPieces

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- Translated flag evaluation is equivariant for the unipotent stabilizer. -/
theorem lineTranslate_unipotent_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (t : ℝ)
    (γ : unipotentStabilizer q) (x : Fin 3 → RationalGL3) :
    lineTranslate source q t (realVertices (fun i => γ.val * x i)) =
      rationalCoefficientComponent degree data.chi γ.val (lineTranslate source q t (realVertices x)) := by
  obtain ⟨hedge, hdiag⟩ := γ.property
  obtain ⟨h10, h20, h21⟩ := borel_entries (edgeStabilizer_borel q hedge)
  have h00 : (q⁻¹ * γ.val * q).val 0 0 ≠ 0 := by rw [hdiag 0]; norm_num
  have h11 : (q⁻¹ * γ.val * q).val 1 1 ≠ 0 := by rw [hdiag 1]; norm_num
  have key := lineTranslatedEvaluation_stabilizer data source isSource q ⟨γ.val, hedge.1⟩ h00 h11
    h10 h20 h21 t (realVertices x)
  rw [hdiag 1, hdiag 2] at key
  simp only [div_one, Rat.cast_one, mul_one] at key
  rw [lineTranslate, lineTranslate, realVertices_mul]
  exact key

/-- The translated flag cochain on the unipotent stabilizer. -/
def lineTranslateCochain {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (t : ℝ) :
    cochains (unipotentStabilizer q) (rationalCoefficientComponent degree data.chi) 2 :=
  ⟨fun x => lineTranslate source q t (realVertices x),
    fun γ x => lineTranslate_unipotent_equivariant data source isSource q t γ x⟩

/-- Translated flag evaluation under the full stabilizer, up to the sign of the translate. -/
theorem lineTranslate_stabilizer_sign {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (γ : edgeStabilizer q) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ (s : ℝ) (x : Fin 3 → RationalGL3),
      lineTranslate source q s (realVertices (fun i => γ.val * x i)) =
        rationalCoefficientComponent degree data.chi γ.val
          (lineTranslate source q (s * (ε : ℝ)) (realVertices x)) := by
  obtain ⟨ε, hε, key⟩ := lineTranslatedEvaluation_flagStabilizer data source isSource q ⟨γ.val, γ.property.1⟩
    (MulAction.mem_stabilizer_iff.mp γ.property.2)
  refine ⟨ε, hε, fun s x => ?_⟩
  rw [lineTranslate, lineTranslate, realVertices_mul]
  exact key s _

/-- The symmetrized translate difference is equivariant for the full stabilizer. -/
theorem lineSymmetric_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (t : ℝ)
    (γ : edgeStabilizer q) (x : Fin 3 → RationalGL3) :
    (1 / 2 : ℂ) • (lineTranslate source q t (realVertices (fun i => γ.val * x i)) +
      lineTranslate source q (-t) (realVertices (fun i => γ.val * x i))) -
      lineTranslate source q 0 (realVertices (fun i => γ.val * x i)) =
    rationalCoefficientComponent degree data.chi γ.val
      ((1 / 2 : ℂ) • (lineTranslate source q t (realVertices x) +
        lineTranslate source q (-t) (realVertices x)) - lineTranslate source q 0 (realVertices x)) := by
  obtain ⟨ε, hε, key⟩ := lineTranslate_stabilizer_sign data source isSource q γ
  rw [key t, key (-t), key 0, map_sub, map_smul, map_add]
  rcases hε with h | h <;> subst h
  · simp only [Rat.cast_one, mul_one]
  · simp only [Rat.cast_neg, Rat.cast_one, mul_neg_one, neg_neg, neg_zero]
    rw [add_comm (rationalCoefficientComponent degree data.chi γ.val (lineTranslate source q (-t) _))]

/-- The symmetrized difference cochain on the full stabilizer. -/
def lineSymmetricDifference {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (t : ℝ) :
    cochains (edgeStabilizer q) (rationalCoefficientComponent degree data.chi) 2 :=
  ⟨fun x => (1 / 2 : ℂ) • (lineTranslate source q t (realVertices x) +
      lineTranslate source q (-t) (realVertices x)) - lineTranslate source q 0 (realVertices x),
    fun γ x => lineSymmetric_equivariant data source isSource q t γ x⟩

/-- **Reduction to the unipotent stabilizer** (line sources). -/
theorem line_flagExact_of_unipotentInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3)
    (invariance : ∀ r : ℚ, ∃ primitive : cochains (unipotentStabilizer q)
        (rationalCoefficientComponent degree data.chi) 1,
      ∀ x, (differentialOne _ _ primitive).val x =
        (lineTranslateCochain data source isSource q r).val x -
          (lineTranslateCochain data source isSource q 0).val x) :
    EndpointReduction.FlagExact data source q := by
  apply line_flagExact_of_translateInvariance data source isSource q
  intro r
  obtain ⟨P₁, h₁⟩ := invariance r
  obtain ⟨P₂, h₂⟩ := invariance (-r)
  -- a primitive on the unipotent stabilizer of the symmetrized difference
  have hsub : ∀ x, (differentialOne _ _ ((1 / 2 : ℂ) • (P₁ + P₂))).val x =
      (lineSymmetricDifference data source isSource q r).val x := by
    intro x
    rw [map_smul, map_add]
    change (1 / 2 : ℂ) • ((differentialOne _ _ P₁).val x + (differentialOne _ _ P₂).val x) = _
    rw [h₁, h₂]
    simp only [lineTranslateCochain, lineSymmetricDifference, Rat.cast_neg]
    module
  have : Finite (Quotient (QuotientGroup.rightRel ((unipotentStabilizer q).subgroupOf (edgeStabilizer q)))) :=
    unipotentStabilizer_finite q
  obtain ⟨P, hP⟩ := exists_primitive_of_finiteIndex (edgeStabilizer q) (unipotentStabilizer q)
    (rationalCoefficientComponent degree data.chi) (lineSymmetricDifference data source isSource q r)
    ((1 / 2 : ℂ) • (P₁ + P₂)) hsub
  refine ⟨fun γ => P.val ![1, γ.val], fun γ₁ γ₂ => ?_⟩
  have hd := hP ![1, γ₁.val, γ₁.val * γ₂.val]
  change P.val ![γ₁.val, γ₁.val * γ₂.val] - P.val ![1, γ₁.val * γ₂.val] + P.val ![1, γ₁.val] =
    (1 / 2 : ℂ) • (lineTranslate source q r (pairVertices γ₁.val γ₂.val) +
      lineTranslate source q (-(r : ℝ)) (pairVertices γ₁.val γ₂.val)) -
      lineTranslate source q 0 (pairVertices γ₁.val γ₂.val) at hd
  have heq := P.property γ₁ ![1, γ₂.val]
  have hfun : (fun i => γ₁.val * (![1, γ₂.val] : Fin 2 → RationalGL3) i) = ![γ₁.val, γ₁.val * γ₂.val] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at heq
  change rationalCoefficientComponent degree data.chi γ₁.val (P.val ![1, γ₂.val]) -
    P.val ![1, (γ₁ * γ₂).val] + P.val ![1, γ₁.val] = _
  rw [← heq]
  exact hd

end TernaryPeriodPolynomials.FlagExactness
