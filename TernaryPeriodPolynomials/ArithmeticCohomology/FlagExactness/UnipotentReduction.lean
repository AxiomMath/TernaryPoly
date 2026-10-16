module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnipotentStabilizer
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.HomogeneousCorestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.ConditionalFlagExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.FlagStabilizer

@[expose] public section


/-!
# Reduction of plane stabilizer exactness to the unipotent stabilizer

Fix a plane source cocycle and a complete flag `q`. Suppose that, on the unipotent
stabilizer `unipotentStabilizer q`, each rationally translated flag cochain
`x ↦ c(x)(n(r)·q⁻¹)` is cohomologous to the untranslated one `x ↦ c(x)(q⁻¹)`. Then
`FlagExact` holds at `q`.

The steps are:
* symmetrize in `r ↦ -r`, which makes the cochain equivariant for the full stabilizer;
* corestrict from the finite-index unipotent part (`exists_primitive_of_finiteIndex`);
* pass to inhomogeneous cochains and apply `flagExact_of_translateInvariance`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GraphPieces

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- Real vertices of rational vertices. -/
def realVertices {k : ℕ} (x : Fin k → RationalGL3) : Fin k → RealGL3 :=
  fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)

theorem realVertices_mul {k : ℕ} (γ : RationalGL3) (x : Fin k → RationalGL3) :
    realVertices (fun i => γ * x i) =
      fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) γ * realVertices x i := by
  funext i
  exact map_mul _ _ _

/-- Translated flag evaluation is equivariant for the unipotent stabilizer. -/
theorem planeTranslate_unipotent_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (t : ℝ)
    (γ : unipotentStabilizer q) (x : Fin 3 → RationalGL3) :
    planeTranslate source q t (realVertices (fun i => γ.val * x i)) =
      rationalCoefficientComponent degree data.chi γ.val (planeTranslate source q t (realVertices x)) := by
  obtain ⟨hedge, hdiag⟩ := γ.property
  obtain ⟨h10, h20, h21⟩ := borel_entries (edgeStabilizer_borel q hedge)
  have h00 : (q⁻¹ * γ.val * q).val 0 0 ≠ 0 := by rw [hdiag 0]; norm_num
  have key := translatedEvaluation_stabilizer data source isSource q ⟨γ.val, hedge.1⟩ h00 h10 h20 h21
    t (realVertices x)
  rw [hdiag 0, hdiag 1] at key
  simp only [div_one, Rat.cast_one, mul_one] at key
  rw [planeTranslate, planeTranslate, realVertices_mul]
  exact key

/-- The translated flag cochain on the unipotent stabilizer. -/
def planeTranslateCochain {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (t : ℝ) :
    cochains (unipotentStabilizer q) (rationalCoefficientComponent degree data.chi) 2 :=
  ⟨fun x => planeTranslate source q t (realVertices x),
    fun γ x => planeTranslate_unipotent_equivariant data source isSource q t γ x⟩

/-- Translated flag evaluation under the full stabilizer, up to the sign of the translate. -/
theorem planeTranslate_stabilizer_sign {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (γ : edgeStabilizer q) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ (s : ℝ) (x : Fin 3 → RationalGL3),
      planeTranslate source q s (realVertices (fun i => γ.val * x i)) =
        rationalCoefficientComponent degree data.chi γ.val
          (planeTranslate source q (s * (ε : ℝ)) (realVertices x)) := by
  obtain ⟨ε, hε, key⟩ := translatedEvaluation_flagStabilizer data source isSource q ⟨γ.val, γ.property.1⟩
    (MulAction.mem_stabilizer_iff.mp γ.property.2)
  refine ⟨ε, hε, fun s x => ?_⟩
  rw [planeTranslate, planeTranslate, realVertices_mul]
  exact key s _

/-- The symmetrized translate difference is equivariant for the full stabilizer. -/
theorem planeSymmetric_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (t : ℝ)
    (γ : edgeStabilizer q) (x : Fin 3 → RationalGL3) :
    (1 / 2 : ℂ) • (planeTranslate source q t (realVertices (fun i => γ.val * x i)) +
      planeTranslate source q (-t) (realVertices (fun i => γ.val * x i))) -
      planeTranslate source q 0 (realVertices (fun i => γ.val * x i)) =
    rationalCoefficientComponent degree data.chi γ.val
      ((1 / 2 : ℂ) • (planeTranslate source q t (realVertices x) +
        planeTranslate source q (-t) (realVertices x)) - planeTranslate source q 0 (realVertices x)) := by
  obtain ⟨ε, hε, key⟩ := planeTranslate_stabilizer_sign data source isSource q γ
  rw [key t, key (-t), key 0, map_sub, map_smul, map_add]
  rcases hε with h | h <;> subst h
  · simp only [Rat.cast_one, mul_one]
  · simp only [Rat.cast_neg, Rat.cast_one, mul_neg_one, neg_neg, neg_zero]
    rw [add_comm (rationalCoefficientComponent degree data.chi γ.val (planeTranslate source q (-t) _))]

/-- The symmetrized difference cochain on the full stabilizer. -/
def planeSymmetricDifference {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (t : ℝ) :
    cochains (edgeStabilizer q) (rationalCoefficientComponent degree data.chi) 2 :=
  ⟨fun x => (1 / 2 : ℂ) • (planeTranslate source q t (realVertices x) +
      planeTranslate source q (-t) (realVertices x)) - planeTranslate source q 0 (realVertices x),
    fun γ x => planeSymmetric_equivariant data source isSource q t γ x⟩

/-- **Reduction to the unipotent stabilizer** (plane sources). -/
theorem flagExact_of_unipotentInvariance {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3)
    (invariance : ∀ r : ℚ, ∃ primitive : cochains (unipotentStabilizer q)
        (rationalCoefficientComponent degree data.chi) 1,
      ∀ x, (differentialOne _ _ primitive).val x =
        (planeTranslateCochain data source isSource q r).val x -
          (planeTranslateCochain data source isSource q 0).val x) :
    EndpointReduction.FlagExact data source q := by
  apply flagExact_of_translateInvariance data source isSource q
  intro r
  obtain ⟨P₁, h₁⟩ := invariance r
  obtain ⟨P₂, h₂⟩ := invariance (-r)
  -- a primitive on the unipotent stabilizer of the symmetrized difference
  have hsub : ∀ x, (differentialOne _ _ ((1 / 2 : ℂ) • (P₁ + P₂))).val x =
      (planeSymmetricDifference data source isSource q r).val x := by
    intro x
    rw [map_smul, map_add]
    change (1 / 2 : ℂ) • ((differentialOne _ _ P₁).val x + (differentialOne _ _ P₂).val x) = _
    rw [h₁, h₂]
    simp only [planeTranslateCochain, planeSymmetricDifference, Rat.cast_neg]
    module
  have : Finite (Quotient (QuotientGroup.rightRel ((unipotentStabilizer q).subgroupOf (edgeStabilizer q)))) :=
    unipotentStabilizer_finite q
  obtain ⟨P, hP⟩ := exists_primitive_of_finiteIndex (edgeStabilizer q) (unipotentStabilizer q)
    (rationalCoefficientComponent degree data.chi) (planeSymmetricDifference data source isSource q r)
    ((1 / 2 : ℂ) • (P₁ + P₂)) hsub
  refine ⟨fun γ => P.val ![1, γ.val], fun γ₁ γ₂ => ?_⟩
  have hd := hP ![1, γ₁.val, γ₁.val * γ₂.val]
  change P.val ![γ₁.val, γ₁.val * γ₂.val] - P.val ![1, γ₁.val * γ₂.val] + P.val ![1, γ₁.val] =
    (1 / 2 : ℂ) • (planeTranslate source q r (pairVertices γ₁.val γ₂.val) +
      planeTranslate source q (-(r : ℝ)) (pairVertices γ₁.val γ₂.val)) -
      planeTranslate source q 0 (pairVertices γ₁.val γ₂.val) at hd
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
