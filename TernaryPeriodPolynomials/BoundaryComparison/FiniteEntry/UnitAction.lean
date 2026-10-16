module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBad3
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBlockG

@[expose] public section


/-!
# The integral-unit action on the opposite plane vectors of the finite entry

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.
Paper: the finite-entry computation, lines ~.

For `κ ∈ GL₂(Ẑ)` and `v = (v₁, v₂) ∈ 𝔸_f²` one has the matrix identity
`blk(κ) · P(v₁, v₂) = P(w₁, w₂) · blk(S κ S)` with `P(a, b) = !![0,1,0; 1,0,0; b,a,1]`
(`planeOppositeStandardMatrix`), `S` the swap, and `(w₁, w₂) = (v₁, v₂) · κ⁻¹` (a row vector times an integral invertible matrix).
The map `v ↦ w` preserves the product Haar measure of `𝔸_f²` (normalised on `Ẑ²`) and the region `badRegion`.

* `exists_T_unit`: the statement used by the finite-entry bridge.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory TopologicalSpace
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- The row-vector action `v ↦ v · h` of an integral `2 × 2` matrix on `𝔸_f²`. -/
def rowMap (h : Matrix (Fin 2) (Fin 2) IntegralAdeles) (v : FiniteAdeles × FiniteAdeles) :
    FiniteAdeles × FiniteAdeles :=
  (v.1 * integralEmbedding (h 0 0) + v.2 * integralEmbedding (h 1 0),
    v.1 * integralEmbedding (h 0 1) + v.2 * integralEmbedding (h 1 1))

theorem rowMap_continuous (h : Matrix (Fin 2) (Fin 2) IntegralAdeles) : Continuous (rowMap h) := by
  unfold rowMap
  exact ((continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)).prodMk
    ((continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const))

theorem rowMap_add (h : Matrix (Fin 2) (Fin 2) IntegralAdeles) (v w : FiniteAdeles × FiniteAdeles) :
    rowMap h (v + w) = rowMap h v + rowMap h w := by
  refine Prod.ext ?_ ?_ <;> (simp only [rowMap, Prod.fst_add, Prod.snd_add]; ring)

/-- The row action of `g` after that of `h` is the row action of `h * g`; for `h * g = 1` it is the identity. -/
theorem rowMap_rowMap {h g : Matrix (Fin 2) (Fin 2) IntegralAdeles} (hg : h * g = 1)
    (v : FiniteAdeles × FiniteAdeles) : rowMap g (rowMap h v) = v := by
  have e : ∀ i l : Fin 2, integralEmbedding (h i 0) * integralEmbedding (g 0 l) +
      integralEmbedding (h i 1) * integralEmbedding (g 1 l) = if i = l then 1 else 0 := by
    intro i l
    have := congrArg integralEmbedding (congrFun (congrFun hg i) l)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, map_add, map_mul] at this
    rw [this]
    split_ifs <;> simp
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [ite_true, ite_false, Fin.isValue, zero_ne_one, one_ne_zero] at e00 e01 e10 e11
  refine Prod.ext ?_ ?_
  · simp only [rowMap]
    calc _ = v.1 * (integralEmbedding (h 0 0) * integralEmbedding (g 0 0) +
          integralEmbedding (h 0 1) * integralEmbedding (g 1 0)) +
          v.2 * (integralEmbedding (h 1 0) * integralEmbedding (g 0 0) +
          integralEmbedding (h 1 1) * integralEmbedding (g 1 0)) := by ring
      _ = v.1 := by rw [e00, e10]; ring
  · simp only [rowMap]
    calc _ = v.1 * (integralEmbedding (h 0 0) * integralEmbedding (g 0 1) +
          integralEmbedding (h 0 1) * integralEmbedding (g 1 1)) +
          v.2 * (integralEmbedding (h 1 0) * integralEmbedding (g 0 1) +
          integralEmbedding (h 1 1) * integralEmbedding (g 1 1)) := by ring
      _ = v.2 := by rw [e01, e11]; ring

/-- The row action of an integral matrix maps `Ẑ²` into itself. -/
theorem rowMap_mem_unit (h : Matrix (Fin 2) (Fin 2) IntegralAdeles) (v : FiniteAdeles × FiniteAdeles)
    (hv : v ∈ Set.range (integralEmbedding) ×ˢ Set.range (integralEmbedding)) :
    rowMap h v ∈ Set.range (integralEmbedding) ×ˢ Set.range (integralEmbedding) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hv
  refine ⟨⟨x * h 0 0 + y * h 1 0, ?_⟩, ⟨x * h 0 1 + y * h 1 1, ?_⟩⟩
  · simp [rowMap, hx, hy]
  · simp [rowMap, hx, hy]

/-- The row action of an integral matrix preserves the small-`3`-adic region. -/
theorem rowMap_badRegion (h : Matrix (Fin 2) (Fin 2) IntegralAdeles) (v : FiniteAdeles × FiniteAdeles)
    (hv : v ∈ badRegion) : rowMap h v ∈ badRegion := by
  have key : ∀ (a b : ℚ_[3]) (c d : IntegralAdeles), ‖a‖ < 1 → ‖b‖ < 1 →
      ‖a * finiteThree (integralEmbedding c) + b * finiteThree (integralEmbedding d)‖ < 1 := by
    intro a b c d ha hb
    have hc : ‖finiteThree (integralEmbedding c)‖ ≤ 1 := by
      rw [finiteThree_integral]; exact PadicInt.norm_le_one _
    have hd : ‖finiteThree (integralEmbedding d)‖ ≤ 1 := by
      rw [finiteThree_integral]; exact PadicInt.norm_le_one _
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖finiteThree (integralEmbedding c)‖ ≤ ‖a‖ * 1 := by gcongr
        _ < 1 := by simpa using ha
    · rw [norm_mul]
      calc ‖b‖ * ‖finiteThree (integralEmbedding d)‖ ≤ ‖b‖ * 1 := by gcongr
        _ < 1 := by simpa using hb
  obtain ⟨h1, h2⟩ := hv
  have e1 : (rowMap h v).1 = v.1 * integralEmbedding (h 0 0) + v.2 * integralEmbedding (h 1 0) := rfl
  have e2 : (rowMap h v).2 = v.1 * integralEmbedding (h 0 1) + v.2 * integralEmbedding (h 1 1) := rfl
  show ‖finiteThree (rowMap h v).1‖ < 1 ∧ ‖finiteThree (rowMap h v).2‖ < 1
  rw [e1, e2, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  exact ⟨key _ _ _ _ h1 h2, key _ _ _ _ h1 h2⟩

/-- The row action of `h` (with `h * g = 1` for an integral `g`) as a continuous additive equivalence of `𝔸_f²`. -/
def rowCAE (h g : Matrix (Fin 2) (Fin 2) IntegralAdeles) (hg : h * g = 1) (gh : g * h = 1) :
    (FiniteAdeles × FiniteAdeles) ≃ₜ+ (FiniteAdeles × FiniteAdeles) where
  toFun := rowMap h
  invFun := rowMap g
  left_inv v := rowMap_rowMap hg v
  right_inv v := rowMap_rowMap gh v
  map_add' := rowMap_add h
  continuous_toFun := rowMap_continuous h
  continuous_invFun := rowMap_continuous g

theorem rowCAE_measurePreserving (h g : Matrix (Fin 2) (Fin 2) IntegralAdeles) (hg : h * g = 1)
    (gh : g * h = 1) :
    MeasurePreserving (rowCAE h g hg gh).toHomeomorph.toMeasurableEquiv
      (finiteMeasure.prod finiteMeasure) (finiteMeasure.prod finiteMeasure) := by
  set μ : Measure (FiniteAdeles × FiniteAdeles) := finiteMeasure.prod finiteMeasure with hμ
  set Φ := rowCAE h g hg gh with hΦ
  refine ⟨Φ.continuous.measurable, ?_⟩
  let K : PositiveCompacts (FiniteAdeles × FiniteAdeles) :=
    finiteUnitCompact ×ˢ finiteUnitCompact
  have hK : (K : Set (FiniteAdeles × FiniteAdeles)) =
      Set.range integralEmbedding ×ˢ Set.range integralEmbedding := rfl
  have hpre : Φ.toHomeomorph.toMeasurableEquiv ⁻¹' (K : Set (FiniteAdeles × FiniteAdeles)) = K := by
    rw [hK]
    ext v
    simp only [Set.mem_preimage]
    constructor
    · intro hv
      have := rowMap_mem_unit g _ hv
      rwa [show rowMap g (Φ.toHomeomorph.toMeasurableEquiv v) = v from rowMap_rowMap hg v] at this
    · intro hv
      exact rowMap_mem_unit h v hv
  have hmeas : Measurable (⇑Φ) := Φ.continuous.measurable
  have : (Measure.map Φ μ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have u1 := Measure.addHaarMeasure_unique (Measure.map Φ μ) K
  have u2 := Measure.addHaarMeasure_unique μ K
  have hKm : MeasurableSet (K : Set (FiniteAdeles × FiniteAdeles)) := K.isCompact.isClosed.measurableSet
  have hval : Measure.map Φ μ K = μ K := by
    rw [Measure.map_apply hmeas hKm]
    exact congrArg μ hpre
  calc Measure.map Φ μ = Measure.map Φ μ K • Measure.addHaarMeasure K := u1
    _ = μ K • Measure.addHaarMeasure K := by rw [hval]
    _ = μ := u2.symm

/-- The swap `!![0,1;1,0]` as an element of `GL₂(Ẑ)`. -/
def swapGL : GeneralLinearGroup (Fin 2) IntegralAdeles :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The matrix identity behind `exists_T_unit`, over an arbitrary commutative ring: `blk(M) · P(v) = P(v · H) · blk(S M S)` when `H M = 1`. -/
theorem blk3_mul_planeOpposite {R : Type*} [CommRing R] (M H : Matrix (Fin 2) (Fin 2) R)
    (hHM : H * M = 1) (v : R × R) :
    blk3 M * (planeOppositeStandardMatrix v.1 v.2).val =
      (planeOppositeStandardMatrix (v.1 * H 0 0 + v.2 * H 1 0) (v.1 * H 0 1 + v.2 * H 1 1)).val *
        blk3 (!![0, 1; 1, 0] * M * !![0, 1; 1, 0]) := by
  have e : ∀ i l : Fin 2, H i 0 * M 0 l + H i 1 * M 1 l = if i = l then 1 else 0 := by
    intro i l
    have := congrFun (congrFun hHM i) l
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this
    exact this
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [ite_true, ite_false, Fin.isValue, zero_ne_one, one_ne_zero] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, planeOppositeStandardMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Fin.sum_univ_three]
  · linear_combination (-v.1) * e01 - v.2 * e11
  · linear_combination (-v.1) * e00 - v.2 * e10

/-- The block embedding `diag(g, 1)` of `GL₂(Ẑ)` into `GL₃(Ẑ)`. -/
def blkInt (g : GeneralLinearGroup (Fin 2) IntegralAdeles) : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  ⟨blk3 g.val, blk3 g⁻¹.val,
    by rw [← blk3_mul, Units.mul_inv, blk3_one],
    by rw [← blk3_mul, Units.inv_mul, blk3_one]⟩

/-- **The unit action on the opposite plane vectors.**  For `κ ∈ GL₂(Ẑ)` the row action `v ↦ v · κ⁻¹` on `𝔸_f²` is a measure preserving
measurable equivalence for the product Haar measure that preserves `badRegion`, and
`blk(κ) · P(v) = P(T v) · blk(S κ S)`. -/
theorem exists_T_unit (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    ∃ T : (FiniteAdeles × FiniteAdeles) ≃ᵐ (FiniteAdeles × FiniteAdeles),
      MeasurePreserving T (finiteMeasure.prod finiteMeasure) (finiteMeasure.prod finiteMeasure) ∧
      (∀ v, v ∈ badRegion ↔ T v ∈ badRegion) ∧
      ∀ v, ∃ k' : GeneralLinearGroup (Fin 3) IntegralAdeles,
        blkGL (GeneralLinearGroup.map integralEmbedding k) * planeOppositeStandardMatrix v.1 v.2
          = planeOppositeStandardMatrix (T v).1 (T v).2 * GeneralLinearGroup.map integralEmbedding k' := by
  have hg : k⁻¹.val * k.val = 1 := by
    simp
  have gh : k.val * k⁻¹.val = 1 := by
    simp
  refine ⟨(rowCAE k⁻¹.val k.val hg gh).toHomeomorph.toMeasurableEquiv,
    rowCAE_measurePreserving _ _ hg gh, ?_, ?_⟩
  · intro v
    refine ⟨fun hv => rowMap_badRegion _ v hv, fun hv => ?_⟩
    have := rowMap_badRegion k.val _ hv
    have hT : (rowCAE k⁻¹.val k.val hg gh).toHomeomorph.toMeasurableEquiv v = rowMap k⁻¹.val v := rfl
    rwa [hT, rowMap_rowMap hg v] at this
  · intro v
    refine ⟨blkInt (swapGL * k * swapGL), ?_⟩
    have hH : k⁻¹.val.map integralEmbedding * k.val.map integralEmbedding = 1 := by
      rw [← Matrix.map_mul, hg]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have key := blk3_mul_planeOpposite (k.val.map integralEmbedding) (k⁻¹.val.map integralEmbedding) hH v
    have hS : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) IntegralAdeles).map integralEmbedding =
        !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hR : (blkInt (swapGL * k * swapGL)).val.map integralEmbedding =
        blk3 (!![0, 1; 1, 0] * k.val.map integralEmbedding * !![0, 1; 1, 0]) := by
      change (blk3 (swapGL * k * swapGL).val).map integralEmbedding = _
      rw [blk3_map, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      change blk3 (((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) IntegralAdeles).map integralEmbedding) * _ *
        ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) IntegralAdeles).map integralEmbedding)) = _
      rw [hS]
    apply Units.ext
    change blk3 (k.val.map integralEmbedding) * (planeOppositeStandardMatrix v.1 v.2).val =
      (planeOppositeStandardMatrix _ _).val * (blkInt (swapGL * k * swapGL)).val.map integralEmbedding
    rw [hR]
    exact key

end TernaryPeriodPolynomials.Argument.BoundaryComparison
