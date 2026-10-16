module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# `realize` on finite-dimensional spaces of smooth vectors

The trusted `CuspidalRepresentation.realize` is only linear. On a finite-dimensional
subspace `E` of smooth vectors, however, every evaluation `u ↦ realize u x` is automatically
continuous. Hence `realize` commutes with Bochner integrals of `E`-valued families, it is
uniformly bounded on the unit ball of `E`, and it commutes with derivatives of differentiable
`E`-valued curves. For a `K`-finite vector these give the compatibility of `realize` with the
compact Lie algebra and with `K`-type projections inside its `K`-span.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open MeasureTheory GeneralEisenstein

namespace TernaryPeriodPolynomials.ArchimedeanConstant

variable (σ : CuspidalRepresentation) (E : Submodule ℂ σ.H) [FiniteDimensional ℂ E]
  (hE : E ≤ σ.smooth)

/-- Evaluation of the realization at a point, as a continuous functional on `E`. -/
def finiteRealizeEval (x : BinaryAdelicGL) : E →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => σ.realize ⟨e.val, hE e.property⟩ x
      map_add' := by
        intro a b
        have : (⟨(a + b : E).val, hE (a + b).property⟩ : σ.smooth) =
            ⟨a.val, hE a.property⟩ + ⟨b.val, hE b.property⟩ := rfl
        rw [this, map_add]
        rfl
      map_smul' := by
        intro c a
        have : (⟨(c • a : E).val, hE (c • a).property⟩ : σ.smooth) =
            c • (⟨a.val, hE a.property⟩ : σ.smooth) := rfl
        rw [this, map_smul]
        rfl }

theorem finiteRealizeEval_apply (x : BinaryAdelicGL) (e : E) :
    finiteRealizeEval σ E hE x e = σ.realize ⟨e.val, hE e.property⟩ x := rfl

/-- The coercion of an `E`-valued Bochner integral is the `H`-valued integral. -/
theorem coe_integral_finite {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → E)
    (hf : Integrable f μ) : ((∫ a, f a ∂μ : E) : σ.H) = ∫ a, (f a : σ.H) ∂μ := by
  have := (E.subtypeL).integral_comp_comm hf
  simpa using this.symm

/-- **`realize` commutes with integrals of families in a finite-dimensional space.** -/
theorem realize_integral_finite {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → E)
    (hf : Integrable f μ) (x : BinaryAdelicGL) :
    σ.realize ⟨(∫ a, f a ∂μ : E).val, hE (∫ a, f a ∂μ : E).property⟩ x =
      ∫ a, σ.realize ⟨(f a).val, hE (f a).property⟩ x ∂μ := by
  rw [← finiteRealizeEval_apply σ E hE x,
    ← (finiteRealizeEval σ E hE x).integral_comp_comm hf]
  rfl

/-- **Uniform bound.** On a finite-dimensional space of smooth vectors, the realization is
bounded by a constant times the Hilbert norm, uniformly over the whole group. -/
theorem realize_uniform_bound_finite :
    ∃ C : ℝ, ∀ (e : E) (x : BinaryAdelicGL), ‖σ.realize ⟨e.val, hE e.property⟩ x‖ ≤ C * ‖e‖ := by
  classical
  let b := Module.finBasis ℂ E
  have hb : ∀ i, ∃ C : ℝ, ∀ x, ‖σ.realize ⟨(b i).val, hE (b i).property⟩ x‖ ≤ C :=
    fun i => σ.bounded _
  choose C hC using hb
  -- the coordinate functionals are continuous on the finite-dimensional space
  let coord : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖coord i‖ * max (C i) 0, ?_⟩
  intro e x
  have he : e = ∑ i, b.coord i e • b i := (b.sum_repr e).symm
  have hexp : σ.realize ⟨e.val, hE e.property⟩ x =
      ∑ i, b.coord i e * σ.realize ⟨(b i).val, hE (b i).property⟩ x := by
    rw [← finiteRealizeEval_apply σ E hE x]
    conv_lhs => rw [he]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 : ‖b.coord i e‖ ≤ ‖coord i‖ * ‖e‖ := (coord i).le_opNorm e
  have h2 : ‖σ.realize ⟨(b i).val, hE (b i).property⟩ x‖ ≤ max (C i) 0 :=
    (hC i x).trans (le_max_left _ _)
  calc ‖b.coord i e‖ * ‖σ.realize ⟨(b i).val, hE (b i).property⟩ x‖
      ≤ (‖coord i‖ * ‖e‖) * max (C i) 0 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖coord i‖ * max (C i) 0 * ‖e‖ := by ring

/-- **Derivatives.** If a curve of smooth vectors stays in `E` and is differentiable there, then
the derivative of its realization at any point is the realization of its derivative. -/
theorem realize_hasDerivAt_finite (γ : ℝ → E) (γ' : E) (t : ℝ) (hγ : HasDerivAt γ γ' t)
    (x : BinaryAdelicGL) :
    HasDerivAt (fun s => σ.realize ⟨(γ s).val, hE (γ s).property⟩ x)
      (σ.realize ⟨γ'.val, hE γ'.property⟩ x) t := by
  have := (((finiteRealizeEval σ E hE x).restrictScalars ℝ).hasFDerivAt
    (x := γ t)).comp_hasDerivAt t hγ
  simp only [ContinuousLinearMap.coe_restrictScalars'] at this
  exact this

include hE in
/-- **`K`-type averages of a `K`-finite vector.** If all translates `π(ι k) v` lie in a
finite-dimensional space `E` of smooth vectors, then realizing a continuous average of them is
the average of the right translates of the realized function. -/
theorem realize_average_finite {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (ι : K → BinaryAdelicGL) (c : K → ℂ) (hc : Continuous c) (v : σ.smooth)
    (hcont : Continuous fun k => σ.π (ι k) v.val)
    (hv : ∀ k, σ.π (ι k) v.val ∈ E) (x : BinaryAdelicGL) :
    ∃ w : σ.smooth, w.val = ∫ k, c k • σ.π (ι k) v.val ∂μ ∧
      σ.realize w x = ∫ k, c k * σ.realize v (x * ι k) ∂μ := by
  let F : K → E := fun k => c k • ⟨σ.π (ι k) v.val, hv k⟩
  have hF : Continuous F :=
    hc.smul (Continuous.subtype_mk hcont _)
  have hint : Integrable F μ := hF.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace F)
  refine ⟨⟨(∫ k, F k ∂μ : E).val, hE (∫ k, F k ∂μ : E).property⟩, ?_, ?_⟩
  · change ((∫ k, F k ∂μ : E) : σ.H) = _
    rw [coe_integral_finite σ E μ F hint]
    rfl
  · rw [realize_integral_finite σ E hE μ F hint x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have hmem : (⟨(F k).val, hE (F k).property⟩ : σ.smooth) =
        c k • ⟨σ.π (ι k) v.val, σ.smooth_stable (ι k) v.val v.property⟩ := rfl
    change σ.realize ⟨(F k).val, hE (F k).property⟩ x = _
    rw [hmem, map_smul, Pi.smul_apply, smul_eq_mul, σ.equivariant]

end TernaryPeriodPolynomials.ArchimedeanConstant
