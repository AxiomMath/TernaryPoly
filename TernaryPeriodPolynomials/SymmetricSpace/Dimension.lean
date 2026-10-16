module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient

@[expose] public section


/-!
# The dimension of `𝒳` is `5 = 6 - 1`

Formalized by Claude Sonnet 5.5.

What is proved (linear algebra and a global chart onto an open subset of a five-dimensional vector space; **a `ChartedSpace`/smooth-manifold structure on `𝒳` and the equivariance of the smooth structure are NOT formalized**):

* `finrank_symmetric`: the real symmetric `3 × 3` matrices have dimension `6` (`TernaryPoly.SymmetricSpaceOrientation.coordinatesEquiv`);
* `finrank_tangent : finrank (symmetric trace-zero matrices) = 5`; this is the tangent space at the base point of `𝒳 = {Q > 0}/ℝ_{>0}` (the scaling direction `Q` itself is removed by the trace), `tangentMat` is the same
  subspace inside all `3 × 3` matrices;
* `chartEquiv`, `chartHomeo`: the trace-one slice `Space` (a set of representatives of `𝒳`, `SymmetricSpaceQuotient.spaceEquiv : Space ≃ 𝒳`) is homeomorphic, by `S ↦ S - (1/3) I`, to the subset
  `{T ∈ tangentMat : T + I/3 > 0}` of the five-dimensional real vector space `tangentMat`, and this subset is open (`isOpen_chartImage`, by compactness of the unit sphere: `posDef_iff_sphere`),
  so `𝒳` (with the topology transported through `spaceEquiv`) is homeomorphic to an open subset of `ℝ⁵`: a five-dimensional topological manifold with a global chart.
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace

open TernaryPoly.SymmetricSpaceOrientation (symmetricSubmodule coordinatesEquiv)

/-- The trace on the real symmetric matrices. -/
def symTrace : symmetricSubmodule →ₗ[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).comp symmetricSubmodule.subtype

/-- Trace-zero symmetric matrices: the tangent space of the symmetric space. -/
def tangentSym : Submodule ℝ symmetricSubmodule := LinearMap.ker symTrace

theorem finrank_symmetric : Module.finrank ℝ symmetricSubmodule = 6 := by
  rw [LinearEquiv.finrank_eq coordinatesEquiv, Module.finrank_fin_fun]

theorem symTrace_surjective : Function.Surjective symTrace := by
  intro r
  refine ⟨⟨(r / 3) • (1 : Mat), (Matrix.isSymm_one).smul _⟩, ?_⟩
  change ((r / 3) • (1 : Mat)).trace = r
  rw [trace_smul, trace_one]
  simp

/-- **(b):** the tangent space of `𝒳 = {Q > 0}/ℝ_{>0}` (symmetric trace-zero matrices) has dimension `5 = 6 - 1`. -/
theorem finrank_tangent : Module.finrank ℝ tangentSym = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker symTrace
  rw [LinearMap.range_eq_top.mpr symTrace_surjective, finrank_top, Module.finrank_self,
    finrank_symmetric] at h
  change 1 + Module.finrank ℝ (LinearMap.ker symTrace) = 6 at h
  change Module.finrank ℝ (LinearMap.ker symTrace) = 5
  omega

/-- The same subspace inside all `3 × 3` real matrices. -/
def tangentMat : Submodule ℝ Mat := tangentSym.map symmetricSubmodule.subtype

theorem mem_tangentMat_iff (T : Mat) : T ∈ tangentMat ↔ Tᵀ = T ∧ T.trace = 0 := by
  constructor
  · rintro ⟨⟨S, hS⟩, hmem, rfl⟩
    exact ⟨hS, hmem⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨T, h1⟩, h2, rfl⟩

theorem finrank_tangentMat : Module.finrank ℝ tangentMat = 5 := by
  rw [← finrank_tangent]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective symmetricSubmodule.subtype
    (Submodule.injective_subtype _) tangentSym)).symm

open TernaryPoly.SymmetricSpacePositive in
theorem chart_mem (S : Space) : S.1 - (1 / 3 : ℝ) • (1 : Mat) ∈ tangentMat := by
  rw [mem_tangentMat_iff]
  have hS : S.1ᵀ = S.1 := by
    simpa [conjTranspose_eq_transpose_of_trivial] using S.2.1.isHermitian.eq
  refine ⟨?_, ?_⟩
  · rw [transpose_sub, transpose_smul, transpose_one, hS]
  · rw [trace_sub, trace_smul, trace_one, S.2.2]
    simp

open TernaryPoly.SymmetricSpacePositive in
/-- **(b), a global chart of the trace-one slice:** `S ↦ S - I/3` identifies `Space` with `{T ∈ tangentMat : T + I/3 positive definite}`. -/
def chartEquiv : Space ≃ {T : tangentMat // (T.1 + (1 / 3 : ℝ) • (1 : Mat)).PosDef} where
  toFun S := ⟨⟨S.1 - (1 / 3 : ℝ) • (1 : Mat), chart_mem S⟩, by simpa using S.2.1⟩
  invFun T := ⟨T.1.1 + (1 / 3 : ℝ) • (1 : Mat), T.2, by
    have h := (mem_tangentMat_iff T.1.1).mp T.1.2
    rw [trace_add, h.2, trace_smul, trace_one]
    simp⟩
  left_inv S := by apply Subtype.ext; simp
  right_inv T := by apply Subtype.ext; apply Subtype.ext; simp

open TernaryPoly.SymmetricSpacePositive in
/-- The chart is a homeomorphism (subspace topologies from the matrix topology). -/
def chartHomeo : Space ≃ₜ {T : tangentMat // (T.1 + (1 / 3 : ℝ) • (1 : Mat)).PosDef} where
  toEquiv := chartEquiv
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_subtype_val.sub continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_subtype_val).add continuous_const


/-- A symmetric real ternary matrix is positive definite iff the quadratic form is positive on the unit sphere. -/
theorem posDef_iff_sphere (A : Mat) (hA : Aᵀ = A) :
    A.PosDef ↔ ∀ x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1, 0 < x ⬝ᵥ A *ᵥ x := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    simpa using h hx0
  · intro h
    refine ⟨?_, fun x hx => ?_⟩
    · simpa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
        simp [norm_smul, hn.ne']
      have := h _ hs
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
      have h2 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
      have : 0 < x ⬝ᵥ A *ᵥ x := by
        by_contra hneg
        have hle : x ⬝ᵥ A *ᵥ x ≤ 0 := not_lt.mp hneg
        nlinarith
      simpa using this

/-- **The image of the chart is open in the five-dimensional vector space `tangentMat`.**  With `chartHomeo`, the trace-one slice `Space` (equivalently `𝒳` with the topology transported by
`spaceEquiv`) is homeomorphic to an open subset of a real vector space of dimension five (`finrank_tangentMat`). -/
theorem isOpen_chartImage :
    IsOpen {T : tangentMat | (T.1 + (1 / 3 : ℝ) • (1 : Mat)).PosDef} := by
  have hsym : ∀ T : tangentMat, (T.1 + (1 / 3 : ℝ) • (1 : Mat))ᵀ = T.1 + (1 / 3 : ℝ) • 1 := by
    intro T
    rw [transpose_add, transpose_smul, transpose_one, ((mem_tangentMat_iff T.1).mp T.2).1]
  have hset : {T : tangentMat | (T.1 + (1 / 3 : ℝ) • (1 : Mat)).PosDef} =
      {T | ∀ y ∈ Metric.sphere (0 : Fin 3 → ℝ) 1, 0 < y ⬝ᵥ (T.1 + (1 / 3 : ℝ) • 1) *ᵥ y} := by
    ext T
    exact posDef_iff_sphere _ (hsym T)
  rw [hset, isOpen_iff_mem_nhds]
  intro T0 hT0
  have hK : IsCompact (Metric.sphere (0 : Fin 3 → ℝ) 1) := isCompact_sphere _ _
  exact hK.eventually_forall_of_forall_eventually (x₀ := T0)
    (P := fun T y => 0 < y ⬝ᵥ (T.1 + (1 / 3 : ℝ) • 1) *ᵥ y) (fun y hy => by
      have hc : Continuous (fun z : tangentMat × (Fin 3 → ℝ) =>
          z.2 ⬝ᵥ (z.1.1 + (1 / 3 : ℝ) • 1) *ᵥ z.2) := by fun_prop
      exact (hc.continuousAt.eventually (lt_mem_nhds (by simpa using hT0 y hy))).mono fun z hz => hz)

end TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace
