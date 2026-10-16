module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartition

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter Function SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology Manifold

/-- The ambient zero extension of an open-submanifold scalar vanishes near every interior
point outside its relative closed support. -/
theorem openScalar_eventually_zero (O : TopologicalSpace.Opens OrbitSpace) (f : O → ℝ)
    (q : O) (hq : q ∉ tsupport f) : openScalar O f =ᶠ[𝓝 (q : OrbitSpace)] 0 := by
  have hf : f =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
  change ∀ᶠ x in 𝓝 q, f x = 0 at hf
  rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq q]
  change ∀ᶠ x in Filter.map Subtype.val (𝓝 q), openScalar O f x = 0
  simpa only [Filter.eventually_map, openScalar_apply, Pi.zero_apply] using hf

/-- Two actual smooth quotient functions partition the open union and vanish locally near
the wrong side. Their construction uses the real manifold partition of unity on the union. -/
theorem exists_two_local_cutoffs {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V) :
    ∃ φ ψ : OrbitSpace → ℝ,
      ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ (U ∪ V) ∧
      ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ ψ (U ∪ V) ∧
      (∀ q ∈ U ∪ V, φ q + ψ q = 1) ∧
      (∀ q ∈ U ∪ V, q ∉ U → φ =ᶠ[𝓝 q] 0) ∧
      (∀ q ∈ U ∪ V, q ∉ V → ψ =ᶠ[𝓝 q] 0) := by
  obtain ⟨f, hf⟩ := exists_union_partition hU hV
  let O := unionOpen U V hU hV
  refine ⟨openScalar O (f 0), openScalar O (f 1), openScalar_smooth O (f 0),
    openScalar_smooth O (f 1), ?_, ?_, ?_⟩
  · intro q hq
    have h := f.sum_eq_one (mem_univ (⟨q, hq⟩ : O))
    calc
      openScalar O (f 0) q + openScalar O (f 1) q = (f 0) ⟨q, hq⟩ + (f 1) ⟨q, hq⟩ :=
        congrArg₂ (· + ·) (openScalar_apply O (f 0) ⟨q, hq⟩) (openScalar_apply O (f 1) ⟨q, hq⟩)
      _ = 1 := by simpa only [finsum_eq_sum_of_fintype, Fin.sum_univ_two] using h
  · intro q hq hnot
    apply openScalar_eventually_zero O (f 0) ⟨q, hq⟩
    exact fun h => hnot (hf 0 h)
  · intro q hq hnot
    apply openScalar_eventually_zero O (f 1) ⟨q, hq⟩
    exact fun h => hnot (hf 1 h)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U : Set OrbitSpace} {n : ℕ}

/-- Projected support of a scalar product is contained in the scalar's true quotient support. -/
theorem quotientSupport_scalarMultiply_subset_tsupport (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) (w : EquivariantForm ρ U n) :
    quotientSupport (scalarMultiply ρ φ hφ n w) ⊆ tsupport φ := by
  apply closure_mono
  rintro q ⟨x, hx, rfl⟩
  change φ (coordinateProjection x) ≠ 0
  intro hz
  apply hx
  rw [scalarMultiply_apply]
  change φ (coordinateProjection x) • _ = 0
  rw [hz, zero_smul]

end TernaryPoly.SmoothDeRhamGluing
