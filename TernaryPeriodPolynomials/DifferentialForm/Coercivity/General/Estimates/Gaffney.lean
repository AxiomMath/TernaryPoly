module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.RegCore
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Invariantize

@[expose] public section


/-! # General coercivity, Tier B: Gaffney's lemma for every admissible group

Distance cutoffs around the orbit of a base point, made smooth and invariant by
`exists_invMult`, form a `CutoffSeq`; with Gaffney's lemma for elements supported over a compact set
this gives Gaffney's lemma `GaffneyAt Γ n k` for every admissible `Γ`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceRiemannian Set Metric Filter Topology

variable {Γ : Subgroup RealGL}

attribute [local instance] spaceMetricSpace in
/-- **Exhausting invariant cutoffs.**  Every admissible group has a sequence of smooth invariant
cutoffs supported over compact subsets of the orbit space, exhausting it, with gradient `O (1 / j)`. -/
theorem Admissible.nonempty_cutoffSeq (h : Admissible Γ) : Nonempty (CutoffSeq Γ) := by
  let S0 : Space := coordinateChart.symm 0
  have hex : ∀ j : ℕ, ∃ c : InvMult Γ, c.Slope (3 * plateauSlope * (1 / ((j : ℝ) + 1))) ∧
      (∀ x ∈ positiveCoordinates, c.toFun x ≠ 0 →
        coordProj Γ x ∈ proj Γ '' closedBall S0 (2 * ((j : ℝ) + 1))) ∧
      (∀ x ∈ positiveCoordinates, mProfile Γ S0 ((j : ℝ) + 1) (coordinateChart.symm x) = 1 →
        c.toFun x = 1) := by
    intro j
    have hr : 0 < (j : ℝ) + 1 := by positivity
    refine exists_invMult h (isCompact_projBall S0 (2 * ((j : ℝ) + 1))) (one_div_pos.mpr hr)
      (abs_mProfile_sub S0 hr) (mProfile_smul S0 ((j : ℝ) + 1)) (fun S hS => ?_)
    exact proj_mem_of_rho_lt S0 (rho_lt_of_mProfile_ne_zero S0 hr hS)
  choose c hslope hsupp hone using hex
  refine ⟨⟨c, 3 * plateauSlope, by linarith [plateauSlope_pos], fun j => ?_,
    fun j => proj Γ '' closedBall S0 (2 * ((j : ℝ) + 1)),
    fun j => isCompact_projBall S0 _, hsupp, ?_⟩⟩
  · have e : 3 * plateauSlope / ((j : ℝ) + 1) = 3 * plateauSlope * (1 / ((j : ℝ) + 1)) := by
      rw [mul_one_div]
    rw [e]
    exact hslope j
  · intro K hK
    obtain ⟨K', hK'c, hKK'⟩ := h.exists_compact_lift hK
    obtain ⟨R, hR⟩ := hK'c.isBounded.subset_closedBall S0
    filter_upwards [eventually_ge_atTop ⌈R⌉₊] with j hj x hx hxK
    refine hone j x hx (mProfile_eq_one S0 (by positivity) ?_)
    obtain ⟨T, hT, hTx⟩ := hKK' hxK
    have hj' : R ≤ (j : ℝ) + 1 := by
      have h1 := Nat.le_ceil R
      have h2 : (⌈R⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    exact (rho_le_of_proj_mem S0 ⟨T, hR hT, hTx⟩).trans hj'

/-- **Gaffney's lemma** for every admissible group: every element of the joint maximal graph lies in
the joint minimal graph. -/
theorem gaffneyAt [hΓ : Fact (Admissible Γ)] {n : ℕ} (k : ℕ) : GaffneyAt Γ n k := by
  obtain ⟨S⟩ := hΓ.out.nonempty_cutoffSeq
  exact gaffneyAt_of_compact S k (compactGaffneyAt k)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
