module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.KappaFormula
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.EdgeGen

@[expose] public section


/-!
# The coefficient at the standard edge of a class `[(a ⊗ ℓ₀) ⊗ e₀]` when the line `L` acts by a character

For `Q = P / U` acting on `Abar U A ⊗ L`, with `L` one-dimensional on which `q` acts by the scalar `χ q`, the
`ι_M`-image of the evaluation `evalQ` of the class `[(a ⊗ ℓ₀) ⊗ edgeGen]` is
`½ (∑_{q • p₀ = p₀} χ q • q a - ∑_{q • p₀ = swap p₀} χ q • q a)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
  TernaryPeriodPolynomials.Argument.BinaryDuality

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)]

theorem iotaM_normAt {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (χ : P ⧸ U → ℚ)
    (hχ : ∀ q, L.ρ q = χ q • LinearMap.id) (a : A.V) (q : P ⧸ U) :
    iotaM U A ℓ₀ hℓ ((Abar U A ⊗ L).ρ q (a ⊗ₜ[ℚ] ℓ₀)) = χ q • (Abar U A).ρ q a := by
  have h1 : (Abar U A ⊗ L).ρ q (a ⊗ₜ[ℚ] ℓ₀) = ((Abar U A).ρ q a) ⊗ₜ[ℚ] (L.ρ q ℓ₀) := rfl
  rw [h1, hχ q]
  change iotaM U A ℓ₀ hℓ (((Abar U A).ρ q a) ⊗ₜ[ℚ] (χ q • ℓ₀)) = _
  rw [iotaM_tmul, map_smul, coefL_spec]
  simp

theorem iotaM_evalQ_edgeGen (π : P ⧸ U →* IntegralGL) (hker : (π.ker : Set (P ⧸ U)).Finite)
    {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (χ : P ⧸ U → ℚ)
    (hχ : ∀ q, L.ρ q = χ q • LinearMap.id) (a : A.V) :
    letI : MulAction (P ⧸ U) OTE := oteMulActionQ π
    iotaM U A ℓ₀ hℓ (evalQ π hker (Abar U A ⊗ L)
        (Coinvariants.mk ((Abar U A ⊗ L).ρ.tprod (Rep.res π P1).ρ)
          ((a ⊗ₜ[ℚ] ℓ₀ : (Abar U A ⊗ L).V) ⊗ₜ[ℚ] edgeGen))) =
      (1 / 2 : ℚ) • ((∑ q ∈ (transp_finite (stab_finite_Q π hker) p0).toFinset, χ q • (Abar U A).ρ q a) -
        (∑ q ∈ (transp_finite (stab_finite_Q π hker) p0.swap).toFinset, χ q • (Abar U A).ρ q a)) := by
  let _ : MulAction (P ⧸ U) OTE := oteMulActionQ π
  rw [evalQ_edgeGen, map_smul, map_sub]
  unfold normAt
  simp only [LinearMap.sum_apply, map_sum]
  have key : ∀ s : Finset (P ⧸ U), ∑ q ∈ s, iotaM U A ℓ₀ hℓ ((Abar U A ⊗ L).ρ q (a ⊗ₜ[ℚ] ℓ₀)) =
      ∑ q ∈ s, χ q • (Abar U A).ρ q a :=
    fun s => Finset.sum_congr rfl fun q _ => iotaM_normAt U A ℓ₀ hℓ χ hχ a q
  rw [key, key]

omit [Representation.IsTrivial (A.ρ.comp U.subtype)] in
/-- Membership in the first index set: the elements of `Q` stabilizing the standard edge. -/
theorem mem_transp_p0 (π : P ⧸ U →* IntegralGL) (hker : (π.ker : Set (P ⧸ U)).Finite) (q : P ⧸ U) :
    letI : MulAction (P ⧸ U) OTE := oteMulActionQ π
    q ∈ (transp_finite (stab_finite_Q π hker) p0).toFinset ↔ q • p0 = p0 := by
  let _ : MulAction (P ⧸ U) OTE := oteMulActionQ π
  rw [Set.Finite.mem_toFinset]
  rfl

omit [Representation.IsTrivial (A.ρ.comp U.subtype)] in
/-- Membership in the second index set: the elements of `Q` carrying the standard edge to its reverse. -/
theorem mem_transp_swap (π : P ⧸ U →* IntegralGL) (hker : (π.ker : Set (P ⧸ U)).Finite) (q : P ⧸ U) :
    letI : MulAction (P ⧸ U) OTE := oteMulActionQ π
    q ∈ (transp_finite (stab_finite_Q π hker) p0.swap).toFinset ↔ q • p0 = p0.swap := by
  let _ : MulAction (P ⧸ U) OTE := oteMulActionQ π
  rw [Set.Finite.mem_toFinset]
  have e : ∀ y : OTE, q • y.swap = (q • y).swap := fun y => (OTE.swap_smul (π q) y).symm
  change q • p0.swap = p0 ↔ _
  constructor
  · intro h
    have h2 := congrArg OTE.swap h
    rw [← e] at h2
    simpa [OTE.swap_swap] using h2
  · intro h
    rw [e, h, OTE.swap_swap]

/-- **Explicit form**: the sums run over `{q | q • p₀ = p₀}` and `{q | q • p₀ = swap p₀}`. -/
theorem iotaM_evalQ_edgeGen_explicit (π : P ⧸ U →* IntegralGL) (hker : (π.ker : Set (P ⧸ U)).Finite)
    {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (χ : P ⧸ U → ℚ)
    (hχ : ∀ q, L.ρ q = χ q • LinearMap.id) (a : A.V) (S S' : Finset (P ⧸ U))
    (hS : letI : MulAction (P ⧸ U) OTE := oteMulActionQ π; ∀ q, q ∈ S ↔ q • p0 = p0)
    (hS' : letI : MulAction (P ⧸ U) OTE := oteMulActionQ π; ∀ q, q ∈ S' ↔ q • p0 = p0.swap) :
    letI : MulAction (P ⧸ U) OTE := oteMulActionQ π
    iotaM U A ℓ₀ hℓ (evalQ π hker (Abar U A ⊗ L)
        (Coinvariants.mk ((Abar U A ⊗ L).ρ.tprod (Rep.res π P1).ρ)
          ((a ⊗ₜ[ℚ] ℓ₀ : (Abar U A ⊗ L).V) ⊗ₜ[ℚ] edgeGen))) =
      (1 / 2 : ℚ) • ((∑ q ∈ S, χ q • (Abar U A).ρ q a) - (∑ q ∈ S', χ q • (Abar U A).ρ q a)) := by
  let _ : MulAction (P ⧸ U) OTE := oteMulActionQ π
  have e1 : (transp_finite (stab_finite_Q π hker) p0).toFinset = S :=
    Finset.ext fun q => (mem_transp_p0 U π hker q).trans (hS q).symm
  have e2 : (transp_finite (stab_finite_Q π hker) p0.swap).toFinset = S' :=
    Finset.ext fun q => (mem_transp_swap U π hker q).trans (hS' q).symm
  rw [← e1, ← e2]
  exact iotaM_evalQ_edgeGen U A π hker ℓ₀ hℓ χ hχ a

end TernaryPeriodPolynomials.Argument.HochschildSerre
