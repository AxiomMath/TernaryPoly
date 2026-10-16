module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EndpointReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.StabilizerBorel

@[expose] public section


/-!
# `FlagExact` as vanishing of an `H²` class of the complete-flag stabilizer

Fix a source cocycle `c` and a complete flag `q`. The flag evaluation
`x ↦ c(x)(q⁻¹)` on rational vertices is a homogeneous 2-cocycle for the arithmetic
stabilizer `Γ_q = rationalLevel ∩ Stab(qB)`. `FlagExact` holds exactly when the
corresponding Mathlib group cohomology class in `H²(Γ_q, V)` vanishes.

This turns the obligation `remaining.1` of `general_eisenstein_graph` into a statement
about Mathlib group cohomology of the Borel-type arithmetic group `Γ_q`.

Original work (AxiomDeep, Claude Opus 5.5). It uses the ambient/group comparison
`ambientCocycle_H2_zero_iff` from the inherited Codexiom `SphericalDetection` modules.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GraphPieces

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The arithmetic stabilizer of the complete flag `flag · B`. -/
def edgeStabilizer (flag : RationalGL3) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3 (QuotientGroup.mk flag : Edges)

theorem edgeStabilizer_conj_mem (side : Side) (flag : RationalGL3) (γ : edgeStabilizer flag) :
    (γ.val⁻¹ * flag)⁻¹ * flag ∈ parabolic side := by
  have hstab : γ.val • (QuotientGroup.mk flag : Edges) = QuotientGroup.mk flag :=
    MulAction.mem_stabilizer_iff.mp γ.property.2
  have hborel := stabilizer_mem_borel flag γ.val hstab
  have heq : (γ.val⁻¹ * flag)⁻¹ * flag = flag⁻¹ * γ.val * flag := by group
  rw [heq]
  cases side
  · exact hborel.1
  · exact hborel.2

/-- The flag evaluation as a homogeneous 2-cochain of the stabilizer. -/
def flagCochain {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (flag : RationalGL3) :
    cochains (edgeStabilizer flag) (rationalCoefficientComponent degree data.chi) 2 :=
  ⟨fun x => Comparison.rationalEvaluation source x flag, by
    intro γ x
    change Comparison.rationalEvaluation source (fun i => γ.val * x i) flag = _
    rw [Comparison.rationalEvaluation_equivariant data side source isSource ⟨γ.val, γ.property.1⟩ x flag]
    congr 1
    exact RationalComparison.source_flagIndependent data RationalNorm.rational_norm side source isSource
      x _ _ (edgeStabilizer_conj_mem side flag γ)⟩

/-- The flag evaluation is a cocycle. -/
def flagCocycle {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (flag : RationalGL3) :
    cocycles (edgeStabilizer flag) (rationalCoefficientComponent degree data.chi) :=
  ⟨flagCochain data side source isSource flag, by
    change differentialTwo _ _ _ = 0
    funext vertices
    have tripleEquality : ∀ first second third,
        (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((![first, second, third] : Fin 3 → RationalGL3) index)) =
        ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) first,
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) second,
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) third] := by
      intro first second third
      funext index
      fin_cases index <;> rfl
    simpa only [differentialTwo, flagCochain, Comparison.rationalEvaluation, tripleEquality,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
      using isSource.2.2.2
        (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
        (rationalGroup flag⁻¹)⟩

/-- `FlagExact` is literally exactness of the stabilizer cocycle. -/
theorem flagExact_iff_primitive {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (flag : RationalGL3) :
    EndpointReduction.FlagExact data source flag ↔
      ∃ primitive : cochains (edgeStabilizer flag) (rationalCoefficientComponent degree data.chi) 1,
        differentialOne _ _ primitive = (flagCocycle data side source isSource flag).val := by
  constructor
  · rintro ⟨primitive, equivariant, boundary⟩
    refine ⟨⟨primitive, fun γ x => equivariant ⟨γ.val, γ.property.1⟩
      (MulAction.mem_stabilizer_iff.mp γ.property.2) x⟩, ?_⟩
    apply Subtype.ext
    funext x
    exact (boundary x).symm
  · rintro ⟨primitive, boundary⟩
    refine ⟨primitive.val, fun γ hγ x => primitive.property ⟨γ.val, ⟨γ.property,
      MulAction.mem_stabilizer_iff.mpr hγ⟩⟩ x, fun x => ?_⟩
    have := congrArg (fun cochain => cochain.val x) boundary
    exact this.symm

/-- **`FlagExact` as vanishing of a Mathlib `H²` class of the complete-flag stabilizer.** -/
theorem flagExact_iff_H2_zero {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (flag : RationalGL3) :
    EndpointReduction.FlagExact data source flag ↔
      groupCohomology.H2π (SphericalDetection.Helpers.subgroupCoefficientRep (edgeStabilizer flag)
          (rationalCoefficientComponent degree data.chi))
        (SphericalDetection.Helpers.ambientCocycleToGroup (edgeStabilizer flag)
          (rationalCoefficientComponent degree data.chi) (flagCocycle data side source isSource flag)) = 0 :=
  (flagExact_iff_primitive data side source isSource flag).trans
    (SphericalDetection.Helpers.ambientCocycle_H2_zero_iff _ _ _).symm

end TernaryPeriodPolynomials.FlagExactness
