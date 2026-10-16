module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitShape

@[expose] public section


/-!
# Global limit: the global integrand is continuous and measurable

`F(s + a, t + b) = F(s, t)` for integral `(a, b)` (`GlobalLimitInvariance`), so `F` is constant on the cosets of the open subgroup `Λ × Λ` (`Λ` = integral points of `FiniteAwayThree`): it is locally
constant, hence continuous, hence measurable.  This is the measurability needed for the integrability and dominated convergence of the global finite integral.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInvariance
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMeas

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The open subgroup of integral points of `FiniteAwayThree`, as a set. -/
def LamZ : Set FiniteAwayThree := Subtype.val ⁻¹' Set.range integralEmbedding

theorem LamZ_isOpen : IsOpen LamZ := integralLattice_isOpen.preimage continuous_subtype_val

theorem LamZ_sub {x y : FiniteAwayThree} (hx : x ∈ LamZ) (hy : y ∈ LamZ) : x - y ∈ LamZ := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  exact ⟨u - v, by rw [map_sub, hu, hv]; rfl⟩

theorem locallyConstant_globalIntegrand (I : EichlerInput σ n) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) : IsLocallyConstant (globalIntegrand I Z gInf) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro z
  refine ⟨{z' | z'.1 - z.1 ∈ LamZ ∧ z'.2 - z.2 ∈ LamZ}, ?_, ?_, ?_⟩
  · exact (LamZ_isOpen.preimage (continuous_fst.sub continuous_const)).inter
      (LamZ_isOpen.preimage (continuous_snd.sub continuous_const))
  · simp only [Set.mem_ofPred_eq, sub_self]
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  · rintro z' ⟨h1, h2⟩
    have e : z' = (z.1 + (z'.1 - z.1), z.2 + (z'.2 - z.2)) := by
      ext <;> simp
    rw [e]
    exact globalIntegrand_add_integral I Z hZ gInf z _ _
      (fun w => (mem_range_integralEmbedding_iff _).mp h1 w)
      (fun w => (mem_range_integralEmbedding_iff _).mp h2 w)

theorem globalIntegrand_continuous (I : EichlerInput σ n) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) : Continuous (globalIntegrand I Z gInf) :=
  (locallyConstant_globalIntegrand I Z hZ gInf).continuous

theorem globalIntegrand_measurable (I : EichlerInput σ n) (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) : Measurable (globalIntegrand I Z gInf) :=
  (globalIntegrand_continuous I Z hZ gInf).measurable

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMeas
