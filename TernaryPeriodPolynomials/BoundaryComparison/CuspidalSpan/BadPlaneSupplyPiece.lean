module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneEdgeExact
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Source
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.RadicalLaw
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace

@[expose] public section


/-!
# One Eichler input realizes its period class in the automorphic plane span

Lemma C.3 at the bad plane (`ar:lem:seed`, level one): for a cuspidal datum `M` and an Eichler
input `I` on its cuspidal part, the plane source built from the Eichler cocycle of `I` is a source
cocycle; its class lies in the plane summand of `M`; the cutoff to the bad plane
(`Separation.exists_cutoff_plane`, a support statement) keeps the bad-plane coordinate and
kills the good-plane one; and the bad-plane edge of the class is exactly `-[φ_I]`, where `φ_I` is
the arithmetic period cocycle of `I` (Kostant constant `-1`, `BadPlaneEdgeExact`).
-/


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

/-- **An Eichler input realizes minus its arithmetic period class** at the bad plane, by an element
of the automorphic plane span that vanishes at the good plane. -/
theorem eichlerInput_realized {n : ℕ} (hn : 0 < n) (hodd : Odd n) (M : CohomologicalCuspData n)
    (I : EichlerInput M.cusp n) :
    ∃ b ∈ automorphicPlaneSpan n, cuspRes n trivialCharacter .plane true b = 0 ∧
      edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false b) =
        -groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
          (I.arithmeticPeriodCocycle
            (TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData)) := by
  let stages := TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData
  let E : LeviCocycleData M.cusp n := LeviCocycleData.ofEichler (I.eichlerCocycle_spec stages)
  have hχ : ∀ u : IntegralAdelesˣ, M.inducingData.chi.toMonoidHom (integralAdeleUnit u) = 1 :=
    fun _ => rfl
  let s : sourceCocycles M.inducingData .plane :=
    ⟨planeSource M.inducingData E, planeSource_isSourceCocycle M.inducingData E hχ⟩
  have ha : sourceClass M.inducingData .plane s ∈ boundarySummand M.inducingData .plane := by
    rw [← sourceClass_range]
    exact LinearMap.mem_range_self _ _
  obtain ⟨a', ha', hkeep, hkill⟩ :=
    TernaryPeriodPolynomials.Separation.exists_cutoff_plane M.inducingData false ha
  refine ⟨a', Submodule.subset_span ⟨M, ha'⟩, hkill, ?_⟩
  have hz : ∀ g h : PlaneStab,
      (evaluatedSource M.inducingData .plane s).val.val ![1, g.val, g.val * h.val]
          (QuotientGroup.mk 1) =
        ((sourceCupData E).l (g.val * h.val) - (sourceCupData E).l g.val)
          ((sourceCupData E).a g.val - (sourceCupData E).a 1) := fun g h =>
    (evaluatedSource_realizes M.inducingData .plane s ![1, g.val, g.val * h.val] 1).trans
      (sourceCupData_identity M.inducingData E rfl ![1, g.val, g.val * h.val])
  have hedge := edgeH2_cuspRes_plane_false_eq (sourceCupData E)
    (kostantLaw_of_planeRadical (lam := (sourceCupData E).lam) (fun _ _ => rfl))
    (I.arithmeticPeriodCocycle stages) (fun m => (sourceA_levi E m).symm) hn hodd
    (evaluatedSource M.inducingData .plane s) hz
  rw [hkeep]
  exact hedge.trans (neg_one_smul ℂ _)

end TernaryPeriodPolynomials.Argument.CuspidalSpan
