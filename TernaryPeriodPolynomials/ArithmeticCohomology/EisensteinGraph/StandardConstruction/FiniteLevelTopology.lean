module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TopologicalMatrices
public import Mathlib.Topology.Instances.ZMod

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteLevelTopology

theorem padicReduction_continuous {prime : ℕ} [Fact prime.Prime] :
    Continuous (PadicInt.toZMod : ℤ_[prime] → ZMod prime) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZMod : ℤ_[prime] →+* ZMod prime)
  have near : ∀ᶠ value : ℤ_[prime] in 𝓝 0, ‖value‖ < 1 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have constant : (PadicInt.toZMod : ℤ_[prime] → ZMod prime) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [near] with value bound
    have membership : value ∈ IsLocalRing.maximalIdeal ℤ_[prime] :=
      (IsLocalRing.mem_maximalIdeal value).mpr (PadicInt.mem_nonunits.mpr bound)
    rw [← PadicInt.ker_toZMod] at membership
    exact membership
  exact continuousAt_const.congr_of_eventuallyEq constant

theorem integralThree_continuous : Continuous integralThree := by
  have equivContinuous : Continuous threeIntegralEquiv := by
    exact @ContinuousAlgEquiv.continuous_invFun _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
      (PadicInt.adicCompletionIntegersEquiv ℤ primeThree)
  exact equivContinuous.comp (continuous_apply placeThree)

theorem integralReduction_continuous : Continuous integralReduction :=
  padicReduction_continuous.comp integralThree_continuous

theorem finiteLevel_isOpen : IsOpen (finiteLevel : Set FiniteGL) := by
  have sourceOpen : IsOpen
      (((rowStabilizer).comap (GeneralLinearGroup.map integralReduction)) :
        Set (GeneralLinearGroup (Fin 3) IntegralAdeles)) := by
    exact (isOpen_discrete (rowStabilizer : Set (GeneralLinearGroup (Fin 3) (ZMod 3)))).preimage
      (TopologicalMatrices.generalLinearMap_continuous integralReduction integralReduction_continuous)
  exact TopologicalMatrices.integralGL_isOpenEmbedding.isOpenMap _ sourceOpen

instance integralGLCompact : CompactSpace (GeneralLinearGroup (Fin 3) IntegralAdeles) := by
  let : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  infer_instance

theorem finiteLevel_isCompact : IsCompact (finiteLevel : Set FiniteGL) := by
  have sourceClosed : IsClosed
      (((rowStabilizer).comap (GeneralLinearGroup.map integralReduction)) :
        Set (GeneralLinearGroup (Fin 3) IntegralAdeles)) := by
    exact (isClosed_discrete (rowStabilizer : Set (GeneralLinearGroup (Fin 3) (ZMod 3)))).preimage
      (TopologicalMatrices.generalLinearMap_continuous integralReduction integralReduction_continuous)
  exact sourceClosed.isCompact.image TopologicalMatrices.integralGL_isOpenEmbedding.continuous

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteLevelTopology
