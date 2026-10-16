module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.Reduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem padicInt_toZMod_continuous {prime : ℕ} [Fact prime.Prime]
    [TopologicalSpace (ZMod prime)] : Continuous (PadicInt.toZMod : ℤ_[prime] → ZMod prime) := by
  apply continuous_iff_continuousAt.mpr
  intro value
  apply Filter.EventuallyEq.continuousAt (y := PadicInt.toZMod value)
  have near : ∀ᶠ nearby : ℤ_[prime] in nhds value, ‖nearby - value‖ < 1 :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).eventually_mem (by simp)
  filter_upwards [near] with nearby close
  have in_kernel : nearby - value ∈ RingHom.ker (PadicInt.toZMod : ℤ_[prime] →+* ZMod prime) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.isUnit_iff]
    exact ne_of_lt close
  have reduction_zero := RingHom.mem_ker.mp in_kernel
  rw [map_sub] at reduction_zero
  exact sub_eq_zero.mp reduction_zero

theorem threeIntegralEquiv_continuous : Continuous threeIntegralEquiv := by
  exact @ContinuousAlgEquiv.continuous_invFun _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
    (PadicInt.adicCompletionIntegersEquiv ℤ primeThree)

theorem integralReduction_continuous [TopologicalSpace (ZMod 3)] : Continuous integralReduction :=
  padicInt_toZMod_continuous.comp (threeIntegralEquiv_continuous.comp (continuous_apply placeThree))

theorem generalLinearGroup_map_continuous {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (ringMap : R →+* S) (continuous : Continuous ringMap)
    (size : ℕ) : Continuous (GeneralLinearGroup.map (n := Fin size) ringMap) := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous.comp ((continuous_apply column).comp (continuous_apply row))))

theorem generalLinearGroup_map_isOpen {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (ringMap : R →+* S)
    (embedding : Topology.IsOpenEmbedding ringMap) (size : ℕ) :
    IsOpenMap (GeneralLinearGroup.map (n := Fin size) ringMap) := by
  apply Units.isOpenMap_map
  · exact Matrix.map_injective embedding.injective
  · exact (Topology.IsOpenEmbedding.piMap (fun _ : Fin size =>
      Topology.IsOpenEmbedding.piMap (fun _ : Fin size => embedding))).isOpenMap

theorem finiteLevel_isOpen : IsOpen (finiteLevel : Set FiniteGL) := by
  let : TopologicalSpace (ZMod 3) := ⊥
  let : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  have source_open : IsOpen
      (((GeneralEisenstein.rowStabilizer).comap (GeneralLinearGroup.map integralReduction) :
        Subgroup (GeneralLinearGroup (Fin 3) IntegralAdeles)) : Set (GeneralLinearGroup (Fin 3) IntegralAdeles)) :=
    (isOpen_discrete _ : IsOpen (GeneralEisenstein.rowStabilizer : Set (GeneralLinearGroup (Fin 3) (ZMod 3)))).preimage
      (generalLinearGroup_map_continuous integralReduction integralReduction_continuous 3)
  exact generalLinearGroup_map_isOpen integralEmbedding integralEmbedding_isOpenEmbedding 3 _ source_open

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
