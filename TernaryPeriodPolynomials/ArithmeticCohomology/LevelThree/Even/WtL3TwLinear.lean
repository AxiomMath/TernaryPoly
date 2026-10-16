module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLiftB

@[expose] public section


/-!
# Linearity of the weight-generic sign-twisted Eichler cocycle in its vector

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `AxiomCodeSourceConstruction/L3EichlerLinear` for an integer rotation weight `wt`: the
weighted affine orbit, the Eichler form, its straight-line period, the antisymmetrised potential
`P⁻`, the Hilbert-level cocycle `A ↦ P⁻(A i)` and its realization `l3AlphaWt` are ℂ-linear in the
weight vector.  The Hilbert-level statements hold for arbitrary vectors; passing to the realization
needs the (smooth) values of the cocycles of the two summands.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

section Linear

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem l3_weightedOrbit_addWt (wt : ℤ) (v v' : σ.H) (x : ℂ) :
    cuspWeightedAffineOrbitWt σ wt (v + v') x =
      cuspWeightedAffineOrbitWt σ wt v x + cuspWeightedAffineOrbitWt σ wt v' x := by
  unfold cuspWeightedAffineOrbitWt cuspAffineOrbitVector
  rw [map_add, smul_add]

theorem l3_weightedOrbit_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (x : ℂ) :
    cuspWeightedAffineOrbitWt σ wt (c • v) x = c • cuspWeightedAffineOrbitWt σ wt v x := by
  unfold cuspWeightedAffineOrbitWt cuspAffineOrbitVector
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  exact smul_comm _ _ _

theorem l3_form_addWt (wt : ℤ) (v v' : σ.H) (x : ℂ) :
    binaryEndpointHolomorphicFormWt σ n wt (v + v') x =
      binaryEndpointHolomorphicFormWt σ n wt v x + binaryEndpointHolomorphicFormWt σ n wt v' x := by
  funext position
  simp only [binaryEndpointHolomorphicFormWt, l3_weightedOrbit_addWt, smul_add, Pi.add_apply]

theorem l3_form_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (x : ℂ) :
    binaryEndpointHolomorphicFormWt σ n wt (c • v) x =
      c • binaryEndpointHolomorphicFormWt σ n wt v x := by
  funext position
  simp only [binaryEndpointHolomorphicFormWt, l3_weightedOrbit_smulWt, Pi.smul_apply]
  exact smul_comm _ _ _

theorem l3_period_addWt (wt : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    binaryEndpointPeriodWt σ n wt (v + v') z =
      binaryEndpointPeriodWt σ n wt v z + binaryEndpointPeriodWt σ n wt v' z := by
  unfold binaryEndpointPeriodWt
  rw [← intervalIntegral.integral_add (binaryEndpointPeriod_integrableWt σ n wt v z hz)
    (binaryEndpointPeriod_integrableWt σ n wt v' z hz)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [l3_form_addWt, smul_add]

theorem l3_period_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    binaryEndpointPeriodWt σ n wt (c • v) z = c • binaryEndpointPeriodWt σ n wt v z := by
  unfold binaryEndpointPeriodWt
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [l3_form_smulWt]
  exact smul_comm _ _ _

theorem l3Potential_addWt (wt : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    l3PotentialWt σ n wt (v + v') z = l3PotentialWt σ n wt v z + l3PotentialWt σ n wt v' z := by
  have hz' : 0 < (binaryComplexReflection z).im := by
    rw [binaryComplexReflection_im]
    exact hz
  unfold l3PotentialWt
  rw [l3_period_addWt σ n wt v v' z hz, l3_period_addWt σ n wt v v' (binaryComplexReflection z) hz',
    map_add]
  module

theorem l3Potential_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    l3PotentialWt σ n wt (c • v) z = c • l3PotentialWt σ n wt v z := by
  unfold l3PotentialWt
  rw [l3_period_smulWt σ n wt c v z, l3_period_smulWt σ n wt c v (binaryComplexReflection z),
    map_smul]
  module

theorem l3Cocycle_addWt (wt : ℤ) (v v' : σ.H) (A : BinaryRealGL) :
    l3CocycleWt σ n wt (v + v') A = l3CocycleWt σ n wt v A + l3CocycleWt σ n wt v' A := by
  unfold l3CocycleWt
  exact l3Potential_addWt σ n wt v v' _ (basePoint_im_pos A)

theorem l3Cocycle_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL) :
    l3CocycleWt σ n wt (c • v) A = c • l3CocycleWt σ n wt v A := by
  unfold l3CocycleWt
  exact l3Potential_smulWt σ n wt c v _

/-- **Additivity** of the scalar twisted Eichler cocycle in the vector, when the Hilbert-level
cocycle values of the summands are smooth. -/
theorem l3Alpha_addWt (wt : ℤ) (v v' : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3CocycleWt σ n wt v A position ∈ σ.smooth)
    (hv' : ∀ position, l3CocycleWt σ n wt v' A position ∈ σ.smooth) :
    l3AlphaWt σ n wt (v + v') A = l3AlphaWt σ n wt v A + l3AlphaWt σ n wt v' A := by
  unfold l3AlphaWt
  rw [l3Cocycle_addWt σ n wt v v' A, hilbertLift_add σ _ _ hv hv']

/-- **Homogeneity** of the scalar twisted Eichler cocycle in the vector. -/
theorem l3Alpha_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3CocycleWt σ n wt v A position ∈ σ.smooth) :
    l3AlphaWt σ n wt (c • v) A = c • l3AlphaWt σ n wt v A := by
  unfold l3AlphaWt
  rw [l3Cocycle_smulWt σ n wt c v A, hilbertLift_smul σ c _ hv]

end Linear

end TernaryPeriodPolynomials.EvenLevelThree

end
