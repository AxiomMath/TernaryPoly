module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerLift

@[expose] public section


/-!
# Linearity of the sign-twisted Eichler cocycle in its vector

The Eichler form, its straight-line period, the antisymmetrised potential `P⁻`, the Hilbert-level
cocycle `A ↦ P⁻(A i)` and its realization `l3Alpha` are ℂ-linear in the weight vector, for every
fixed real group element.  The Hilbert-level statements hold for arbitrary vectors; passing to the
realization needs the (smooth) values of the cocycles of the two summands.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

section Linear

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem l3_weightedOrbit_add (h : ℤ) (v v' : σ.H) (x : ℂ) :
    cuspWeightedAffineOrbit σ h (v + v') x =
      cuspWeightedAffineOrbit σ h v x + cuspWeightedAffineOrbit σ h v' x := by
  unfold cuspWeightedAffineOrbit cuspAffineOrbitVector
  rw [map_add, smul_add]

theorem l3_weightedOrbit_smul (h : ℤ) (c : ℂ) (v : σ.H) (x : ℂ) :
    cuspWeightedAffineOrbit σ h (c • v) x = c • cuspWeightedAffineOrbit σ h v x := by
  unfold cuspWeightedAffineOrbit cuspAffineOrbitVector
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  exact smul_comm _ _ _

theorem l3_form_add (h : ℤ) (v v' : σ.H) (x : ℂ) :
    binaryEndpointHolomorphicForm σ n h (v + v') x =
      binaryEndpointHolomorphicForm σ n h v x + binaryEndpointHolomorphicForm σ n h v' x := by
  funext position
  simp only [binaryEndpointHolomorphicForm, l3_weightedOrbit_add, smul_add, Pi.add_apply]

theorem l3_form_smul (h : ℤ) (c : ℂ) (v : σ.H) (x : ℂ) :
    binaryEndpointHolomorphicForm σ n h (c • v) x = c • binaryEndpointHolomorphicForm σ n h v x := by
  funext position
  simp only [binaryEndpointHolomorphicForm, l3_weightedOrbit_smul, Pi.smul_apply]
  exact smul_comm _ _ _

theorem l3_period_add (h : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    binaryEndpointPeriod σ n h (v + v') z =
      binaryEndpointPeriod σ n h v z + binaryEndpointPeriod σ n h v' z := by
  unfold binaryEndpointPeriod
  rw [← intervalIntegral.integral_add (binaryEndpointPeriod_integrable σ n h v z hz)
    (binaryEndpointPeriod_integrable σ n h v' z hz)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [l3_form_add, smul_add]

theorem l3_period_smul (h : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    binaryEndpointPeriod σ n h (c • v) z = c • binaryEndpointPeriod σ n h v z := by
  unfold binaryEndpointPeriod
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [l3_form_smul]
  exact smul_comm _ _ _

theorem l3Potential_add (h : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    l3Potential σ n h (v + v') z = l3Potential σ n h v z + l3Potential σ n h v' z := by
  have hz' : 0 < (binaryComplexReflection z).im := by
    rw [binaryComplexReflection_im]
    exact hz
  unfold l3Potential
  rw [l3_period_add σ n h v v' z hz, l3_period_add σ n h v v' (binaryComplexReflection z) hz',
    map_add]
  module

theorem l3Potential_smul (h : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    l3Potential σ n h (c • v) z = c • l3Potential σ n h v z := by
  unfold l3Potential
  rw [l3_period_smul σ n h c v z, l3_period_smul σ n h c v (binaryComplexReflection z), map_smul]
  module

theorem l3Cocycle_add (h : ℤ) (v v' : σ.H) (A : BinaryRealGL) :
    l3Cocycle σ n h (v + v') A = l3Cocycle σ n h v A + l3Cocycle σ n h v' A := by
  unfold l3Cocycle
  exact l3Potential_add σ n h v v' _ (basePoint_im_pos A)

theorem l3Cocycle_smul (h : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL) :
    l3Cocycle σ n h (c • v) A = c • l3Cocycle σ n h v A := by
  unfold l3Cocycle
  exact l3Potential_smul σ n h c v _

/-- **Additivity** of the scalar twisted Eichler cocycle in the vector, when the Hilbert-level
cocycle values of the summands are smooth. -/
theorem l3Alpha_add (h : ℤ) (v v' : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3Cocycle σ n h v A position ∈ σ.smooth)
    (hv' : ∀ position, l3Cocycle σ n h v' A position ∈ σ.smooth) :
    l3Alpha σ n h (v + v') A = l3Alpha σ n h v A + l3Alpha σ n h v' A := by
  unfold l3Alpha
  rw [l3Cocycle_add σ n h v v' A, hilbertLift_add σ _ _ hv hv']

/-- **Homogeneity** of the scalar twisted Eichler cocycle in the vector. -/
theorem l3Alpha_smul (h : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3Cocycle σ n h v A position ∈ σ.smooth) :
    l3Alpha σ n h (c • v) A = c • l3Alpha σ n h v A := by
  unfold l3Alpha
  rw [l3Cocycle_smul σ n h c v A, hilbertLift_smul σ c _ hv]

end Linear

end TernaryPeriodPolynomials.SourceConstruction

end
