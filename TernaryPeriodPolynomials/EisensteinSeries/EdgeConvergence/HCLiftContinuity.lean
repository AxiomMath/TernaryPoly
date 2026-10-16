module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftUniform
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftSlice

@[expose] public section


/-!
# Continuity in the parameter of the Taylor coefficients of the orbit functions

Original work by Claude Sonnet 5.5.

At any argument `y`, the orbit function of the twisted family at the parameter `s` is
`(s, M) ↦ exp((s - s₀)(weight + log Ξ)) • (orbit function at `s₀`)(M)`, jointly smooth in `(s, M)`
on `ℂ ×` the invertible matrices (`shiftFunction_contDiffOn`). Hence the Taylor coefficients at a
fixed tuple are continuous in `s` (`continuous_orbit_coefficients`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers
open CompactTaylorBounds

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

section Continuity

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- The orbit function of the twisted family at the argument `y`, as a function of the parameter
and the tuple of matrices (the shift formula). -/
def shiftFunction (y : AdelicGL) :
    ℂ × SmoothJets.MatrixTuples 3 arity.succ → data.cusp.H :=
  fun pair =>
    (Complex.exp ((pair.1 - cohomologicalPoint) *
        (weight (fun i => invertibleMatrix (pair.2 i.castSucc)) : ℂ)) *
      Complex.exp ((pair.1 - cohomologicalPoint) *
        (heightLog (y * atInfinity (invertibleMatrix (pair.2 (Fin.last arity)))) : ℂ))) •
    FamilyCuspTaylor.matrixOrbit data .plane cohomologicalPoint family induced y pair.2

theorem orbitAt_eq_shiftFunction (parameter : ℂ) (y : AdelicGL) :
    orbitAt data holomorphic family induced weight parameter y =
      fun matrices => shiftFunction data family induced weight y (parameter, matrices) :=
  funext fun matrices =>
    matrixOrbit_twistedAt data holomorphic family induced weight parameter y matrices

theorem shiftFunction_contDiffOn (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (y : AdelicGL) :
    ContDiffOn ℝ ⊤ (shiftFunction data family induced weight y)
      {pair | pair.2 ∈ SmoothJets.domain 3 arity.succ} := by
  have hθ : ContDiffOn ℝ ⊤ (FamilyCuspTaylor.matrixOrbit data .plane cohomologicalPoint family
      induced y) (SmoothJets.domain 3 arity.succ) :=
    FamilyCuspLift.joint_smooth data .plane cohomologicalPoint family induced lift y
  have hw : ContDiffOn ℝ ⊤ (fun N : SmoothJets.MatrixTuples 3 arity.succ =>
      weight (fun i => invertibleMatrix (N i.castSucc))) (SmoothJets.domain 3 arity.succ) :=
    smooth_comp_castSucc weight weightSmooth
  have hh : ContDiffOn ℝ ⊤ (fun N : SmoothJets.MatrixTuples 3 arity.succ =>
      heightLog (y * atInfinity (invertibleMatrix (N (Fin.last arity)))))
      (SmoothJets.domain 3 arity.succ) :=
    smooth_comp_coordinate (Fin.last arity)
      (fun x : Fin 1 → RealGL3 => heightLog (y * atInfinity (x 0)))
      (heightLog_law.smooth y)
  have hz : ContDiff ℝ ⊤ (fun pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ =>
      pair.1 - cohomologicalPoint) :=
    contDiff_fst.sub contDiff_const
  have hθs := hθ.comp contDiff_snd.contDiffOn
    (s := {pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ |
      pair.2 ∈ SmoothJets.domain 3 arity.succ}) (fun pair membership => membership)
  have hws := hw.comp contDiff_snd.contDiffOn
    (s := {pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ |
      pair.2 ∈ SmoothJets.domain 3 arity.succ}) (fun pair membership => membership)
  have hhs := hh.comp contDiff_snd.contDiffOn
    (s := {pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ |
      pair.2 ∈ SmoothJets.domain 3 arity.succ}) (fun pair membership => membership)
  have first : ContDiffOn ℝ ⊤ (fun pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ =>
      Complex.exp ((pair.1 - cohomologicalPoint) *
        (weight (fun i => invertibleMatrix (pair.2 i.castSucc)) : ℂ)))
      {pair | pair.2 ∈ SmoothJets.domain 3 arity.succ} :=
    (hz.contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hws)).cexp
  have second : ContDiffOn ℝ ⊤ (fun pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ =>
      Complex.exp ((pair.1 - cohomologicalPoint) *
        (heightLog (y * atInfinity (invertibleMatrix (pair.2 (Fin.last arity)))) : ℂ)))
      {pair | pair.2 ∈ SmoothJets.domain 3 arity.succ} :=
    (hz.contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hhs)).cexp
  exact (first.mul second).smul hθs

/-- The Taylor coefficients at a fixed tuple of the orbit functions of the twisted family are
continuous in the parameter. -/
theorem continuous_orbit_coefficients (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (y : AdelicGL) (real : Fin (arity + 1) → RealGL3) (order : ℕ) :
    Continuous (fun parameter => coefficients
      (orbitAt data holomorphic family induced weight parameter y)
      (fun index => (real index).val) order) := by
  have centerMembership : (fun index => (real index).val) ∈ SmoothJets.domain 3 arity.succ :=
    fun _ => GeneralLinearGroup.det_ne_zero _
  have domainOpen : IsOpen {pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ |
      pair.2 ∈ SmoothJets.domain 3 arity.succ} :=
    (SmoothJets.domain_open 3 arity.succ).preimage continuous_snd
  have sliced := continuousOn_sliceCoefficients (shiftFunction data family induced weight y)
    domainOpen (shiftFunction_contDiffOn data family induced weight lift weightSmooth y)
    (fun index => (real index).val) order
  have everything : {parameter : ℂ | (parameter, (fun index => (real index).val)) ∈
      {pair : ℂ × SmoothJets.MatrixTuples 3 arity.succ |
        pair.2 ∈ SmoothJets.domain 3 arity.succ}} = Set.univ :=
    Set.eq_univ_of_forall fun _ => centerMembership
  rw [everything, continuousOn_univ] at sliced
  have equality : (fun parameter => coefficients
      (orbitAt data holomorphic family induced weight parameter y)
      (fun index => (real index).val) order) =
      fun parameter => coefficients
        (fun matrices => shiftFunction data family induced weight y (parameter, matrices))
        (fun index => (real index).val) order := by
    funext parameter
    rw [orbitAt_eq_shiftFunction data holomorphic family induced weight parameter y]
  rw [equality]
  exact sliced

end Continuity

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
