module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualEquiv

@[expose] public section


/-!
# General coercivity, dual coefficients: the dual metric and the dual `L²` pairing

The metric of the dual flat bundle `Λ^k T* ⊗ E*` at a point `x` is the inverse trace Gram matrix of
the cotangent space at `x`, tensored with the dual coefficient metric, which is the standard
coefficient metric at the Cartan point `ι x` (the metric `‖ρ*(g)⁻¹ v‖` at `S = g gᵀ`).
`dualFormPairing` is that explicit contraction; `dualScalar` is its descent to the orbit space and
`dualL2` its integral for the Riemannian volume of the orbit space.  The transport theorem
`dualL2_eq` identifies it with the standard `L²` pairing of the Cartan images.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
  TernaryPoly.SymmetricSpaceRiemannian TernaryPoly.SymmetricSpaceTraceMetric
open MeasureTheory Set Filter
open scoped ContDiff Topology

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- The metric of the dual bundle `Λ^k T* ⊗ E*` at `x`: the inverse Gram matrix of the trace metric
at `x` tensored with the standard coefficient metric at the Cartan point `ι x`. -/
def dualFormPairing (n k : ℕ) (x : Coordinates) (a b : FormValue n k) : ℝ :=
  (k.factorial : ℝ)⁻¹ * matrixContraction (coordinateCoefficientBilin n (iotaC x))
    (tensorMatrix k (inverseGram x)) (formCoordinates a) (formCoordinates b)

theorem coordinateGram_iotaC {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (LinearMap.toMatrix' (fderiv ℝ iotaC x).toLinearMap).transpose *
      coordinateGram (iotaC x) * LinearMap.toMatrix' (fderiv ℝ iotaC x).toLinearMap =
        coordinateGram x := by
  have hm := congrArg LinearMap.BilinForm.toMatrix' (coordinateBilin_iotaC hx)
  simpa only [LinearMap.BilinForm.toMatrix'_comp, coordinateGram] using hm

theorem compCLM_iotaC_comp {x : Coordinates} (hx : x ∈ positiveCoordinates) (a : FormValue n k) :
    (a.compContinuousLinearMap (fderiv ℝ iotaC (iotaC x))).compContinuousLinearMap
      (fderiv ℝ iotaC x) = a := by
  apply ContinuousAlternatingMap.ext
  intro v
  change a (fun i => (fderiv ℝ iotaC (iotaC x)) ((fderiv ℝ iotaC x) (v i))) = a v
  apply congrArg a
  funext i
  exact congrArg (fun L : Coordinates →L[ℝ] Coordinates => L (v i)) (fderiv_iotaC_comp hx)

/-- The dual metric of a form is the standard metric of its Cartan pullback at `ι x`. -/
theorem dualFormPairing_eq {x : Coordinates} (hx : x ∈ positiveCoordinates) (a b : FormValue n k) :
    dualFormPairing n k x a b =
      formPairing n k (iotaC x) (a.compContinuousLinearMap (fderiv ℝ iotaC (iotaC x)))
        (b.compContinuousLinearMap (fderiv ℝ iotaC (iotaC x))) := by
  have key := contraction_isometry (n := n) (k := k)
    (coordinateCoefficientBilin n (iotaC x)) (coordinateGram x) (coordinateGram (iotaC x))
    (coordinateGram_posDef x hx) (fderiv ℝ iotaC x) (coordinateGram_iotaC hx)
    (a.compContinuousLinearMap (fderiv ℝ iotaC (iotaC x)))
    (b.compContinuousLinearMap (fderiv ℝ iotaC (iotaC x)))
  rw [compCLM_iotaC_comp hx, compCLM_iotaC_comp hx] at key
  unfold dualFormPairing formPairing inverseGram
  exact congrArg ((k.factorial : ℝ)⁻¹ * ·) key

/-- The pointwise dual metric of two dual forms. -/
def dualPairingFn (a b : DForm Γ n k) (x : Coordinates) : ℝ :=
  dualFormPairing n k x (DForm.fn a x) (DForm.fn b x)

theorem dualPairingFn_eq_std (h : Admissible Γ) (a b : DForm Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    dualPairingFn a b x = pairingFn (toStd h n k a) (toStd h n k b) (iotaC x) := by
  unfold dualPairingFn pairingFn
  rw [dualFormPairing_eq hx, toStd_fn, toStd_fn, ioPull_apply n k _ (iotaC_mem hx),
    ioPull_apply n k _ (iotaC_mem hx), iotaC_iotaC hx]

theorem dualPairingFn_action (h : Admissible Γ) (a b : DForm Γ n k) (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    dualPairingFn a b (coordinateAction (γ : RealGL) x) = dualPairingFn a b x := by
  have hmem : coordinateAction (γ : RealGL) x ∈ positiveCoordinates :=
    coordinateAction_mem (γ : RealGL) x hx
  have e1 := dualPairingFn_eq_std h a b hmem
  have e2 := dualPairingFn_eq_std h a b hx
  have e3 := iotaC_action (γ : RealGL) hx
  have e4 := pairingFn_action h.theta (toStd h n k a) (toStd h n k b)
    ⟨thetaHom (γ : RealGL), theta_mem_thetaImage γ.2⟩ (iotaC_mem hx)
  exact e1.trans ((congrArg (pairingFn (toStd h n k a) (toStd h n k b)) e3).trans (e4.trans e2.symm))

open Classical in
/-- The `Γ`-invariant dual pointwise metric of two dual forms, as a function on the orbit space. -/
def dualScalar (a b : DForm Γ n k) : OrbitSpace Γ → ℝ :=
  if h : Admissible Γ then
    Quotient.lift (s := MulAction.orbitRel Γ Space)
      (fun S : Space => dualPairingFn a b (coordinateChart S)) (by
        intro S T hST
        obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hST
        subst hγ
        have hc : coordinateChart (γ • T) = coordinateAction (γ : RealGL) (coordinateChart T) :=
          coordinateChart_act (γ : RealGL) T
        change dualPairingFn a b (coordinateChart (γ • T)) = dualPairingFn a b (coordinateChart T)
        rw [hc]
        exact dualPairingFn_action h a b γ (extract_mem T))
  else fun _ => 0

theorem dualScalar_proj (h : Admissible Γ) (a b : DForm Γ n k) (S : Space) :
    dualScalar a b (proj Γ S) = dualPairingFn a b (coordinateChart S) := by
  unfold dualScalar
  rw [dite_eq_left h]
  rfl

/-- The orbit-space map induced by the Cartan involution, from `Γ` to its Cartan image. -/
abbrev qIota (Γ : Subgroup RealGL) : OrbitSpace Γ → OrbitSpace (thetaImage Γ) :=
  quotIota Γ (thetaImage Γ) (fun _ ha => theta_mem_thetaImage ha)

theorem dualScalar_eq_std (h : Admissible Γ) (a b : DForm Γ n k) (q : OrbitSpace Γ) :
    dualScalar a b q = scalarPairing (toStd h n k a) (toStd h n k b) (qIota Γ q) := by
  obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
  have h1 : qIota Γ (proj Γ S) = proj (thetaImage Γ) (iota S) := rfl
  have h2 := scalarPairing_proj h.theta (toStd h n k a) (toStd h n k b) (iota S)
  have hS : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have h3 := dualPairingFn_eq_std h a b hS
  exact (dualScalar_proj h a b S).trans
    (h3.trans ((congrArg (pairingFn (toStd h n k a) (toStd h n k b)) (iotaC_chart S)).trans h2.symm))

/-- The dual `L²` pairing: the integral of the dual pointwise metric against the Riemannian volume of
the orbit space. -/
def dualL2 (a b : DForm Γ n k) : ℝ := ∫ q, dualScalar a b q ∂quotientVolume Γ

/-- The squared dual `L²` norm. -/
def dualNormSq (a : DForm Γ n k) : ℝ := dualL2 a a

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
