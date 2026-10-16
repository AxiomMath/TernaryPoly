module

public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.Cutoff

@[expose] public section



/-! Genuine scalar-cutoff commutators of the actual polynomial-form differential and adjoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped ContDiff Matrix.Norms.Elementwise

/-- The exact affine-coordinate principal symbol of exterior differentiation. -/
def localDifferentialSymbol (n k : ℕ) (c : Coordinates → ℝ)
    (w : Coordinates → FormValue n k) (x : Coordinates) : FormValue n (k + 1) :=
  (coordinates n (k + 1)).symm (fun j => matrixSymbol (fun d : Fin 5 => Pi.single d 1)
    (differentialCoefficients n k) c (components n k w) j x)

/-- The genuine inverse-Gram transpose of that symbol. -/
def localAdjointSymbol (n k : ℕ) (c : Coordinates → ℝ)
    (w : Coordinates → FormValue n (k + 1)) (x : Coordinates) : FormValue n k :=
  (coordinates n k).symm (fun i => weightedSymbolTranspose (weightedGram n k)
    (weightedGram n (k + 1)) (fun d : Fin 5 => Pi.single d 1)
    (differentialCoefficients n k) c (components n (k + 1) w) i x)

theorem components_cutoff (n k : ℕ) (c : Coordinates → ℝ) (w : Coordinates → FormValue n k) :
    components n k (fun x => c x • w x) = fun i x => c x * components n k w i x := by
  funext i x
  simp only [components, map_smul, Pi.smul_apply, smul_eq_mul]

theorem differentiableAt_components (n k : ℕ) {w : Coordinates → FormValue n k}
    {x : Coordinates} (hw : DifferentiableAt ℝ w x) (i : Index n k) :
    DifferentiableAt ℝ (components n k w i) x := by
  let L : FormValue n k →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (coordinates n k).toContinuousLinearMap
  change DifferentiableAt ℝ (L ∘ w) x
  exact L.differentiableAt.comp x hw

/-- The actual exterior derivative obeys its exact first-order cutoff law. -/
theorem extDeriv_cutoff (n k : ℕ) (c : Coordinates → ℝ) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hc : DifferentiableAt ℝ c x) (hw : DifferentiableAt ℝ w x) :
    extDeriv (fun y => c y • w y) x = c x • extDeriv w x + localDifferentialSymbol n k c w x := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  have hcw : DifferentiableAt ℝ (fun y => c y • w y) x :=
    DifferentiableAt.fun_smul (𝕜 := ℝ) (F := FormValue n k) hc hw
  apply (coordinates n (k + 1)).injective
  rw [map_add, map_smul]
  funext j
  change components n (k + 1) (extDeriv (fun y => c y • w y)) j x =
    c x * components n (k + 1) (extDeriv w) j x + _
  rw [extDeriv_eq_matrixFirstOrder n k _ hcw, components_cutoff,
    extDeriv_eq_matrixFirstOrder n k _ hw]
  simp only [localDifferentialSymbol, ContinuousLinearEquiv.apply_symm_apply]
  exact matrixFirstOrder_cutoff (I := Index n k) (J := Index n (k + 1)) (K := Fin 5)
    (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k) (fun _ _ _ _ => 0) c (components n k w) hc
    (differentiableAt_components n k hw) j

/-- The actual weighted local adjoint obeys the opposite cutoff law, including metric and density. -/
theorem localAdjoint_cutoff (n k : ℕ) (c : Coordinates → ℝ)
    (w : Coordinates → FormValue n (k + 1)) {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (hc : DifferentiableAt ℝ c x) (hw : DifferentiableAt ℝ w x) :
    localAdjoint n k (fun y => c y • w y) x =
      c x • localAdjoint n k w x - localAdjointSymbol n k c w x := by
  apply (coordinates n k).injective
  simp only [localAdjoint, localAdjointSymbol, ContinuousLinearEquiv.map_sub,
    ContinuousLinearEquiv.map_smul, ContinuousLinearEquiv.apply_symm_apply]
  funext i
  rw [components_cutoff]
  apply weightedMatrixAdjoint_cutoff
  · intro j l d
    exact differentiableAt_const _
  · intro j l
    have h := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k + 1)) j) l
    exact h.differentiableOn (by simp) x hx |>.differentiableAt (isOpen_positiveCoordinates.mem_nhds hx)
  · exact hc
  · exact differentiableAt_components n (k + 1) hw

end TernaryPoly.PolynomialFormCoordinates
