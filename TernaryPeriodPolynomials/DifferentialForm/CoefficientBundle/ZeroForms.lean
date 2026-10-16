module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.LocalSections
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Equivariant

@[expose] public section

/-! Degree-zero covering forms encode actual coefficient-valued functions, with no differential assumptions. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts SmoothLocalDeRham SmoothCoveringDeRham
open Set Filter Topology Bundle Manifold ContinuousAlternatingMap
open scoped ContDiff Manifold

def decodeZero (n : ℕ) (w : Coordinates [⋀^Fin 0]→L[ℝ] Coefficients n) : Coefficients n :=
  zeroEquiv.symm w

@[simp] theorem decodeZero_apply (n : ℕ) (w : Coordinates [⋀^Fin 0]→L[ℝ] Coefficients n) :
    decodeZero n w = w (fun i => Fin.elim0 i) := by
  simp only [decodeZero, zeroEquiv, constOfIsEmptyLIE_symm_apply]
  congr 1
  exact Subsingleton.elim _ _

@[simp] theorem decodeZero_encode (n : ℕ) (v : Coefficients n) :
    decodeZero n (zeroEquiv (E := Coordinates) v) = v := zeroEquiv.symm_apply_apply v

theorem decodeZero_pull (n : ℕ) (φ : Coordinates → Coordinates)
    (w : RawForm Coordinates (Coefficients n) 0) (x : Coordinates) :
    decodeZero n (pullRaw φ w x) = decodeZero n (w (φ x)) := by
  rw [decodeZero_apply, decodeZero_apply]
  change w (φ x) (fun i => (fderiv ℝ φ x) (Fin.elim0 i)) = w (φ x) (fun i => Fin.elim0 i)
  congr 1
  exact Subsingleton.elim _ _

@[simp] theorem decodeZero_coefficient (n : ℕ) (g : DeckGroup)
    (w : Coordinates [⋀^Fin 0]→L[ℝ] Coefficients n) :
    decodeZero n (coefficientFormMap (coefficientMap (deckRepresentation n) g) 0 w) =
      coefficientAction n g (decodeZero n w) := rfl

theorem zero_equivariant_iff (n : ℕ) (U : Set OrbitSpace) (w : RawForm Coordinates (Coefficients n) 0) :
    SmoothCoveringDeRham.IsEquivariant (deckRepresentation n) U w ↔
      ∀ g x, x ∈ liftedDomain U → decodeZero n (w (deckMap g x)) = coefficientAction n g (decodeZero n (w x)) := by
  constructor
  · intro h g x hx
    have he := congrArg (decodeZero n) (h g x hx)
    simpa only [decodeZero_pull, decodeZero_coefficient] using he
  · intro h g x hx
    apply zeroEquiv.symm.injective
    change decodeZero n _ = decodeZero n _
    rw [decodeZero_pull, decodeZero_coefficient]
    exact h g x hx

def coordinateFunction (n : ℕ) (f : Space → Coefficients n) (x : Coordinates) : Coefficients n :=
  f (coordinateChart.symm x)

theorem smooth_coordinateFunction (n : ℕ) {U : Set OrbitSpace} (f : Space → Coefficients n)
    (hf : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ f (quotientProjection ⁻¹' U)) :
    ContDiffOn ℝ ∞ (coordinateFunction n f) (liftedDomain U) := by
  have h := hf.comp (coordinateChart_symm_contMDiffOn.mono
    (show liftedDomain U ⊆ coordinateChart.target from fun x hx => by simpa only [coordinateChart_target] using hx.1))
    (fun x hx => hx.2)
  exact h.contDiffOn

def coveringZeroForm (n : ℕ) {U : Set OrbitSpace} (f : Space → Coefficients n)
    (hf : IsEquivariantFunction n f)
    (hs : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ f (quotientProjection ⁻¹' U)) :
    EquivariantForm (deckRepresentation n) U 0 :=
  ⟨ofFunction (coordinateFunction n f) (smooth_coordinateFunction n f hs), by
    apply (zero_equivariant_iff n U _).mpr
    intro g x hx
    rw [ofFunction_apply _ _ (deckMap_liftedDomain g U hx), ofFunction_apply _ _ hx,
      decodeZero_encode, decodeZero_encode]
    change f (coordinateChart.symm (deckMap g x)) = coefficientAction n g (f (coordinateChart.symm x))
    rw [deckMap_inverseChart g hx.1]
    exact hf g _⟩

end TernaryPoly.PolynomialCoefficientBundle
