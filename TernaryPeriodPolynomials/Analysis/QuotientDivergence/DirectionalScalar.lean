module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.ScalarDescent
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingScalar
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence

@[expose] public section


/-! Directional derivatives of quotient scalars along actual deck tangent fields descend smoothly. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  SmoothCoveringDeRham SmoothDeRhamGluing PolynomialFormConnection Set Filter
open scoped ContDiff Manifold Topology

def coordinateDirectional (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates) (x : Coordinates) : ℝ :=
  fderiv ℝ (liftScalar φ) x (V x)

theorem liftScalar_contDiff {φ : OrbitSpace → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) :
    ContDiffOn ℝ ∞ (liftScalar φ) positiveCoordinates := by
  simpa only [liftedDomain_univ] using liftScalar_smooth (U := univ) hφ.contMDiffOn

theorem coordinateDirectional_deck (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hV : IsDeckVectorField V) (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    coordinateDirectional φ V (deckMap g x) = coordinateDirectional φ V x := by
  have hs := liftScalar_contDiff hφ
  have hd := ((deckMap_smooth g x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have ht := ((hs _ (deckMap_mem g hx)).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds (deckMap_mem g hx))).differentiableAt (by simp)
  have he : (liftScalar φ ∘ deckMap g) =ᶠ[𝓝 x] liftScalar φ := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact liftScalar_deck φ g hy
  have hc := fderiv_comp x ht hd
  have hf : (fderiv ℝ (liftScalar φ) (deckMap g x)).comp (fderiv ℝ (deckMap g) x) =
      fderiv ℝ (liftScalar φ) x := hc.symm.trans he.fderiv_eq
  unfold coordinateDirectional
  rw [hV g x hx]
  exact congrArg (fun L : Coordinates →L[ℝ] ℝ => L (V x)) hf

theorem contDiffOn_coordinateDirectional (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hV : ContDiffOn ℝ ∞ V positiveCoordinates) :
    ContDiffOn ℝ ∞ (coordinateDirectional φ V) positiveCoordinates := by
  exact ((liftScalar_contDiff hφ).fderiv_of_isOpen isOpen_positiveCoordinates (by simp)).clm_apply hV

def directional (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates) : OrbitSpace → ℝ :=
  descend (coordinateDirectional φ V)

theorem directional_coordinateProjection (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hV : IsDeckVectorField V) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    directional φ V (coordinateProjection x) = fderiv ℝ (liftScalar φ) x (V x) :=
  descend_coordinateProjection _ (coordinateDirectional_deck φ hφ V hV) x hx

theorem contMDiff_directional (φ : OrbitSpace → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ) (V : Coordinates → Coordinates)
    (hV : IsDeckVectorField V) (hVs : ContDiffOn ℝ ∞ V positiveCoordinates) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (directional φ V) :=
  contMDiff_descend _ (contDiffOn_coordinateDirectional φ hφ V hVs)
    (coordinateDirectional_deck φ hφ V hV)

end TernaryPoly.QuotientScalarDescent
