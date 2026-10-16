module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Smooth
public import TernaryPeriodPolynomials.Analysis.BilinearVolumeDensity
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


/-! Genuine finite coordinates for form fibers, and their density-weighted positive Gram matrix. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts SymmetricSpaceRiemannian
open scoped ContDiff Matrix.Norms.Elementwise

abbrev Index (n k : ℕ) := Fin (Module.finrank ℝ (FormValue n k))

def basis (n k : ℕ) : Module.Basis (Index n k) ℝ (FormValue n k) :=
  Module.finBasis ℝ (FormValue n k)

def coordinates (n k : ℕ) : FormValue n k ≃L[ℝ] (Index n k → ℝ) :=
  (basis n k).equivFun.toContinuousLinearEquiv

/-- Continuous linear maps commute with finite sums.  The statement has the types fixed by the
map itself, so that rewriting avoids the costly `AddMonoidHomClass` search of the generic
`map_sum` on the form-fibre types. -/
theorem clm_map_sum {R E F ι : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F] (g : E →L[R] F) (s : Finset ι) (f : ι → E) :
    g (∑ i ∈ s, f i) = ∑ i ∈ s, g (f i) := map_sum g f s

/-- Continuous linear maps preserve subtraction (see `clm_map_sum`). -/
theorem clm_map_sub {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
    [AddCommGroup F] [Module R F] [TopologicalSpace F] (g : E →L[R] F) (x y : E) :
    g (x - y) = g x - g y := map_sub g x y

/-- Continuous linear maps preserve zero (see `clm_map_sum`). -/
theorem clm_map_zero {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F] (g : E →L[R] F) : g 0 = 0 := map_zero g

/-- Continuous linear maps preserve addition (see `clm_map_sum`). -/
theorem clm_map_add {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F] (g : E →L[R] F) (x y : E) :
    g (x + y) = g x + g y := map_add g x y

/-- Continuous linear maps commute with scalar multiplication (see `clm_map_sum`). -/
theorem clm_map_smul {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F] (g : E →L[R] F) (c : R) (x : E) :
    g (c • x) = c • g x := map_smul g c x

/-- Coordinates commute with finite sums.  This is proved from the additive structure alone, since
the generic `map_sum` makes a costly instance search on the form-fibre types. -/
theorem coordinates_sum {ι : Type*} (n k : ℕ) (s : Finset ι) (f : ι → FormValue n k) :
    coordinates n k (∑ i ∈ s, f i) = ∑ i ∈ s, coordinates n k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearEquiv.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearEquiv.map_add, ih]

/-- This bilinear form is exactly the genuine scalar metric times the genuine volume density. -/
def weightedBilin (n k : ℕ) (x : Coordinates) :
    (Index n k → ℝ) →ₗ[ℝ] (Index n k → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => coordinateDensity x *
    formPairing n k x ((coordinates n k).symm u) ((coordinates n k).symm v))
    (by intro u v w; rw [map_add, formPairing_add_left, mul_add])
    (by intro t u v; rw [map_smul, formPairing_smul_left]; simp only [smul_eq_mul]; ring)
    (by intro u v w; rw [map_add, formPairing_add_right, mul_add])
    (by intro t u v; rw [map_smul, formPairing_smul_right]; simp only [smul_eq_mul]; ring)

/-- The actual Gram matrix in a genuine basis, without redundant alternating coordinates. -/
def weightedGram (n k : ℕ) (x : Coordinates) : Matrix (Index n k) (Index n k) ℝ :=
  LinearMap.BilinForm.toMatrix' (weightedBilin n k x)

@[simp] theorem weightedGram_apply (n k : ℕ) (x : Coordinates) (i j : Index n k) :
    weightedGram n k x i j = coordinateDensity x *
      formPairing n k x ((coordinates n k).symm (Pi.single i 1))
        ((coordinates n k).symm (Pi.single j 1)) := rfl

/-- The finite coordinate pairing is exactly the original density-weighted form metric. -/
theorem weightedGram_pairing (n k : ℕ) (x : Coordinates) (a b : FormValue n k) :
    (coordinates n k a) ⬝ᵥ (weightedGram n k x).mulVec (coordinates n k b) =
      coordinateDensity x * formPairing n k x a b := by
  rw [← Matrix.toBilin'_apply']
  change Matrix.toBilin' (LinearMap.BilinForm.toMatrix' (weightedBilin n k x)) _ _ = _
  rw [Matrix.toBilin'_toMatrix']
  change coordinateDensity x * formPairing n k x _ _ = _
  rw [(coordinates n k).symm_apply_apply, (coordinates n k).symm_apply_apply]

/-- The metric and density are both positive on the actual coordinate domain. -/
theorem weightedGram_posDef (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (weightedGram n k x).PosDef := by
  apply BilinearVolumeDensity.gram_posDef
  · intro u v
    change coordinateDensity x * _ = coordinateDensity x * _
    rw [formPairing_symm n k x hx]
  · intro u hu
    apply mul_pos (coordinateDensity_pos x hx)
    exact formPairing_positive n k x hx _ (fun h => hu ((coordinates n k).symm.injective (h.trans (map_zero _).symm)))

end TernaryPoly.PolynomialFormCoordinates
