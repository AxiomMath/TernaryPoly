module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Support
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.GraphLimit

@[expose] public section


/-! Finite scalar reconstruction is detected by genuine compact tests of a weakly supported form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set PolynomialFormHilbert PolynomialCoefficientMetric PolynomialFormCoordinates
  SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Manifold
attribute [local instance] cutoffHilbertModule

theorem inner_bounded_coreScalarMultiply (n k : ℕ) (ψ : OrbitSpace → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ ψ)
    (L : Hilbert n k →L[ℝ] Hilbert n k)
    (hL : ∀ a : Core n k, L (inclusion n k a) = inclusion n k (coreScalarMultiply n k ψ hψ a))
    (u : Hilbert n k) (a : Core n k) :
    inner ℝ (L u) (inclusion n k a) =
      inner ℝ u (inclusion n k (coreScalarMultiply n k ψ hψ a)) := by
  refine (inclusion_dense n k).induction_on u
    (isClosed_eq (L.continuous.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro b
  exact (congrArg (fun v => inner ℝ v (inclusion n k a)) (hL b)).trans
    (inner_coreScalarMultiply n k ψ hψ b a)

theorem quotientSupport_finite_scalar_residual (n k : ℕ) {ι : Type*} [Fintype ι]
    (ψ : ι → OrbitSpace → ℝ)
    (hψ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (ψ i))
    (U : Set OrbitSpace) (hU : IsOpen U) (he : ∀ q ∈ U, ∑ i, ψ i q = 1)
    (a : Core n k) :
    quotientSupport (a - ∑ i, coreScalarMultiply n k (ψ i) (hψ i) a).val ⊆ Uᶜ := by
  classical
  apply closure_minimal _ hU.isClosed_compl
  rintro q ⟨x, hx, rfl⟩ hq
  apply hx
  change a.val.val.val x - (∑ i, coreScalarMultiply n k (ψ i) (hψ i) a).val.val.val x = 0
  have hv : (∑ i, coreScalarMultiply n k (ψ i) (hψ i) a).val.val.val x = a.val.val.val x := by
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ i, (coreScalarMultiply n k (ψ i) (hψ i) a).val.val.val x) = _
    simp only [coreScalarMultiply_apply]
    exact (Finset.sum_smul (s := Finset.univ) (f := fun i => ψ i (coordinateProjection x))
      (x := a.val.val.val x)).symm.trans
        ((congrArg (fun t : ℝ => t • a.val.val.val x) (he _ hq)).trans (one_smul ℝ _))
  rw [hv, sub_self]

theorem finite_scalar_reconstruction_of_weakSupport (n k : ℕ) {ι : Type*} [Fintype ι]
    (ψ : ι → OrbitSpace → ℝ)
    (hψ : ∀ i, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (ψ i))
    (L : ι → Hilbert n k →L[ℝ] Hilbert n k)
    (hL : ∀ i (a : Core n k), L i (inclusion n k a) =
      inclusion n k (coreScalarMultiply n k (ψ i) (hψ i) a))
    (K U : Set OrbitSpace) (hU : IsOpen U) (hKU : K ⊆ U)
    (he : ∀ q ∈ U, ∑ i, ψ i q = 1)
    (u : Hilbert n k) (hu : HasWeakSupportIn n k K u) : ∑ i, L i u = u := by
  classical
  apply ext_inner_right ℝ
  intro v
  refine (inclusion_dense n k).induction_on v
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  have hd : Disjoint (quotientSupport (a - ∑ i, coreScalarMultiply n k (ψ i) (hψ i) a).val) K := by
    apply Set.disjoint_left.mpr
    intro q hq hqK
    exact quotientSupport_finite_scalar_residual n k ψ hψ U hU he a hq (hKU hqK)
  let b (i : ι) := coreScalarMultiply n k (ψ i) (hψ i) a
  have hz := hu (a - ∑ i, b i) hd
  have hm : inclusion n k (a - ∑ i, b i) = inclusion n k a - ∑ i, inclusion n k (b i) :=
    ((inclusion n k).map_sub a (∑ i, b i)).trans
      (congrArg (inclusion n k a - ·) (map_sum (inclusion n k) b Finset.univ))
  have hz' : inner ℝ u (inclusion n k a - ∑ i, inclusion n k (b i)) = 0 :=
    (congrArg (inner ℝ u) hm).symm.trans hz
  have hi : inner ℝ u (inclusion n k a) = inner ℝ u (∑ i, inclusion n k (b i)) :=
    sub_eq_zero.mp ((inner_sub_right u (inclusion n k a) (∑ i, inclusion n k (b i))).symm.trans hz')
  calc
    _ = ∑ i, inner ℝ (L i u) (inclusion n k a) := sum_inner Finset.univ (fun i => L i u) _
    _ = ∑ i, inner ℝ u (inclusion n k (b i)) := Finset.sum_congr rfl (fun i _ =>
      inner_bounded_coreScalarMultiply n k (ψ i) (hψ i) (L i) (hL i) u a)
    _ = inner ℝ u (∑ i, inclusion n k (b i)) := (inner_sum Finset.univ (fun i => inclusion n k (b i)) u).symm
    _ = _ := hi.symm

end TernaryPoly.PolynomialFormConnection
