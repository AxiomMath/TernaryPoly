module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Mult
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Operators
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.SymbolTransport
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingScalar

@[expose] public section


/-! # General coercivity, Tier B: commutators of the exterior derivative with invariant multipliers

For a smooth `Γ`-invariant function `c`, the commutator `d (c ·) - c d` on compactly supported
equivariant forms is the zero-order operator `a ↦ dc ∧ a`.  When the invariant gradient of `c` is
bounded by `B`, its `L²` operator norm is at most `√K · B` with `K` depending only on the degrees.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
  TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormConnection
  TernaryPoly.SymmetricSpaceTraceMetric
open MeasureTheory Set Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n m : ℕ}

theorem add_add_neg_one_smul {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : V) :
    A + B + (-1 : ℝ) • B = A := by
  rw [neg_one_smul, add_neg_cancel_right]

namespace InvMult

variable (c : InvMult Γ)

/-- The commutator `d (c a) - c d a` of the exterior derivative with multiplication by `c`. -/
def commCore (n m : ℕ) : CForm Γ n m →ₗ[ℝ] CForm Γ n (m + 1) :=
  (CForm.d Γ n m).comp c.mulMap + (-1 : ℝ) • c.mulMap.comp (CForm.d Γ n m)

theorem fn_commCore_eq (a : CForm Γ n m) (x : Coordinates) :
    CForm.fn (c.commCore n m a) x =
      CForm.fn (CForm.d Γ n m (c.mulMap a)) x +
        (-1 : ℝ) • CForm.fn (c.mulMap (CForm.d Γ n m a)) x := rfl

/-- The commutator is pointwise the wedge with the differential of `c`. -/
theorem fn_commCore (a : CForm Γ n m) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (c.commCore n m a) x =
      TernaryPoly.SmoothDeRhamGluing.scalarWedge (fderiv ℝ c.toFun x) (CForm.fn a x) := by
  have hnhds : positiveCoordinates ∈ 𝓝 x := isOpen_positiveCoordinates.mem_nhds hx
  have hc : DifferentiableAt ℝ c.toFun x := ((c.smooth.contDiffAt hnhds).differentiableAt (by simp))
  have ha : DifferentiableAt ℝ (CForm.fn a) x :=
    ((CForm.smooth a x hx).contDiffAt hnhds).differentiableAt (by simp)
  have he : CForm.fn (c.mulMap a) =ᶠ[𝓝 x] fun y => c.toFun y • CForm.fn a y := by
    filter_upwards [hnhds] with y hy
    exact c.fn_mulMap a hy
  have e1 : CForm.fn (CForm.d Γ n m (c.mulMap a)) x = extDeriv (CForm.fn (c.mulMap a)) x :=
    CForm.d_apply _ hx
  have e2 : CForm.fn (c.mulMap (CForm.d Γ n m a)) x = c.toFun x • extDeriv (CForm.fn a) x :=
    (c.fn_mulMap _ hx).trans (congrArg (fun z : FormValue n (m + 1) => c.toFun x • z) (CForm.d_apply _ hx))
  have e3 : extDeriv (CForm.fn (c.mulMap a)) x =
      TernaryPoly.SmoothDeRhamGluing.scalarWedge (fderiv ℝ c.toFun x) (CForm.fn a x) +
        c.toFun x • extDeriv (CForm.fn a) x :=
    (he.extDeriv_eq).trans (TernaryPoly.SmoothDeRhamGluing.extDeriv_scalar hc ha)
  refine (c.fn_commCore_eq a x).trans ?_
  have e4 : CForm.fn (CForm.d Γ n m (c.mulMap a)) x +
      (-1 : ℝ) • CForm.fn (c.mulMap (CForm.d Γ n m a)) x =
      (TernaryPoly.SmoothDeRhamGluing.scalarWedge (fderiv ℝ c.toFun x) (CForm.fn a x) +
        c.toFun x • extDeriv (CForm.fn a) x) + (-1 : ℝ) • (c.toFun x • extDeriv (CForm.fn a) x) :=
    congrArg₂ (fun u v : FormValue n (m + 1) => u + (-1 : ℝ) • v) (e1.trans e3) e2
  exact e4.trans (add_add_neg_one_smul (V := FormValue n (m + 1)) _ _)

/-- A bound `B` for the invariant gradient of `c`. -/
def Slope (B : ℝ) : Prop :=
  ∀ x ∈ positiveCoordinates, ∀ v : Coordinates,
    |fderiv ℝ c.toFun x v| ≤ B * Real.sqrt (coordinatePair x v v)

theorem scalarPairing_commCore_le [hΓ : Fact (Admissible Γ)] {K B : ℝ} (hs : c.Slope B)
    (hH : ∀ x ∈ positiveCoordinates, ∀ (α : Coordinates →L[ℝ] ℝ),
      (∀ v, |α v| ≤ B * Real.sqrt (coordinatePair x v v)) → ∀ a : FormValue n m,
        formPairing n (m + 1) x (TernaryPoly.SmoothDeRhamGluing.scalarWedge α a)
          (TernaryPoly.SmoothDeRhamGluing.scalarWedge α a) ≤ K * B ^ 2 * formPairing n m x a a)
    (a : CForm Γ n m) (q : OrbitSpace Γ) :
    scalarPairing (c.commCore n m a) (c.commCore n m a) q ≤ K * B ^ 2 * scalarPairing a a q := by
  obtain ⟨S, rfl⟩ := proj_surjective (Γ := Γ) q
  have hx : coordinateChart S ∈ positiveCoordinates := extract_mem S
  have e0 : pairingFn (c.commCore n m a) (c.commCore n m a) (coordinateChart S) =
      formPairing n (m + 1) (coordinateChart S)
        (CForm.fn (c.commCore n m a) (coordinateChart S))
        (CForm.fn (c.commCore n m a) (coordinateChart S)) := rfl
  have e1 : scalarPairing (c.commCore n m a) (c.commCore n m a) (proj Γ S) =
      formPairing n (m + 1) (coordinateChart S)
        (TernaryPoly.SmoothDeRhamGluing.scalarWedge (fderiv ℝ c.toFun (coordinateChart S))
          (CForm.fn a (coordinateChart S)))
        (TernaryPoly.SmoothDeRhamGluing.scalarWedge (fderiv ℝ c.toFun (coordinateChart S))
          (CForm.fn a (coordinateChart S))) := by
    refine (scalarPairing_proj hΓ.out _ _ S).trans (e0.trans ?_)
    rw [c.fn_commCore a hx]
  have e2 : scalarPairing a a (proj Γ S) =
      formPairing n m (coordinateChart S) (CForm.fn a (coordinateChart S))
        (CForm.fn a (coordinateChart S)) := scalarPairing_proj hΓ.out a a S
  rw [e1, e2]
  exact hH _ hx _ (hs _ hx) _

theorem normSq_le_of_scalarPairing_le [Fact (Admissible Γ)] {k l : ℕ} {r : ℝ}
    (a : CForm Γ n k) (b : CForm Γ n l)
    (h : ∀ q, scalarPairing a a q ≤ r * scalarPairing b b q) : normSq a ≤ r * normSq b := by
  rw [normSq_eq, normSq_eq, ← integral_const_mul]
  exact integral_mono (integrable_scalarPairing _ _)
    ((integrable_scalarPairing _ _).const_mul _) h

/-- One constant (depending only on the degrees) bounds all commutators with a given invariant
gradient bound. -/
theorem exists_normSq_commCore_le (n m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Γ : Subgroup RealGL) [Fact (Admissible Γ)] (c : InvMult Γ) (B : ℝ),
      0 ≤ B → c.Slope B → ∀ a : CForm Γ n m,
        normSq (c.commCore n m a) ≤ K * B ^ 2 * normSq a := by
  obtain ⟨K, hK, H⟩ := exists_scalarWedge_metric_bound n m
  refine ⟨K, hK, fun Γ hΓ c B hB hs a => ?_⟩
  exact normSq_le_of_scalarPairing_le (c.commCore n m a) a
    (c.scalarPairing_commCore_le hs (fun x hx α hα b => H B hB x hx α hα b) a)

end InvMult

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
