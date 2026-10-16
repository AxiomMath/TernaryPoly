module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.LocalTranspose
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffConvolutionBound
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffBound
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffConvergence
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.CutoffSymbol
public import TernaryPeriodPolynomials.DifferentialForm.DifferentialExtensionFormula
public import TernaryPeriodPolynomials.DifferentialForm.AdjointExtensionFormula
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientExtension
public import TernaryPeriodPolynomials.DifferentialForm.DifferentialCoefficientExtension
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Locality

@[expose] public section


/-! # General coercivity, Tier B: Friedrichs estimates for the local mollifier

For a first-order operator `D` on forms (the exterior derivative or the codifferential) given in the
fixed coordinates by a matrix of compactly supported coefficients, the cutoff mollifier satisfies
a fixed-scale bound for `D ∘ (η (κ_c ∗ (χ ·)))`, a scale-uniform bound for the commutator with `D`
(Friedrichs), and the commutator converges to the symbol of `D`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.CompactCoordinateIntegration TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

/-- A first-order operator on forms written in the fixed coordinates by compactly supported
smooth coefficient arrays on a compact subset `K` of the positive coordinates. -/
structure FODatum (n kin kout : ℕ) (K : Set Coordinates) where
  D : (Coordinates → FormValue n kin) → (Coordinates → FormValue n kout)
  Kι : Type
  [fin : Fintype Kι]
  v : Kι → Coordinates
  A : Index n kout → Index n kin → Kι → Coordinates → ℝ
  B : Index n kout → Index n kin → Kι → Coordinates → ℝ
  A_smooth : ∀ j i q, ContDiff ℝ ∞ (A j i q)
  B_smooth : ∀ j i q, ContDiff ℝ ∞ (B j i q)
  A_compact : ∀ j i q, HasCompactSupport (A j i q)
  B_compact : ∀ j i q, HasCompactSupport (B j i q)
  matrix : ∀ g : Coordinates → FormValue n kin, ContDiff ℝ ∞ g → tsupport g ⊆ K →
    ∀ j, components n kout (D g) j = matrixFirstOrder v A B (components n kin g) j
  smooth : ∀ g : Coordinates → FormValue n kin, ContDiff ℝ ∞ g → tsupport g ⊆ positiveCoordinates →
    ContDiff ℝ ∞ (D g)
  tsupport_sub : ∀ g : Coordinates → FormValue n kin, tsupport (D g) ⊆ tsupport g
  loc : ∀ (g₁ g₂ : Coordinates → FormValue n kin) (y : Coordinates), g₁ =ᶠ[𝓝 y] g₂ → D g₁ y = D g₂ y

attribute [instance] FODatum.fin

/-- The three cutoffs used by the regulariser: `χ` inside, `η` outside, `θ` a buffer. -/
structure Cuts where
  χ : Coordinates → ℝ
  η : Coordinates → ℝ
  θ : Coordinates → ℝ
  χ_smooth : ContDiff ℝ ∞ χ
  η_smooth : ContDiff ℝ ∞ η
  θ_smooth : ContDiff ℝ ∞ θ
  χ_compact : HasCompactSupport χ
  η_compact : HasCompactSupport η
  θ_compact : HasCompactSupport θ
  χ_pos : tsupport χ ⊆ positiveCoordinates
  η_pos : tsupport η ⊆ positiveCoordinates
  θ_pos : tsupport θ ⊆ positiveCoordinates
  η_one : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] 1
  θ_one : ∀ x ∈ tsupport χ ∪ tsupport η, θ =ᶠ[𝓝 x] 1
  M : ℝ
  M_nonneg : 0 ≤ M
  η_bound : ∀ x, ‖η x‖ ≤ M

namespace Cuts

variable (C : Cuts)

theorem θ_eq_one_of_mem {x : Coordinates} (hx : x ∈ tsupport C.χ ∪ tsupport C.η) : C.θ x = 1 :=
  (C.θ_one x hx).self_of_nhds.trans (Pi.one_apply x)

theorem tsupport_χ_sub_θ : tsupport C.χ ⊆ tsupport C.θ := fun x hx =>
  subset_tsupport C.θ (by
    rw [Function.mem_support, C.θ_eq_one_of_mem (Or.inl hx)]
    exact one_ne_zero)

theorem tsupport_η_sub_θ : tsupport C.η ⊆ tsupport C.θ := fun x hx =>
  subset_tsupport C.θ (by
    rw [Function.mem_support, C.θ_eq_one_of_mem (Or.inr hx)]
    exact one_ne_zero)

end Cuts

section FirstOrder

variable {n kin kout : ℕ} (C : Cuts) (F : FODatum n kin kout (tsupport C.θ))

/-- Fixed-scale bound: the mollifier gains one derivative. -/
theorem exists_compL2_D_frMol_le {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : Coordinates → FormValue n kin},
      ContDiffOn ℝ ∞ f positiveCoordinates →
      compL2 (F.D (frMol n kin C.χ C.η c f)) ≤ A * compL2 (fun y => C.χ y • f y) := by
  have hκ : ContDiff ℝ 1 (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) :=
    (TernaryPoly.CompactScalarMollifier.kernel_contDiff Coordinates volume c).of_le (by simp)
  have hcκ := TernaryPoly.CompactScalarMollifier.kernel_compact Coordinates volume c hc.ne'
  have hs := fun j => exists_matrix_cutoff_convolution_bound volume F.v
    (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c) C.η F.A F.B hκ hcκ
    (C.η_smooth.of_le (by simp)) C.η_compact
    (fun j i q => (F.A_smooth j i q).continuous) (fun j i q => (F.B_smooth j i q).continuous) j
  choose Cj hCj hbound using hs
  refine ⟨∑ j, Cj j, Finset.sum_nonneg (fun j _ => hCj j), fun {f} hf => ?_⟩
  have hg : ContDiff ℝ ∞ (frMol n kin C.χ C.η c f) :=
    contDiff_frMol C.χ_smooth C.χ_pos C.η_smooth hc.ne' hf
  have hsub : tsupport (frMol n kin C.χ C.η c f) ⊆ tsupport C.θ :=
    (tsupport_frMol_subset C.χ C.η c f).trans C.tsupport_η_sub_θ
  have hmat := F.matrix _ hg hsub
  have hcomp : components n kin (frMol n kin C.χ C.η c f) = fun i y => C.η y *
      scalarConvolution volume (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => C.χ z * components n kin f i z) y :=
    funext fun i => funext fun y => components_frMol C.χ C.η c f i y
  have hfq : ∀ i, Continuous (fun z => C.χ z * components n kin f i z) := fun i =>
    (contDiff_components_cut C.χ_smooth C.χ_pos hf i).continuous
  have hfc : ∀ i, HasCompactSupport (fun z => C.χ z * components n kin f i z) := fun i =>
    C.χ_compact.mul_right
  have hS : compL2 (fun y => C.χ y • f y) =
      ∑ i, ∫ x, ‖C.χ x * components n kin f i x‖ ^ 2 := by
    unfold compL2
    exact Finset.sum_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun x =>
      congrArg (fun r : ℝ => ‖r‖ ^ 2) (components_smul_fun C.χ f i x))
  have hj : ∀ j, ∫ x, ‖components n kout (F.D (frMol n kin C.χ C.η c f)) j x‖ ^ 2 ≤
      Cj j * compL2 (fun y => C.χ y • f y) := by
    intro j
    have h1 := hbound j (fun i z => C.χ z * components n kin f i z) hfq hfc
    rw [hS]
    have e : components n kout (F.D (frMol n kin C.χ C.η c f)) j = matrixFirstOrder F.v F.A F.B
        (fun i y => C.η y * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * components n kin f i z) y) j :=
      (hmat j).trans (congrArg (fun G => matrixFirstOrder F.v F.A F.B G j) hcomp)
    rw [e]
    exact h1
  calc compL2 (F.D (frMol n kin C.χ C.η c f))
      = ∑ j, ∫ x, ‖components n kout (F.D (frMol n kin C.χ C.η c f)) j x‖ ^ 2 := rfl
    _ ≤ ∑ j, Cj j * compL2 (fun y => C.χ y • f y) := Finset.sum_le_sum fun j _ => hj j
    _ = (∑ j, Cj j) * compL2 (fun y => C.χ y • f y) := (Finset.sum_mul _ _ _).symm


theorem frMol_congr_on {χ η : Coordinates → ℝ} (c : ℝ) {f f' : Coordinates → FormValue n kin}
    (h : ∀ y ∈ tsupport χ, f y = f' y) : frMol n kin χ η c f = frMol n kin χ η c f' := by
  have hcut : (fun y => χ y • f y) = fun y => χ y • f' y := by
    funext y
    by_cases hy : y ∈ tsupport χ
    · exact congrArg (fun z : FormValue n kin => χ y • z) (h y hy)
    · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      exact (congrArg (fun r : ℝ => r • f y) h0).trans
        ((zero_smul_fv (f y)).trans ((zero_smul_fv (f' y)).symm.trans
          (congrArg (fun r : ℝ => r • f' y) h0.symm)))
  funext x
  exact congrArg (fun g : Coordinates → FormValue n kin => η x • frConv n kin c g x) hcut

/-- The scale-uniform Friedrichs bound for the commutator of `D` with the mollifier. -/
theorem exists_compL2_commutator_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c : ℝ}, 0 < c → ∀ {f : Coordinates → FormValue n kin},
      ContDiffOn ℝ ∞ f positiveCoordinates →
      compL2 (fun x => F.D (frMol n kin C.χ C.η c f) x -
        frMol n kout C.χ C.η c (F.D f) x) ≤ A * compL2 (fun y => C.θ y • f y) := by
  have hs := fun j => TernaryPoly.CompactScalarMollifier.matrix_double_cutoff_uniform volume C.χ C.η
    (C.χ_smooth.of_le (by simp)) C.χ_compact (C.η_smooth.of_le (by simp)) C.η_compact F.v F.A F.B
    (fun j i q => (F.A_smooth j i q).of_le (by simp)) (fun j i q => (F.B_smooth j i q).continuous)
    F.A_compact F.B_compact j
  choose Cj hCj hbound using hs
  refine ⟨∑ j, Cj j, Finset.sum_nonneg (fun j _ => hCj j), fun {c} hc {f} hf => ?_⟩
  -- the buffered input
  have hfθ : ContDiff ℝ ∞ (fun y => C.θ y • f y) := contDiff_cut C.θ_smooth C.θ_pos hf
  have hfθc : HasCompactSupport (fun y => C.θ y • f y) := hasCompactSupport_cut C.θ_compact f
  have hfθs : tsupport (fun y => C.θ y • f y) ⊆ tsupport C.θ := tsupport_cut_subset C.θ f
  have hfeq : ∀ y ∈ tsupport C.χ, f y = (fun y => C.θ y • f y) y := fun y hy =>
    ((congrArg (fun r : ℝ => r • f y) (C.θ_eq_one_of_mem (Or.inl hy))).trans
      (one_smul_fv (f y))).symm
  have hk1 : frMol n kin C.χ C.η c f = frMol n kin C.χ C.η c (fun y => C.θ y • f y) :=
    frMol_congr_on c hfeq
  have hDeq : ∀ y ∈ tsupport C.χ, F.D f y = F.D (fun y => C.θ y • f y) y := fun y hy =>
    F.loc _ _ y (by
      filter_upwards [C.θ_one y (Or.inl hy)] with z hz
      have hz' : C.θ z = 1 := hz.trans (Pi.one_apply z)
      exact (one_smul_fv (f z)).symm.trans (congrArg (fun r : ℝ => r • f z) hz'.symm))
  have hk2 : frMol n kout C.χ C.η c (F.D f) =
      frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) := frMol_congr_on c hDeq
  have hfun : (fun x => F.D (frMol n kin C.χ C.η c f) x - frMol n kout C.χ C.η c (F.D f) x) =
      fun x => F.D (frMol n kin C.χ C.η c (fun y => C.θ y • f y)) x -
        frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x :=
    funext fun x => congrArg₂ (fun u v : FormValue n kout => u - v)
      (congrArg (fun G => F.D G x) hk1) (congrFun hk2 x)
  refine (congrArg compL2 hfun).trans_le ?_
  -- componentwise matrix form
  have hg : ContDiff ℝ ∞ (frMol n kin C.χ C.η c (fun y => C.θ y • f y)) :=
    contDiff_frMol C.χ_smooth C.χ_pos C.η_smooth hc.ne' hfθ.contDiffOn
  have hgs : tsupport (frMol n kin C.χ C.η c (fun y => C.θ y • f y)) ⊆ tsupport C.θ :=
    (tsupport_frMol_subset C.χ C.η c _).trans C.tsupport_η_sub_θ
  have hm1 := F.matrix _ hg hgs
  have hm2 := F.matrix _ hfθ hfθs
  have hcomp : components n kin (frMol n kin C.χ C.η c (fun y => C.θ y • f y)) =
      fun i y => C.η y * scalarConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => C.χ z * components n kin (fun y => C.θ y • f y) i z) y :=
    funext fun i => funext fun y => components_frMol C.χ C.η c _ i y
  have hj : ∀ j, ∫ x, ‖components n kout (fun x => F.D (frMol n kin C.χ C.η c
        (fun y => C.θ y • f y)) x - frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x) j x‖ ^ 2 ≤
      Cj j * compL2 (fun y => C.θ y • f y) := by
    intro j
    have h1 := hbound j (components n kin (fun y => C.θ y • f y))
      (fun i => (contDiff_components_of hfθ i).of_le (by simp)) (fun i => hasCompactSupport_components_of hfθc i)
      c hc
    have hA : ∀ x, components n kout (F.D (frMol n kin C.χ C.η c (fun y => C.θ y • f y))) j x =
        matrixFirstOrder F.v F.A F.B (fun i y => C.η y * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * components n kin (fun y => C.θ y • f y) i z) y) j x := fun x =>
      congrFun ((hm1 j).trans (congrArg (fun G => matrixFirstOrder F.v F.A F.B G j) hcomp)) x
    have hB : ∀ x, components n kout (frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y))) j x =
        C.η x * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * matrixFirstOrder F.v F.A F.B
            (components n kin (fun y => C.θ y • f y)) j z) x := fun x =>
      (components_frMol C.χ C.η c _ j x).trans
        (congrArg (fun G : Coordinates → ℝ => C.η x * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * G z) x) (hm2 j))
    have hsubc : ∀ x, components n kout (fun x => F.D (frMol n kin C.χ C.η c
        (fun y => C.θ y • f y)) x - frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x) j x =
        components n kout (F.D (frMol n kin C.χ C.η c (fun y => C.θ y • f y))) j x -
        components n kout (frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y))) j x := fun x =>
      congrArg (fun z : Index n kout → ℝ => z j) (map_sub (coordinates n kout) _ _)
    have e : ∀ x, components n kout (fun x => F.D (frMol n kin C.χ C.η c
        (fun y => C.θ y • f y)) x - frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x) j x =
        matrixFirstOrder F.v F.A F.B (fun i y => C.η y * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * components n kin (fun y => C.θ y • f y) i z) y) j x -
        C.η x * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * matrixFirstOrder F.v F.A F.B
            (components n kin (fun y => C.θ y • f y)) j z) x := fun x =>
      (hsubc x).trans (congrArg₂ (· - ·) (hA x) (hB x))
    exact (integral_congr_ae (Eventually.of_forall fun x =>
      congrArg (fun r : ℝ => ‖r‖ ^ 2) (e x))).trans_le h1
  calc compL2 (fun x => F.D (frMol n kin C.χ C.η c (fun y => C.θ y • f y)) x -
        frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x)
      = ∑ j, ∫ x, ‖components n kout (fun x => F.D (frMol n kin C.χ C.η c
          (fun y => C.θ y • f y)) x - frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) x) j x‖ ^ 2 :=
        rfl
    _ ≤ ∑ j, Cj j * compL2 (fun y => C.θ y • f y) := Finset.sum_le_sum fun j _ => hj j
    _ = (∑ j, Cj j) * compL2 (fun y => C.θ y • f y) := (Finset.sum_mul _ _ _).symm


theorem components_sub_fun {n k : ℕ} (u w : Coordinates → FormValue n k) (j : Index n k)
    (x : Coordinates) :
    components n k (fun x => u x - w x) j x = components n k u j x - components n k w j x :=
  congrArg (fun z : Index n k → ℝ => z j) (map_sub (coordinates n k) (u x) (w x))

theorem cut_congr_on {χ θ : Coordinates → ℝ} (hθ : ∀ y ∈ tsupport χ, θ y = 1)
    (f : Coordinates → FormValue n kin) :
    (fun y => χ y • f y) = fun y => χ y • (θ y • f y) := by
  funext y
  by_cases hy : y ∈ tsupport χ
  · exact congrArg (fun z : FormValue n kin => χ y • z)
      ((one_smul_fv (f y)).symm.trans (congrArg (fun r : ℝ => r • f y) (hθ y hy).symm))
  · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    exact (congrArg (fun r : ℝ => r • f y) h0).trans
      ((zero_smul_fv (f y)).trans ((zero_smul_fv (θ y • f y)).symm.trans
        (congrArg (fun r : ℝ => r • (θ y • f y)) h0.symm)))

/-- The defect of the commutator of `D` with the mollifier from its symbol along the cutoffs. -/
def commFun (c : ℝ) (f : Coordinates → FormValue n kin) : Coordinates → FormValue n kout :=
  fun x => (F.D (frMol n kin C.χ C.η c f) x - frMol n kout C.χ C.η c (F.D f) x) -
    (F.D (fun y => C.η y • (C.χ y • f y)) x - C.η x • (C.χ x • F.D f x))

theorem commFun_buffer (c : ℝ) {f : Coordinates → FormValue n kin} :
    commFun C F c f = commFun C F c (fun y => C.θ y • f y) := by
  have hθ1 : ∀ y ∈ tsupport C.χ, C.θ y = 1 := fun y hy => C.θ_eq_one_of_mem (Or.inl hy)
  have hfeq : ∀ y ∈ tsupport C.χ, f y = (fun y => C.θ y • f y) y := fun y hy =>
    ((congrArg (fun r : ℝ => r • f y) (hθ1 y hy)).trans (one_smul_fv (f y))).symm
  have hDeq : ∀ y ∈ tsupport C.χ, F.D f y = F.D (fun y => C.θ y • f y) y := fun y hy =>
    F.loc _ _ y (by
      filter_upwards [C.θ_one y (Or.inl hy)] with z hz
      have hz' : C.θ z = 1 := hz.trans (Pi.one_apply z)
      exact (one_smul_fv (f z)).symm.trans (congrArg (fun r : ℝ => r • f z) hz'.symm))
  have hk1 : frMol n kin C.χ C.η c f = frMol n kin C.χ C.η c (fun y => C.θ y • f y) :=
    frMol_congr_on c hfeq
  have hk2 : frMol n kout C.χ C.η c (F.D f) =
      frMol n kout C.χ C.η c (F.D (fun y => C.θ y • f y)) := frMol_congr_on c hDeq
  have hk3 : (fun y => C.η y • (C.χ y • f y)) =
      fun y => C.η y • (C.χ y • (C.θ y • f y)) :=
    funext fun y => congrArg (fun z : FormValue n kin => C.η y • z)
      (congrFun (cut_congr_on hθ1 f) y)
  have hk4 : ∀ x, C.η x • (C.χ x • F.D f x) =
      C.η x • (C.χ x • F.D (fun y => C.θ y • f y) x) := by
    intro x
    by_cases hx : x ∈ tsupport C.χ
    · exact congrArg (fun z : FormValue n kout => C.η x • (C.χ x • z)) (hDeq x hx)
    · have h0 : C.χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have e1 : C.χ x • F.D f x = 0 :=
        (congrArg (fun r : ℝ => r • F.D f x) h0).trans (zero_smul_fv _)
      have e2 : C.χ x • F.D (fun y => C.θ y • f y) x = 0 :=
        (congrArg (fun r : ℝ => r • F.D (fun y => C.θ y • f y) x) h0).trans (zero_smul_fv _)
      exact (congrArg (fun z : FormValue n kout => C.η x • z) (e1.trans e2.symm))
  funext x
  unfold commFun
  exact congrArg₂ (fun u v : FormValue n kout => u - v)
    (congrArg₂ (fun u v : FormValue n kout => u - v)
      (congrArg (fun G => F.D G x) hk1) (congrFun (congrArg (fun G => frMol n kout C.χ C.η c G) rfl) x |>.trans (congrFun hk2 x)))
    (congrArg₂ (fun u v : FormValue n kout => u - v)
      (congrArg (fun G => F.D G x) hk3) (hk4 x))

theorem components_commFun (c : ℝ) (hc : 0 < c) {g : Coordinates → FormValue n kin}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ tsupport C.θ) (j : Index n kout) (x : Coordinates) :
    components n kout (commFun C F c g) j x =
      (matrixFirstOrder F.v F.A F.B (fun i y => C.η y * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * components n kin g i z) y) j x -
        C.η x * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * matrixFirstOrder F.v F.A F.B (components n kin g) j z) x) -
      (matrixFirstOrder F.v F.A F.B (fun i y => C.η y * (C.χ y * components n kin g i y)) j x -
        C.η x * (C.χ x * matrixFirstOrder F.v F.A F.B (components n kin g) j x)) := by
  have hmol : ContDiff ℝ ∞ (frMol n kin C.χ C.η c g) :=
    contDiff_frMol C.χ_smooth C.χ_pos C.η_smooth hc.ne' hg.contDiffOn
  have hmols : tsupport (frMol n kin C.χ C.η c g) ⊆ tsupport C.θ :=
    (tsupport_frMol_subset C.χ C.η c g).trans C.tsupport_η_sub_θ
  have hm1 := F.matrix _ hmol hmols
  have hm2 := F.matrix g hg hgs
  have hcomp : components n kin (frMol n kin C.χ C.η c g) = fun i y => C.η y *
      scalarConvolution volume (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => C.χ z * components n kin g i z) y :=
    funext fun i => funext fun y => components_frMol C.χ C.η c g i y
  have hcut : ContDiff ℝ ∞ (fun y => C.η y • (C.χ y • g y)) :=
    contDiff_cut C.η_smooth C.η_pos (contDiff_cut C.χ_smooth C.χ_pos hg.contDiffOn).contDiffOn
  have hcuts : tsupport (fun y => C.η y • (C.χ y • g y)) ⊆ tsupport C.θ :=
    (tsupport_cut_subset C.η _).trans C.tsupport_η_sub_θ
  have hm3 := F.matrix _ hcut hcuts
  have hcc : components n kin (fun y => C.η y • (C.χ y • g y)) =
      fun i y => C.η y * (C.χ y * components n kin g i y) :=
    funext fun i => funext fun y =>
      (components_smul_fun C.η (fun y => C.χ y • g y) i y).trans
        (congrArg (fun r : ℝ => C.η y * r) (components_smul_fun C.χ g i y))
  have hA : components n kout (F.D (frMol n kin C.χ C.η c g)) j x =
      matrixFirstOrder F.v F.A F.B (fun i y => C.η y * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * components n kin g i z) y) j x :=
    congrFun ((hm1 j).trans (congrArg (fun G => matrixFirstOrder F.v F.A F.B G j) hcomp)) x
  have hB : components n kout (frMol n kout C.χ C.η c (F.D g)) j x =
      C.η x * scalarConvolution volume
          (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
          (fun z => C.χ z * matrixFirstOrder F.v F.A F.B (components n kin g) j z) x :=
    (components_frMol C.χ C.η c _ j x).trans
      (congrArg (fun G : Coordinates → ℝ => C.η x * scalarConvolution volume
        (TernaryPoly.CompactScalarMollifier.kernel Coordinates volume c)
        (fun z => C.χ z * G z) x) (hm2 j))
  have hC : components n kout (F.D (fun y => C.η y • (C.χ y • g y))) j x =
      matrixFirstOrder F.v F.A F.B (fun i y => C.η y * (C.χ y * components n kin g i y)) j x :=
    congrFun ((hm3 j).trans (congrArg (fun G => matrixFirstOrder F.v F.A F.B G j) hcc)) x
  have hE : components n kout (fun x => C.η x • (C.χ x • F.D g x)) j x =
      C.η x * (C.χ x * matrixFirstOrder F.v F.A F.B (components n kin g) j x) :=
    (components_smul_fun C.η (fun y => C.χ y • F.D g y) j x).trans
      (congrArg (fun r : ℝ => C.η x * r)
        ((components_smul_fun C.χ (F.D g) j x).trans
          (congrArg (fun r : ℝ => C.χ x * r) (congrFun (hm2 j) x))))
  have hsub : ∀ (u w : Coordinates → FormValue n kout),
      components n kout (fun x => u x - w x) j x =
        components n kout u j x - components n kout w j x := fun u w =>
    components_sub_fun u w j x
  change components n kout (fun x => (F.D (frMol n kin C.χ C.η c g) x -
        frMol n kout C.χ C.η c (F.D g) x) -
      (F.D (fun y => C.η y • (C.χ y • g y)) x - C.η x • (C.χ x • F.D g x))) j x = _
  rw [hsub, hsub, hsub, hA, hB, hC]
  rw [show components n kout (fun x => C.η x • (C.χ x • F.D g x)) j x =
    components n kout (fun x => C.η x • (C.χ x • F.D g x)) j x from rfl, hE]

theorem commFun_component_tendsto {g : Coordinates → FormValue n kin} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ tsupport C.θ) (j : Index n kout) :
    Tendsto (fun c : ℝ => ∫ x, ‖components n kout (commFun C F c g) j x‖ ^ 2) atTop (𝓝 0) := by
  have h := TernaryPoly.CompactScalarMollifier.matrix_double_cutoff_tendsto volume C.χ C.η
    (C.χ_smooth.of_le (by simp)) C.χ_compact (C.η_smooth.of_le (by simp)) C.η_compact F.v F.A F.B
    (fun j i q => (F.A_smooth j i q).of_le (by simp)) (fun j i q => (F.B_smooth j i q).continuous)
    F.A_compact F.B_compact (components n kin g)
    (fun i => (contDiff_components_of hg i).of_le (by simp)) j
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hid := matrixFirstOrder_two_cutoffs F.v F.A F.B C.χ C.η (components n kin g) j x
    ((C.χ_smooth.differentiable (by simp)) x) ((C.η_smooth.differentiable (by simp)) x)
    (fun i => ((contDiff_components_of hg i).differentiable (by simp)) x)
  have e := components_commFun C F c hc hg hgs j x
  dsimp only
  rw [e, hid]

theorem commFun_tendsto_buffered {g : Coordinates → FormValue n kin} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ tsupport C.θ) :
    Tendsto (fun c : ℝ => wL2 (commFun C F c g)) atTop (𝓝 0) := by
  have hηs : tsupport C.η ⊆ tsupport C.θ := C.tsupport_η_sub_θ
  have hθK : tsupport C.θ ⊆ positiveCoordinates := C.θ_pos
  have hDg : ContDiff ℝ ∞ (F.D g) := F.smooth g hg (hgs.trans hθK)
  have hcut : ContDiff ℝ ∞ (fun y => C.η y • (C.χ y • g y)) :=
    contDiff_cut C.η_smooth C.η_pos (contDiff_cut C.χ_smooth C.χ_pos hg.contDiffOn).contDiffOn
  have hcuts : tsupport (fun y => C.η y • (C.χ y • g y)) ⊆ tsupport C.θ :=
    (tsupport_cut_subset C.η _).trans hηs
  have hDcut : ContDiff ℝ ∞ (F.D (fun y => C.η y • (C.χ y • g y))) :=
    F.smooth _ hcut (hcuts.trans hθK)
  have hEs : ContDiff ℝ ∞ (fun x => C.η x • (C.χ x • F.D g x)) :=
    contDiff_cut C.η_smooth C.η_pos (contDiff_cut C.χ_smooth C.χ_pos hDg.contDiffOn).contDiffOn
  have hw : ∀ᶠ c : ℝ in atTop, ContDiff ℝ ∞ (commFun C F c g) ∧
      HasCompactSupport (commFun C F c g) ∧ tsupport (commFun C F c g) ⊆ tsupport C.θ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have hmol : ContDiff ℝ ∞ (frMol n kin C.χ C.η c g) :=
      contDiff_frMol C.χ_smooth C.χ_pos C.η_smooth hc.ne' hg.contDiffOn
    have hmols : tsupport (frMol n kin C.χ C.η c g) ⊆ tsupport C.θ :=
      (tsupport_frMol_subset C.χ C.η c g).trans hηs
    have hDmol : ContDiff ℝ ∞ (F.D (frMol n kin C.χ C.η c g)) := F.smooth _ hmol (hmols.trans hθK)
    have hMD : ContDiff ℝ ∞ (frMol n kout C.χ C.η c (F.D g)) :=
      contDiff_frMol C.χ_smooth C.χ_pos C.η_smooth hc.ne' hDg.contDiffOn
    have hsub : tsupport (commFun C F c g) ⊆ tsupport C.θ := by
      refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
      · refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
        · exact (F.tsupport_sub _).trans hmols
        · exact (tsupport_frMol_subset C.χ C.η c (F.D g)).trans hηs
      · refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
        · exact (F.tsupport_sub _).trans hcuts
        · exact (tsupport_cut_subset C.η _).trans hηs
    refine ⟨((hDmol.sub hMD).sub (hDcut.sub hEs)), ?_, hsub⟩
    exact C.θ_compact.of_isClosed_subset (isClosed_tsupport _) hsub
  have hcomp : Tendsto (fun c : ℝ => compL2 (commFun C F c g)) atTop (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun j _ => commFun_component_tendsto C F hg hgs j)
    rw [Finset.sum_const_zero] at this
    exact this
  have ht : Tendsto (fun c : ℝ => ∫ x, ‖commFun C F c g x‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun c => integral_nonneg fun x => sq_nonneg _) ?_
      (by
        have := hcomp.const_mul (‖(coordinates n kout).symm.toContinuousLinearMap‖ ^ 2)
        rw [mul_zero] at this
        exact this)
    filter_upwards [hw] with c hc
    exact integral_le_compL2 hc.1.continuous hc.2.1
  exact compact_weighted_square_tendsto n kout (tsupport C.θ) C.θ_compact.isCompact C.θ_pos
    (fun c => commFun C F c g) hw ht

/-- The commutator of `D` with the mollifier converges, in the metric-density norm, to the symbol
`D (η χ f) - η χ D f` of `D` along the cutoffs. -/
theorem commutator_tendsto {f : Coordinates → FormValue n kin}
    (hf : ContDiffOn ℝ ∞ f positiveCoordinates) :
    Tendsto (fun c : ℝ => wL2 (commFun C F c f)) atTop (𝓝 0) := by
  have hg : ContDiff ℝ ∞ (fun y => C.θ y • f y) := contDiff_cut C.θ_smooth C.θ_pos hf
  have hgs : tsupport (fun y => C.θ y • f y) ⊆ tsupport C.θ := tsupport_cut_subset C.θ f
  have := commFun_tendsto_buffered C F hg hgs
  exact Tendsto.congr (fun c => congrArg wL2 (commFun_buffer C F c).symm) this

end FirstOrder

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
