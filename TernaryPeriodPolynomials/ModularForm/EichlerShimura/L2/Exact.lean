module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Space

@[expose] public section


/-!
# The subspace of exact forms and the orthogonal projection

`Approx φ` says that `φ` is smooth, equivariant and has differential supported compactly modulo `Γ`.
The closure `bSub` of the span of the weighted coordinates of the differentials `dφ` is a closed
subspace of the equivariant vectors (`bSub_le_eqvSub`); `projB` is the orthogonal projection on it.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d)

/-- Smooth equivariant `ℂ^d`-valued functions with differential supported compactly modulo `Γ`. -/
def Approx (φ : ℂ → Wd d) : Prop :=
  ContDiffOn ℝ ∞ φ U ∧ D.EqvFun φ ∧ ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧
    ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ φ z = 0

theorem continuousOn_fderiv {φ : ℂ → Wd d} (hφ : ContDiffOn ℝ ∞ φ U) :
    ContinuousOn (fun z => fderiv ℝ φ z) U :=
  hφ.continuousOn_fderiv_of_isOpen isOpen_U (by simp)

theorem Approx.eqv {φ : ℂ → Wd d} (h : D.Approx φ) : D.Eqv (fun z => fderiv ℝ φ z) :=
  D.eqv_fderiv (h.1.differentiableOn (by simp)) h.2.1

theorem Approx.good (W : Weights Γ) {φ : ℂ → Wd d} (h : D.Approx φ) :
    Good D W (fun z => fderiv ℝ φ z) := by
  obtain ⟨h1, h2, K, hK, hKU, h0⟩ := h
  refine ⟨continuousOn_fderiv h1, ?_⟩
  exact W.lintegral_θ_edens_lt_top D (continuousOn_fderiv h1)
    (D.eqv_fderiv (h1.differentiableOn (by simp)) h2) hK hKU h0

variable (W : Weights Γ)

/-- The generators of the subspace of exact forms. -/
def genSet : Set (Hs d) :=
  {x | ∃ φ : ℂ → Wd d, ∃ h : D.Approx φ, x = D.xvec W (Approx.good D W h)}

/-- The closed subspace spanned by the differentials of equivariant functions with support compact
modulo `Γ`. -/
def bSub : Submodule ℝ (Hs d) := (Submodule.span ℝ (D.genSet W)).topologicalClosure

theorem bSub_le_eqvSub : D.bSub W ≤ D.eqvSub W := by
  unfold bSub
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [Submodule.span_le]
  rintro x ⟨φ, h, rfl⟩
  exact D.xvec_mem_eqvSub W (Approx.good D W h) (Approx.eqv D h)

instance : (D.bSub W).HasOrthogonalProjection := by
  have : CompleteSpace (D.bSub W) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- The orthogonal projection on the closed subspace of exact forms. -/
def projB (x : Hs d) : Hs d := (D.bSub W).starProjection x

theorem projB_mem (x : Hs d) : D.projB W x ∈ D.bSub W := Submodule.starProjection_apply_mem _ x

theorem sub_projB_mem_orthogonal (x : Hs d) : x - D.projB W x ∈ (D.bSub W)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal x

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
