module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Datum
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HeightCutoff

@[expose] public section


/-!
# Real-linear `1`-forms, the slash action and the invariant pairing

A `1`-form with values in `ℂ^d` is a field of real-linear maps `ℂ → ℂ^d`.  Pull-back by an element
`γ` of `Γ` followed by `ρ(γ)⁻¹` is the slash action `slash`; equivariant forms are the fixed points.
The hyperbolic pairing `Im² (⟪S a₁, S a₂⟫ + ⟪S b₁, S b₂⟫)` of two forms (`Pinv`, with `a = L 1`,
`b = L i`) is invariant under the slash action, and the exterior derivative commutes with it.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff InnerProductSpace MatrixGroups

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one)
open TernaryPeriodPolynomials.Argument.ESFoundations.Height (hasDerivAt_mob norm_denom_sq)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

/-- The automorphy factor `c z + d` of a matrix. -/
def jfun (γ : SL(2, ℤ)) (z : ℂ) : ℂ := ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)

/-- The derivative of the Möbius map, as a complex number. -/
def mobDeriv (γ : SL(2, ℤ)) (z : ℂ) : ℂ := 1 / jfun γ z ^ 2

theorem fderiv_mob_apply (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ (mob γ) z v = mobDeriv γ z * v := by
  have h := ((hasDerivAt_mob γ hz).hasFDerivAt.restrictScalars ℝ).fderiv
  rw [h]
  simp [mobDeriv, jfun, mul_comm]

theorem im_mob_eq (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    (mob γ z).im = z.im * ‖mobDeriv γ z‖ := by
  rw [norm_denom_sq γ hz]
  simp only [mobDeriv, jfun, norm_div, norm_one, norm_pow]
  have : 0 < ‖((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)‖ := by
    rw [norm_pos_iff]
    exact Partition.denom_ne_zero' γ hz
  field_simp

/-- A real-linear `1`-form with values in `ℂ^d`: at every point a real-linear map `ℂ → ℂ^d`. -/
abbrev Form (d : ℕ) := ℂ → (ℂ →L[ℝ] Wd d)

/-- The conformal invariance of the pointwise norm of a `1`-form on a surface: the sum of the
pairings on the two images of the orthonormal basis `1, i` under multiplication by `c` is `|c|²`
times the original one. -/
theorem conf_pair (S : Wd d →L[ℂ] Wd d) (c : ℂ) (L₁ L₂ : ℂ →L[ℝ] Wd d) :
    ⟪S (L₁ (c * 1)), S (L₂ (c * 1))⟫_ℝ + ⟪S (L₁ (c * Complex.I)), S (L₂ (c * Complex.I))⟫_ℝ =
      ‖c‖ ^ 2 * (⟪S (L₁ 1), S (L₂ 1)⟫_ℝ + ⟪S (L₁ Complex.I), S (L₂ Complex.I)⟫_ℝ) := by
  have e1 : c * 1 = c.re • (1 : ℂ) + c.im • Complex.I := by
    apply Complex.ext <;> simp
  have e2 : c * Complex.I = c.re • Complex.I + (-c.im) • (1 : ℂ) := by
    apply Complex.ext <;> simp
  have hS : ∀ (r : ℝ) (x : Wd d), S (r • x) = r • S x := fun r x => by
    simp
  rw [e1, e2]
  simp only [map_add, map_smul, hS, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have hn : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn]
  ring

namespace HodgeDatum

variable (D : HodgeDatum Γ d)

/-- The (flat) squared pointwise norm of a form. -/
def edens (L : Form d) (z : ℂ) : ℝ := ‖D.S z (L z 1)‖ ^ 2 + ‖D.S z (L z Complex.I)‖ ^ 2

/-- The (flat) pairing of two forms. -/
def pairE (L₁ L₂ : Form d) (z : ℂ) : ℝ :=
  ⟪D.S z (L₁ z 1), D.S z (L₂ z 1)⟫_ℝ + ⟪D.S z (L₁ z Complex.I), D.S z (L₂ z Complex.I)⟫_ℝ

theorem pairE_self (L : Form d) (z : ℂ) : D.pairE L L z = D.edens L z := by
  simp [pairE, edens]

theorem edens_nonneg (L : Form d) (z : ℂ) : 0 ≤ D.edens L z := by
  unfold edens; positivity

/-- Pullback by `γ` followed by `ρ(γ)⁻¹`. -/
def slash (γ : Γ) (L : Form d) : Form d := fun w =>
  (D.ρR γ⁻¹).comp ((L (mob (γ : SL(2, ℤ)) w)).comp (fderiv ℝ (mob (γ : SL(2, ℤ))) w))

/-- Equivariance of a form: invariance under the slash action. -/
def Eqv (L : Form d) : Prop := ∀ γ : Γ, ∀ w ∈ U, D.slash γ L w = L w

theorem inner_rho_inv (γ : Γ) {w : ℂ} (hw : w ∈ U) (u v : Wd d) :
    ⟪D.S w (D.ρR γ⁻¹ u), D.S w (D.ρR γ⁻¹ v)⟫_ℝ =
      ⟪D.S (mob (γ : SL(2, ℤ)) w) u, D.S (mob (γ : SL(2, ℤ)) w) v⟫_ℝ := by
  have hg : mob (γ : SL(2, ℤ)) w ∈ U := Partition.mob_mem _ _
  have h := D.S_equiv γ⁻¹ (mob (γ : SL(2, ℤ)) w) hg u v
  have e : mob ((γ⁻¹ : Γ) : SL(2, ℤ)) (mob (γ : SL(2, ℤ)) w) = w := by
    rw [← mob_mul, Subgroup.coe_inv, inv_mul_cancel, mob_one hw]
  rw [e] at h
  rw [real_inner_wd, real_inner_wd]
  exact congrArg Complex.re h

theorem pairE_slash (γ : Γ) (L₁ L₂ : Form d) {w : ℂ} (hw : w ∈ U) :
    D.pairE (D.slash γ L₁) (D.slash γ L₂) w =
      ‖mobDeriv (γ : SL(2, ℤ)) w‖ ^ 2 * D.pairE L₁ L₂ (mob (γ : SL(2, ℤ)) w) := by
  have h1 : ∀ (L : Form d) (v : ℂ), D.slash γ L w v =
      D.ρR γ⁻¹ (L (mob (γ : SL(2, ℤ)) w) (mobDeriv (γ : SL(2, ℤ)) w * v)) := fun L v => by
    simp [slash, fderiv_mob_apply _ hw]
  simp only [pairE, h1, inner_rho_inv D γ hw]
  exact conf_pair (D.S (mob (γ : SL(2, ℤ)) w)) (mobDeriv (γ : SL(2, ℤ)) w)
    (L₁ (mob (γ : SL(2, ℤ)) w)) (L₂ (mob (γ : SL(2, ℤ)) w))

/-- The `Γ`-invariant pointwise pairing of two forms: `Im²` times the flat pairing `pairE`. -/
def Pinv (L₁ L₂ : Form d) (z : ℂ) : ℝ := z.im ^ 2 * D.pairE L₁ L₂ z

theorem Pinv_slash (γ : Γ) (L₁ L₂ : Form d) {w : ℂ} (hw : w ∈ U) :
    D.Pinv (D.slash γ L₁) (D.slash γ L₂) w = D.Pinv L₁ L₂ (mob (γ : SL(2, ℤ)) w) := by
  unfold Pinv
  rw [D.pairE_slash γ L₁ L₂ hw, im_mob_eq _ hw]
  ring

theorem Pinv_mob_of_eqv {L₁ L₂ : Form d} (h₁ : D.Eqv L₁) (h₂ : D.Eqv L₂) (γ : Γ) {w : ℂ}
    (hw : w ∈ U) : D.Pinv L₁ L₂ (mob (γ : SL(2, ℤ)) w) = D.Pinv L₁ L₂ w := by
  rw [← D.Pinv_slash γ L₁ L₂ hw]
  unfold Pinv pairE
  rw [h₁ γ w hw, h₂ γ w hw]

/-- An equivariant function: `φ (γ z) = ρ γ (φ z)`. -/
def EqvFun (φ : ℂ → Wd d) : Prop := ∀ γ : Γ, ∀ z ∈ U, φ (mob (γ : SL(2, ℤ)) z) = D.ρ γ (φ z)

/-- Naturality of the exterior derivative under the slash action. -/
theorem slash_fderiv (γ : Γ) {φ : ℂ → Wd d} (hφ : DifferentiableOn ℝ φ U) {w : ℂ} (hw : w ∈ U) :
    D.slash γ (fun z => fderiv ℝ φ z) w =
      fderiv ℝ (fun z => D.ρR γ⁻¹ (φ (mob (γ : SL(2, ℤ)) z))) w := by
  have hm : DifferentiableAt ℝ (mob (γ : SL(2, ℤ))) w :=
    ((hasDerivAt_mob _ hw).differentiableAt).restrictScalars ℝ
  have hφ' : DifferentiableAt ℝ φ (mob (γ : SL(2, ℤ)) w) :=
    (hφ _ (Partition.mob_mem _ _)).differentiableAt (isOpen_U.mem_nhds (Partition.mob_mem _ _))
  have := (D.ρR γ⁻¹).hasFDerivAt.comp w (hφ'.hasFDerivAt.comp w hm.hasFDerivAt)
  rw [show (fun z => D.ρR γ⁻¹ (φ (mob (γ : SL(2, ℤ)) z))) =
    ⇑(D.ρR γ⁻¹) ∘ φ ∘ mob (γ : SL(2, ℤ)) from rfl, this.fderiv]
  rfl

theorem eqv_fderiv {φ : ℂ → Wd d} (hφ : DifferentiableOn ℝ φ U) (h : D.EqvFun φ) :
    D.Eqv (fun z => fderiv ℝ φ z) := by
  intro γ w hw
  rw [D.slash_fderiv γ hφ hw]
  have hev : (fun z => D.ρR γ⁻¹ (φ (mob (γ : SL(2, ℤ)) z))) =ᶠ[𝓝 w] φ := by
    filter_upwards [isOpen_U.mem_nhds hw] with z hz
    rw [h γ z hz]
    have h2 := congrArg (fun T : Wd d →L[ℂ] Wd d => T (φ z)) (D.ρ.map_mul γ⁻¹ γ)
    simp only [inv_mul_cancel, map_one] at h2
    exact h2.symm
  exact hev.fderiv_eq

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
