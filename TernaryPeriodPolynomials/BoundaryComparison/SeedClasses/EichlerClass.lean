module

public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open Complex UpperHalfPlane
open scoped UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The Möbius action `z ↦ (az + b)/(cz + d)` of a real `2 × 2` matrix on `ℂ`. -/
def mob (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℝ) * z + (γ 0 1 : ℝ)) / ((γ 1 0 : ℝ) * z + (γ 1 1 : ℝ))

/-- The automorphy denominator `cz + d`. -/
def dnm (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ := (γ 1 0 : ℝ) * z + (γ 1 1 : ℝ)

/-- The coordinate action `v ↦ γ⁻¹ v = (d x - b y, -c x + a y)` (the adjugate) on the variables
`(X, Y)` of the binary forms. -/
def invCoord (γ : GL (Fin 2) ℝ) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(γ 1 1 : ℝ) * v 0 - (γ 0 1 : ℝ) * v 1, -(γ 1 0 : ℝ) * v 0 + (γ 0 0 : ℝ) * v 1]

/-- The Eichler--Shimura integrand `h(z)(zy - x)^{n+1}` of the binary class of weight `n + 3`. -/
def binaryIntegrand (n : ℕ) (h : ℂ → ℂ) (v : Fin 2 → ℂ) (z : ℂ) : ℂ :=
  h z * (z * v 1 - v 0) ^ (n + 1)

theorem mob_eq_smul (γ : GL (Fin 2) ℝ) (hpos : 0 < γ.det.val) (z : ℍ) :
    mob γ z = ((γ • z : ℍ) : ℂ) := (coe_smul_of_det_pos hpos z).symm

theorem mob_im_pos (γ : GL (Fin 2) ℝ) (hpos : 0 < γ.det.val) {z : ℂ} (hz : 0 < z.im) :
    0 < (mob γ z).im := by
  have := mob_eq_smul γ hpos ⟨z, hz⟩
  rw [show z = ((⟨z, hz⟩ : ℍ) : ℂ) from rfl, this]
  exact (γ • (⟨z, hz⟩ : ℍ)).im_pos

theorem dnm_ne_zero (γ : GL (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) : dnm γ z ≠ 0 :=
  denom_ne_zero_of_im γ hz.ne'

theorem det_eq_one (γ : GL (Fin 2) ℝ) (h : γ.det = 1) :
    (γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := congrArg Units.val h
  simpa [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two] using this

theorem mob_hasDerivAt (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / dnm γ z ^ 2) z := by
  have h := HasDerivAt.div
    (((hasDerivAt_id z).const_mul ((γ 0 0 : ℝ) : ℂ)).add_const ((γ 0 1 : ℝ) : ℂ))
    (((hasDerivAt_id z).const_mul ((γ 1 0 : ℝ) : ℂ)).add_const ((γ 1 1 : ℝ) : ℂ))
    (dnm_ne_zero γ hz)
  have he : ((γ 0 0 : ℝ) : ℂ) * ((γ 1 0 : ℝ) * z + (γ 1 1 : ℝ)) -
      ((γ 0 0 : ℝ) * z + (γ 0 1 : ℝ)) * (γ 1 0 : ℝ) = 1 := by
    have := det_eq_one γ hdet
    have h2 : (((γ 0 0 : ℝ) * γ 1 1 - γ 0 1 * γ 1 0 : ℝ) : ℂ) = 1 := by exact_mod_cast this
    push_cast at h2
    linear_combination h2
  simpa only [mul_one, id_eq, he, mob, dnm, Pi.div_apply] using! h

/-- The binary period integrand is pulled back by `γ` to the integrand at the inverse-transformed
coordinates, when `h` has weight `n + 3` for `γ`. -/
theorem binaryIntegrand_transform (n : ℕ) (h : ℂ → ℂ) (γ : GL (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hmod : h (mob γ z) = dnm γ z ^ (n + 3) * h z) (v : Fin 2 → ℂ) :
    binaryIntegrand n h v (mob γ z) * (1 / dnm γ z ^ 2) =
      binaryIntegrand n h (invCoord γ v) z := by
  have hden := dnm_ne_zero γ hz
  have he : mob γ z * v 1 - v 0 =
      (z * (invCoord γ v 1) - invCoord γ v 0) / dnm γ z := by
    apply (eq_div_iff hden).2
    unfold mob dnm invCoord
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [sub_mul, mul_right_comm (_ / _) (v 1) _, div_mul_cancel₀ _ (by simpa [dnm] using hden)]
    ring
  unfold binaryIntegrand
  rw [hmod, he, div_pow, pow_add]
  field_simp
  ring

/-- **Constancy of the transformation defect.** For any family of primitives `F v` of the binary
integrand on the upper half-plane, `F v (γ z) - F (γ⁻¹ v) z` does not depend on `z`. -/
theorem primitive_defect_const (n : ℕ) (h : ℂ → ℂ) (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1)
    (hmod : ∀ z : ℂ, 0 < z.im → h (mob γ z) = dnm γ z ^ (n + 3) * h z)
    (F : (Fin 2 → ℂ) → ℂ → ℂ)
    (hF : ∀ v z, 0 < z.im → HasDerivAt (F v) (binaryIntegrand n h v z) z)
    (v : Fin 2 → ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    F v (mob γ z) - F (invCoord γ v) z = F v (mob γ w) - F (invCoord γ v) w := by
  have hpos : 0 < γ.det.val := by simp [hdet]
  have hder : ∀ u : ℂ, 0 < u.im →
      HasDerivAt (fun u => F v (mob γ u) - F (invCoord γ v) u) 0 u := by
    intro u hu
    have h1 := (hF v (mob γ u) (mob_im_pos γ hpos hu)).comp u (mob_hasDerivAt γ hdet hu)
    have h2 := hF (invCoord γ v) u hu
    have h3 := h1.sub h2
    have h4 := binaryIntegrand_transform n h γ hu (hmod u hu) v
    have h5 : binaryIntegrand n h v (mob γ u) * (1 / dnm γ u ^ 2) -
        binaryIntegrand n h (invCoord γ v) u = 0 := by rw [h4, sub_self]
    exact h3.congr_deriv h5
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconv : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  exact IsOpen.is_const_of_deriv_eq_zero hopen hconv
    (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hder u hu).deriv) hz hw

/-- The period cocycle of a family of primitives: the transformation defect, computed at the base
point `i`. -/
def periodConst (F : (Fin 2 → ℂ) → ℂ → ℂ) (γ : GL (Fin 2) ℝ) (v : Fin 2 → ℂ) : ℂ :=
  F v (mob γ Complex.I) - F (invCoord γ v) Complex.I

theorem mob_mul (γ δ : GL (Fin 2) ℝ) (hγ : γ.det = 1) (hδ : δ.det = 1) {z : ℂ}
    (hz : 0 < z.im) : mob (γ * δ) z = mob γ (mob δ z) := by
  have hγp : 0 < γ.det.val := by simp [hγ]
  have hδp : 0 < δ.det.val := by simp [hδ]
  have hp : 0 < (γ * δ).det.val := by simp [hγ, hδ]
  have e1 := mob_eq_smul (γ * δ) hp ⟨z, hz⟩
  have e2 := mob_eq_smul δ hδp ⟨z, hz⟩
  have e3 := mob_eq_smul γ hγp (δ • (⟨z, hz⟩ : ℍ))
  change mob (γ * δ) z = _ at e1
  change mob δ z = _ at e2
  rw [e1, mul_smul, e2]
  exact e3.symm

theorem invCoord_mul (γ δ : GL (Fin 2) ℝ) (v : Fin 2 → ℂ) :
    invCoord (γ * δ) v = invCoord δ (invCoord γ v) := by
  ext i
  fin_cases i <;>
    simp [invCoord, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The period cocycle relation** `c(γδ) = c(γ) + c(δ)∘γ⁻¹`, for primitives of the binary
integrand of a weight-`n+3` function modular for `γ` and `δ`. -/
theorem periodConst_mul (n : ℕ) (h : ℂ → ℂ) (γ δ : GL (Fin 2) ℝ) (hγ : γ.det = 1)
    (hδ : δ.det = 1)
    (hmodγ : ∀ z : ℂ, 0 < z.im → h (mob γ z) = dnm γ z ^ (n + 3) * h z)
    (F : (Fin 2 → ℂ) → ℂ → ℂ)
    (hF : ∀ v z, 0 < z.im → HasDerivAt (F v) (binaryIntegrand n h v z) z)
    (v : Fin 2 → ℂ) :
    periodConst F (γ * δ) v = periodConst F γ v + periodConst F δ (invCoord γ v) := by
  have hI : 0 < (Complex.I : ℂ).im := by simp
  have hpos : 0 < δ.det.val := by simp [hδ]
  have hz : 0 < (mob δ Complex.I).im := mob_im_pos δ hpos hI
  have hc := primitive_defect_const n h γ hγ hmodγ F hF v hz hI
  unfold periodConst at *
  rw [mob_mul γ δ hγ hδ hI, invCoord_mul]
  linear_combination hc

/-- The modularity of the extension `h = f ∘ ofComplex` of a slash-invariant form of weight `k`:
`h(γz) = (cz + d)^k h(z)` for `γ` in the determinant-one group. -/
theorem modular_of_slashInvariant {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ))
    [Λ.HasDetOne] (k : ℕ) [SlashInvariantFormClass F Λ (k : ℤ)] (f : F)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Λ) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (mob γ z)) = dnm γ z ^ k * f (ofComplex z) := by
  have hdet : γ.det = 1 := Subgroup.HasDetOne.det_eq hγ
  have hpos : 0 < γ.det.val := by simp [hdet]
  have hmod := SlashInvariantForm.slash_action_eqn'' (F := F) (k := (k : ℤ)) f hγ ⟨z, hz⟩
  have e1 := mob_eq_smul γ hpos ⟨z, hz⟩
  change mob γ z = _ at e1
  rw [e1, ofComplex_apply, hmod, ofComplex_apply_of_im_pos hz]
  simp only [zpow_natCast]
  rfl

/-- Moment primitives: holomorphic primitives of `h(z) z^j`, normalized at the base point `i`. -/
theorem exists_moment_primitives (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) :
    ∃ G : ℕ → ℂ → ℂ, (∀ j, G j Complex.I = 0) ∧
      ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z := by
  have hd : ∀ j : ℕ, DifferentiableOn ℂ (fun z => h z * z ^ j) {z : ℂ | 0 < z.im} :=
    fun j => hh.mul ((differentiable_id.pow j).differentiableOn)
  choose G hG using fun j : ℕ =>
    (convex_halfSpace_im_gt (0 : ℝ)).exists_forall_hasDerivWithinAt (hd j)
  refine ⟨fun j z => G j z - G j Complex.I, fun j => sub_self _, fun j z hz => ?_⟩
  exact ((hG j z hz).hasDerivAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).sub_const _

/-- The polynomial in `v = (x, y)` of the `I`-normalized primitive of the binary integrand:
`∑_j C(n+1, j) (-1)^{n+1-j} G_j(w) y^j x^{n+1-j}`, `G_j` the moment primitives. -/
def eichlerPoly (n : ℕ) (G : ℕ → ℂ → ℂ) (w : ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ Finset.range (n + 2),
    MvPolynomial.C (G j w * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j)) *
      MvPolynomial.X 1 ^ j * MvPolynomial.X 0 ^ (n + 1 - j)

theorem eichlerPoly_isHomogeneous (n : ℕ) (G : ℕ → ℂ → ℂ) (w : ℂ) :
    MvPolynomial.IsHomogeneous (eichlerPoly n G w) (n + 1) := by
  unfold eichlerPoly
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hj
  have h1 := ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow j).mul
    ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow (n + 1 - j))
  have e : 1 * j + 1 * (n + 1 - j) = n + 1 := by omega
  rw [e] at h1
  have h2 := (MvPolynomial.isHomogeneous_C (Fin 2)
    (G j w * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j))).mul h1
  rw [zero_add] at h2
  rw [mul_assoc]
  exact h2

theorem eval_eichlerPoly (n : ℕ) (G : ℕ → ℂ → ℂ) (w : ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (eichlerPoly n G w) =
      ∑ j ∈ Finset.range (n + 2),
        G j w * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j) * v 1 ^ j * v 0 ^ (n + 1 - j) := by
  simp [eichlerPoly, map_sum]

theorem eichlerPoly_hasDerivAt (n : ℕ) (h : ℂ → ℂ) (G : ℕ → ℂ → ℂ)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z) (v : Fin 2 → ℂ) {z : ℂ}
    (hz : 0 < z.im) :
    HasDerivAt (fun w => MvPolynomial.eval v (eichlerPoly n G w)) (binaryIntegrand n h v z) z := by
  simp only [eval_eichlerPoly]
  have hs := HasDerivAt.fun_sum (u := Finset.range (n + 2)) (x := z)
    (A := fun j w => G j w * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j) * v 1 ^ j *
      v 0 ^ (n + 1 - j))
    (A' := fun j => h z * z ^ j * ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j) * v 1 ^ j *
      v 0 ^ (n + 1 - j))
    (fun j _ => (((((hG j z hz).mul_const _).mul_const _).mul_const _).mul_const _))
  refine hs.congr_deriv ?_
  unfold binaryIntegrand
  rw [show (z * v 1 - v 0) = z * v 1 + (-v 0) by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, neg_pow]
  ring

/-- The linear substitution realizing `invCoord γ` on binary forms. -/
def invCoordPoly (γ : GL (Fin 2) ℝ) : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.C ((γ 1 1 : ℝ) : ℂ) * MvPolynomial.X 0 -
      MvPolynomial.C ((γ 0 1 : ℝ) : ℂ) * MvPolynomial.X 1,
    -(MvPolynomial.C ((γ 1 0 : ℝ) : ℂ)) * MvPolynomial.X 0 +
      MvPolynomial.C ((γ 0 0 : ℝ) : ℂ) * MvPolynomial.X 1]

theorem eval_bind₁_invCoordPoly (γ : GL (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ (invCoordPoly γ) P) =
      MvPolynomial.eval (invCoord γ v) P := by
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) v (invCoordPoly γ) P
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) v (MvPolynomial.bind₁ (invCoordPoly γ) P) =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (invCoord γ v) P
  have hf : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) v (invCoordPoly γ i)) =
      invCoord γ v := by
    funext i
    fin_cases i <;> simp [invCoordPoly, invCoord]
  rw [h, hf]

/-- **The Eichler cocycle** of weight `n + 3`: the value at `γ i` of the `i`-normalized primitive,
a homogeneous binary form of degree `n + 1`. -/
def eichlerCocycle (n : ℕ) (G : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) : MvPolynomial (Fin 2) ℂ :=
  eichlerPoly n G (mob γ Complex.I)

theorem eichlerCocycle_isHomogeneous (n : ℕ) (G : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) :
    MvPolynomial.IsHomogeneous (eichlerCocycle n G γ) (n + 1) :=
  eichlerPoly_isHomogeneous n G _

theorem eichlerPoly_base (n : ℕ) (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0) :
    eichlerPoly n G Complex.I = 0 := by
  simp [eichlerPoly, hG0]

theorem eval_eichlerCocycle (n : ℕ) (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (γ : GL (Fin 2) ℝ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (eichlerCocycle n G γ) =
      periodConst (fun v w => MvPolynomial.eval v (eichlerPoly n G w)) γ v := by
  unfold periodConst eichlerCocycle
  simp only [eichlerPoly_base n G hG0, map_zero, sub_zero]

/-- **The Eichler cocycle is a 1-cocycle for the action on binary forms**:
`c(γδ) = c(γ) + γ·c(δ)`, where `γ·P = P ∘ γ⁻¹`. -/
theorem eichlerCocycle_mul (n : ℕ) (h : ℂ → ℂ) (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (h z * z ^ j) z) (γ δ : GL (Fin 2) ℝ)
    (hγ : γ.det = 1) (hδ : δ.det = 1)
    (hmodγ : ∀ z : ℂ, 0 < z.im → h (mob γ z) = dnm γ z ^ (n + 3) * h z) :
    eichlerCocycle n G (γ * δ) =
      eichlerCocycle n G γ + MvPolynomial.bind₁ (invCoordPoly γ) (eichlerCocycle n G δ) := by
  apply MvPolynomial.funext
  intro v
  rw [map_add, eval_bind₁_invCoordPoly, eval_eichlerCocycle n G hG0,
    eval_eichlerCocycle n G hG0, eval_eichlerCocycle n G hG0]
  exact periodConst_mul n h γ δ hγ hδ hmodγ _
    (fun v z hz => eichlerPoly_hasDerivAt n h G hG v hz) v

end TernaryPeriodPolynomials.Argument.SeedC3
