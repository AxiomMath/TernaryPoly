module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Trans
public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural

@[expose] public section


/-!
# Translated, coefficient-transported forms and their equivariance

(averaging on
the fiber with coefficient transport `ρ(u)⁻¹`; "both maps commute with the lattice-preserving Levi
action, which preserves normalized Haar measure and transports the coframe and coefficients
together").

For a form `F` on the face `e(P)` and `v ∈ ℝ²` put `F_v = ρ(t_v)⁻¹ τ_v^* F` (`shiftForm`). For a
plane parabolic group `D` acting on the face (`Γ_P = Nℤ² ⋊ Λ`) and a `D`-invariant `F`
(`g^*F = ρ(g)F`):

* `pullForm_shiftForm`: `g^* F_v = ρ(g) F_{λ_g⁻¹ v}` (the Levi block permutes the translation family);
* `shiftForm_add_lattice`: `F_{u + v} = F_v` for a lattice vector `u` realized by an element of the
  group (`F_v` is periodic in `v`, which is why the coefficient transport is part of the average).

These are identities of chart forms (no integration). They rest on `trL_comp_rho`, the conjugation
law `ρ(t_{-v}) ρ(g) = ρ(g) ρ(t_{-λ_g⁻¹ v})`, and on `pullBack_pullForm` (naturality of pullbacks
along the equivariant map `x ↦ g x` of the translation group).

Formalized by Claude Sonnet 5.5.
-/

open scoped ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

variable {G : Type} [Group G] (D : PlaneData G) (n : ℕ)

/-- The linear action `v ↦ λ_g v` of the Levi block on translation vectors, as a hom of the
translation group. -/
def lamHom (g : G) : TransGrp →* TransGrp :=
  AddMonoidHom.toMultiplicative
    ((Matrix.mulVecLin (D.lam g : Matrix (Fin 2) (Fin 2) ℝ)).toAddMonoidHom)

theorem lamHom_apply (g : G) (v : Fin 2 → ℝ) :
    lamHom D g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) := rfl

theorem lamHom_toAdd (g : G) (s : TransGrp) :
    Multiplicative.toAdd (lamHom D g s) =
      (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (Multiplicative.toAdd s) := rfl

theorem lam_mulVec_inv (g : G) (v : Fin 2 → ℝ) :
    (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one]
  simp

theorem lam_mulVec_inv' (g : G) (v : Fin 2 → ℝ) :
    (D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]
  simp

theorem act_trPD (g : G) (s : TransGrp) {x : Face} :
    D.act g (trPD.act s x) = trPD.act (lamHom D g s) (D.act g x) := by
  rw [trPD_act s x, trPD_act (lamHom D g s) (D.act g x)]
  funext i
  fin_cases i
  · simp [PlaneData.act, lamHom_toAdd, Matrix.mulVec, dotProduct, Fin.sum_univ_two, faceTau]
    ring
  · simp [PlaneData.act, lamHom_toAdd, Matrix.mulVec, dotProduct, Fin.sum_univ_two, faceTau]
    ring
  · simp [PlaneData.act, faceTau, mob]
  · simp [PlaneData.act, faceTau, mob]

/-- The Levi action `g` on the face is equivariant for the translation group along `lamHom`. -/
def lamEquiv (g : G) : EquivMap isOpen_faceSet isOpen_faceSet trPD.action trPD.action
    (lamHom D g) where
  φ := D.act g
  smooth := D.act_contDiffOn g
  mapsTo := D.act_mapsTo g
  equiv s _ _ := act_trPD D g s

/-- Pulling back along `g` is the pullback of the group action. -/
theorem pullBack_act_eq (g : G) (w : Form (F := Coef n) faceSet 2) :
    pullBack isOpen_faceSet (D.act_contDiffOn g) (D.act_mapsTo g) 2 w =
      ZigZag.pullForm isOpen_faceSet D.action g 2 w := by
  apply Form.ext
  intro x hx
  rw [pullBack_apply isOpen_faceSet _ _ _ hx, ZigZag.pullForm_apply isOpen_faceSet D.action g _ hx]
  rfl

/-- **Commutation of `g^*` and the translation pullback**:
`g^* τ_v^* = τ_{λ_g⁻¹ v}^* g^*`. -/
theorem pullForm_comm_trPull (g : G) (v : Fin 2 → ℝ) (w : Form (F := Coef n) faceSet 2) :
    ZigZag.pullForm isOpen_faceSet D.action g 2
        (ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) 2 w) =
      ZigZag.pullForm isOpen_faceSet trPD.action
        (Multiplicative.ofAdd ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) 2
        (ZigZag.pullForm isOpen_faceSet D.action g 2 w) := by
  have h := pullBack_pullForm isOpen_faceSet isOpen_faceSet trPD.action trPD.action (lamHom D g)
    (lamEquiv D g).smooth (lamEquiv D g).mapsTo (lamEquiv D g).equiv
    (Multiplicative.ofAdd ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v)) w
  rw [lamHom_apply, lam_mulVec_inv] at h
  have e : pullBack (F := Coef n) isOpen_faceSet (lamEquiv D g).smooth (lamEquiv D g).mapsTo 2 =
      pullBack (F := Coef n) isOpen_faceSet (D.act_contDiffOn g) (D.act_mapsTo g) 2 := rfl
  rw [e] at h
  simpa only [pullBack_act_eq] using h

/-- The conjugation law `ρ(t_{-v}) ρ(g) = ρ(g) ρ(t_{-λ_g⁻¹ v})` for `g = [[λ, w], [0, 1]]`. -/
theorem trL_comp_rho (g : G) (v : Fin 2 → ℝ) :
    (trL n (-v)).comp (ZigZag.repCLM (D.rhoR n) g) =
      (ZigZag.repCLM (D.rhoR n) g).comp
        (trL n (-((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v))) := by
  ext q
  apply Coef.toPoly_injective
  have h0 := congrFun (lam_mulVec_inv D g v) 0
  have h1 := congrFun (lam_mulVec_inv D g v) 1
  generalize (D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v = u at h0 h1 ⊢
  have e1 : Coef.toPoly ((trL n (-v)).comp (ZigZag.repCLM (D.rhoR n) g) q) =
      SeedC3.rho (transMat (-v 0) (-v 1) * D.plm g) (Coef.toPoly q) := by
    change Coef.toPoly (trL n (-v) (D.rhoCoef n g q)) = _
    rw [toPoly_trL, D.toPoly_rhoCoef, rho_mul]
    simp only [Pi.neg_apply]
  have e2 : Coef.toPoly ((ZigZag.repCLM (D.rhoR n) g).comp (trL n (-u)) q) =
      SeedC3.rho (D.plm g * transMat (-u 0) (-u 1)) (Coef.toPoly q) := by
    change Coef.toPoly (D.rhoCoef n g (trL n _ q)) = _
    rw [D.toPoly_rhoCoef, toPoly_trL, rho_mul]
    simp only [Pi.neg_apply]
  rw [e1, e2]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  unfold PlaneData.plm
  generalize (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) = L at h0 h1 ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, transMat, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [h0, h1]

/-- **The translated, coefficient-transported form** `F_v = ρ(t_v)⁻¹ τ_v^* F`. -/
def shiftForm (v : Fin 2 → ℝ) :
    Form (F := Coef n) faceSet 2 →ₗ[ℝ] Form (F := Coef n) faceSet 2 :=
  (ZigZag.twForm (trL n (-v)) 2).comp
    (ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd v) 2)

/-- Pullbacks along two actions agreeing pointwise on the chart coincide. -/
theorem pullForm_congr_act {G' : Type} [Group G'] (A : ZigZag.Action G faceSet)
    (B : ZigZag.Action G' faceSet) (g : G) (g' : G') (h : ∀ x ∈ faceSet, A.act g x = B.act g' x)
    (w : Form (F := Coef n) faceSet 2) :
    ZigZag.pullForm isOpen_faceSet A g 2 w = ZigZag.pullForm isOpen_faceSet B g' 2 w := by
  apply Form.ext
  intro x hx
  rw [ZigZag.pullForm_apply isOpen_faceSet A g _ hx, ZigZag.pullForm_apply isOpen_faceSet B g' _ hx]
  have : A.act g =ᶠ[nhds x] B.act g' := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using h y hy
  exact pullRaw_eventuallyEq _ this

/-- **Equivariance of the translated forms**: for a `Γ_P`-invariant `F`,
`g^* F_v = ρ(g) F_{λ_g⁻¹ v}`. -/
theorem pullForm_shiftForm (g : G) (v : Fin 2 → ℝ) (F : Form (F := Coef n) faceSet 2)
    (hF : ZigZag.pullForm isOpen_faceSet D.action g 2 F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) 2 F) :
    ZigZag.pullForm isOpen_faceSet D.action g 2 (shiftForm n v F) =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) g) 2
        (shiftForm n ((D.lam g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).mulVec v) F) := by
  unfold shiftForm
  simp only [LinearMap.comp_apply]
  rw [ZigZag.pullForm_twForm isOpen_faceSet D.action g, pullForm_comm_trPull, hF,
    ZigZag.pullForm_twForm isOpen_faceSet trPD.action, ← ZigZag.twForm_mul, ← ZigZag.twForm_mul,
    trL_comp_rho]

/-- **Periodicity**: if `F` is invariant under a lattice element `ν` of `Γ_P` with `λ_ν = 1`,
`w_ν = u`, then `F_{v + u} = F_v`. -/
theorem shiftForm_add_lattice (ν : G) (hν : (D.lam ν : Matrix (Fin 2) (Fin 2) ℝ) = 1)
    (u v : Fin 2 → ℝ) (hu : D.w ν = u) (F : Form (F := Coef n) faceSet 2)
    (hF : ZigZag.pullForm isOpen_faceSet D.action ν 2 F =
      ZigZag.twForm (ZigZag.repCLM (D.rhoR n) ν) 2 F) :
    shiftForm n (u + v) F = shiftForm n v F := by
  have hact : ∀ x ∈ faceSet, D.action.act ν x = trPD.action.act (Multiplicative.ofAdd u) x := by
    intro x hx
    change D.act ν x = trPD.act (Multiplicative.ofAdd u) x
    rw [trPD_act]
    funext i
    fin_cases i
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, hu, faceTau]
    · simp [PlaneData.act, hν, faceTau, mob]
    · simp [PlaneData.act, hν, faceTau, mob]
  have hrho : ZigZag.repCLM (D.rhoR n) ν = trL n u := by
    ext q
    apply Coef.toPoly_injective
    change Coef.toPoly (D.rhoCoef n ν q) = _
    rw [D.toPoly_rhoCoef, toPoly_trL]
    unfold PlaneData.plm
    rw [hν, hu]
    congr 1
  have h1 : ZigZag.pullForm isOpen_faceSet trPD.action (Multiplicative.ofAdd u) 2 F =
      ZigZag.twForm (trL n u) 2 F := by
    rw [← pullForm_congr_act n D.action trPD.action ν (Multiplicative.ofAdd u) hact, hF, hrho]
  unfold shiftForm
  simp only [LinearMap.comp_apply]
  rw [ofAdd_add, ZigZag.pullForm_mul isOpen_faceSet trPD.action, h1,
    ZigZag.pullForm_twForm isOpen_faceSet trPD.action, ← ZigZag.twForm_mul]
  have hc : (trL n (-(u + v))).comp (trL n u) = trL n (-v) := by
    rw [← trL_add]
    congr 1
    abel
  rw [hc]

end TernaryPeriodPolynomials.Argument.EisensteinClass
