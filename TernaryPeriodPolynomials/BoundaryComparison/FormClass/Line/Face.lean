module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Radical
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.PlaneInvolution
public import TernaryPeriodPolynomials.EisensteinSeries.Class.GammaNAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FaceRestriction

@[expose] public section


/-!
# U2: the face model of the line cusp `Q` and its averaged class

Formalized by Claude Sonnet 5.5.

The involution `ȷ(g) = J (g⁻¹)ᵗ J` (`jmath`, `jPlane`, `jPlane_equivariant`) exchanges `P` and `Q`.  Hence the face `e(Q)` of the line group `Γ_Q = Γ(N) ∩ Q(ℤ)` is modelled by the
face `e(P) = ℝ² × ℍ` with `Γ_P` acting as usual and the equivariant map `x ↦ ȷ̃(i_P x)` into `Ω` along `ȷ : Γ_P ≃ Γ_Q`:
* `psiQ`, `rhoQ`: `ȷ : Γ_P → Γ(N)` (image `Γ_Q`) and the coefficient representation `ρ(ȷ g)`;
* `lineFaceMap` (an `EquivMap`), `lineFaceForm`: pullback of a closed `Γ(N)`-equivariant form to the face model;
* **`lineFaceForm_class`**: its de Rham class is the group restriction along `psiQ` (the `Q`-analogue of `faceForm_class`);
* `qMat_comm`, `lineTwist`: the data of `TwistData` (the generalization of the average): radical action `ρ(qMat v)`, intertwining, lattice;
* **`lineFace_avg_class`**: the radical average (over `Nℤ²`, coefficient transport `ρ(qMat v)`) of the face pullback has the same class, i.e. represents `r_Q [F]`.
-/

open MvPolynomial CategoryTheory
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces

variable (N : ℕ) (n : ℕ)

/-- `ȷ` restricted to `Γ_P = Γ(N) ∩ P(ℤ)`, as a homomorphism into `Γ(N)` (its image is `Γ_Q`). -/
def psiQ : gammaNP N →* gammaN N where
  toFun g := ⟨jmath g.1, jmath_mem_gammaN.2 g.2.1⟩
  map_one' := Subtype.ext jmath_one
  map_mul' g h := Subtype.ext (jmath_mul g.1 h.1)

theorem psiQ_val (g : gammaNP N) : ((psiQ N g : gammaN N) : SL(3, ℤ)) = jmath g.1 := rfl

/-- The coefficient representation of `Γ_P`, transported through `ȷ`: `ρ(ȷ g)`. -/
def rhoQ : Representation ℝ (gammaNP N) (Coef n) := (gammaRho (gammaN N) n).comp (psiQ N)

/-- **The face model of the line cusp `Q`**: `x ↦ ȷ̃(i_P x)` maps the face `e(P)` into `Ω`. -/
def jFace (x : Face) : Fin 5 → ℝ := jPlane (ptOf x)

theorem contDiffOn_jFace : ContDiffOn ℝ ∞ jFace faceSet :=
  contDiffOn_jPlane.comp contDiffOn_ptOf fun _ hx => ptOf_mem hx

/-- The equivariant map from the face to `Ω`, along `ȷ : Γ_P → Γ(N)` (whose image is `Γ_Q`). -/
def lineFaceMap : EquivMap isOpen_faceSet isOpen_Omega (gammaNPlaneData N).action (gammaAct (gammaN N))
    (psiQ N) where
  φ := jFace
  smooth := contDiffOn_jFace
  mapsTo _ hx := jPlane_mem (ptOf_mem hx)
  equiv g x hx := by
    have hp : ptOf x ∈ Omega := ptOf_mem hx
    have e1 := jPlane_equivariant g.1 hp
    have e2 := planeAct_plm_ptOf (gammaNPlaneData N) g hx
    rw [gammaNPlaneData_plm] at e2
    change jPlane (ptOf ((gammaNPlaneData N).act g x)) = planeAct (realMat (jmath g.1)) (jPlane (ptOf x))
    rw [← e2]
    exact e1

theorem qMat_eq_rt (v : Fin 2 → ℝ) : qMat v = rt (transMat (-v 0) (-v 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat, transMat, rt, Fin.rev]

theorem transMat_inv (a b : ℝ) : (transMat a b)⁻¹ = transMat (-a) (-b) := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem plm_transMat {G : Type} [Group G] (D : PlaneData G) (g : G) (u : Fin 2 → ℝ) :
    D.plm g * transMat (u 0) (u 1) =
      transMat (((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 0)
        (((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 1) * D.plm g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PlaneData.plm, parabolicMatrix, transMat, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The key matrix identity: `qMat(λ_g u) · rt(P_g⁻¹) = rt(P_g⁻¹) · qMat(u)`, i.e. `ȷ` carries the commutation relation of `t_u` and
`P_g` to that of the line radical. -/
theorem qMat_comm {G : Type} [Group G] (D : PlaneData G) (g : G) (u : Fin 2 → ℝ) :
    qMat ((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) * rt (D.plm g)⁻¹ =
      rt (D.plm g)⁻¹ * qMat u := by
  have hdet : (D.plm g).det = 1 := D.det_plm g
  have hP : (D.plm g)⁻¹ * D.plm g = 1 := Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)
  have hP' : D.plm g * (D.plm g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
  have key := plm_transMat D g (-u)
  have hneg : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (-u) = -((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) :=
    Matrix.mulVec_neg _ _
  rw [hneg] at key
  simp only [Pi.neg_apply] at key
  rw [qMat_eq_rt, qMat_eq_rt, ← rt_mul, ← rt_mul]
  congr 1
  calc (D.plm g)⁻¹ * transMat (-((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 0)
          (-((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 1)
      = (D.plm g)⁻¹ * (transMat (-((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 0)
          (-((D.lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec u) 1) * D.plm g) * (D.plm g)⁻¹ := by
        simp only [Matrix.mul_assoc, hP', Matrix.mul_one]
    _ = (D.plm g)⁻¹ * (D.plm g * transMat (-u 0) (-u 1)) * (D.plm g)⁻¹ := by rw [key]
    _ = transMat (-u 0) (-u 1) * (D.plm g)⁻¹ := by
        rw [← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem toPoly_rhoQ (g : gammaNP N) (q : Coef n) :
    Coef.toPoly (ZigZag.repCLM (rhoQ N n) g q) = rho (realMat (jmath g.1)) (Coef.toPoly q) :=
  toPoly_gammaRho (gammaN N) n (psiQ N g) q

/-- **The twisted average data of the line face**: the coefficient representation `ρ(ȷ g)`, the radical action `ρ(qMat v)`. -/
def lineTwist [NeZero N] : TwistData (gammaNPlaneData N) n (N : ℝ) where
  ρ' := rhoQ N n
  σ := sQ n
  uni := uniRep_sQ n
  levi g := levi_integral (latticeData_gammaN N) g
  hint g u := by
    refine ContinuousLinearMap.ext fun q => ?_
    simp only [ContinuousLinearMap.comp_apply]
    apply Coef.toPoly_injective
    rw [toPoly_sQ, toPoly_rhoQ, toPoly_rhoQ, toPoly_sQ, rho_mul, rho_mul, realMat_jmath, ← gammaNPlaneData_plm,
      qMat_comm]
  lattice k := by
    obtain ⟨ν, hν1, hν2⟩ := (latticeData_gammaN N).lattice k
    refine ⟨ν, hν1, hν2, ?_⟩
    refine ContinuousLinearMap.ext fun q => ?_
    apply Coef.toPoly_injective
    rw [toPoly_rhoQ, toPoly_sQ, realMat_jmath, ← gammaNPlaneData_plm]
    congr 1
    have hplm : (gammaNPlaneData N).plm ν = transMat ((gammaNPlaneData N).w ν 0) ((gammaNPlaneData N).w ν 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [PlaneData.plm, parabolicMatrix, transMat, hν1]
    rw [hplm, transMat_inv, ← qMat_eq_rt, hν2]

/-- **The pullback of a closed `Γ(N)`-equivariant form to the face model of `Q`.** -/
def lineFaceForm (F : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) :
    ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n) :=
  pullInv (lineFaceMap N) (fun _ => rfl) F

/-- **The class of the pullback to the face model of `Q` is the group restriction of the class** (`Γ_P ≃ Γ_Q` through `ȷ`). -/
theorem lineFaceForm_class (F : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
        (lineFaceForm N n F) =
      (groupCohomology.map (psiQ N) (resMor (psiQ N) (rhoQ N n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N)) (gammaRho (gammaN N) n) F) :=
  deRhamClass_natural (lineFaceMap N) convex_faceSet faceSet_nonempty convex_Omega Omega_nonempty (fun _ => rfl) F

/-- **U2: the radical average of the face model of `Q` represents the restriction `r_Q`.**  For every closed `Γ(N)`-equivariant form `F` the torus
average (over the radical lattice `Nℤ²` of `Q`, with the coefficient transport `ρ(qMat v)`) of its pullback to the face model of `Q` has the class
`(ȷ)^* r_Q [F]`, i.e. the group restriction of `[F]` to `Γ_Q` read through `ȷ : Γ_P ≃ Γ_Q`. -/
theorem lineFace_avg_class [NeZero N]
    (F : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
        ((lineTwist N n).avInvT (lineFaceForm N n F)) =
      (groupCohomology.map (psiQ N) (resMor (psiQ N) (rhoQ N n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N)) (gammaRho (gammaN N) n) F) :=
  ((lineTwist N n).deRhamClass_avInvT (Nat.cast_ne_zero.mpr (NeZero.ne N)) (lineFaceForm N n F)).trans
    (lineFaceForm_class N n F)

end TernaryPeriodPolynomials.Argument.FormClassK
