module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Data
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneAction

@[expose] public section


/-!
# The action of a line parabolic group on the line face `ℝ² × ℍ` (line mirror of `SeedC3.PlaneAction`)

Coordinates `x = (w₁, w₂, Re τ, Im τ)` (the face `Face`, `faceSet`, `faceTau` of the plane are reused).  The element with data `(C, v)`
acts by `(w, τ) ↦ ((w + v) C⁻¹, C·τ)` (row vector `w`, Möbius action of `C`), which is the action `G ↦ q G qᵀ` of `q = [[1, v], [0, C]]` in the
line chart (`Entry.lineChart_lineConj_w`, `Entry.lineTau_lineConj`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial Complex
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3

namespace LineData

variable {G : Type} [Group G] (D : LineData G)

/-- The action on the face coordinates. -/
def act (g : G) (x : Face) : Face :=
  ![(x 0 + D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (x 1 + D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 0,
    -(x 0 + D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 +
      (x 1 + D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 0,
    (mob (D.lam g) (faceTau x)).re, (mob (D.lam g) (faceTau x)).im]

theorem act_zero (g : G) (x : Face) : D.act g x 0 =
    (x 0 + D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (x 1 + D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [act]

theorem act_one (g : G) (x : Face) : D.act g x 1 =
    -(x 0 + D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 +
      (x 1 + D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by simp [act]

theorem act_two (g : G) (x : Face) : D.act g x 2 = (mob (D.lam g) (faceTau x)).re := by simp [act]

theorem act_three (g : G) (x : Face) : D.act g x 3 = (mob (D.lam g) (faceTau x)).im := by simp [act]

theorem faceTau_act (g : G) (x : Face) : faceTau (D.act g x) = mob (D.lam g) (faceTau x) := by
  simp only [faceTau, D.act_two, D.act_three]
  exact Complex.re_add_im _

theorem act_mapsTo (g : G) : Set.MapsTo (D.act g) faceSet faceSet := by
  intro x hx
  have hpos : 0 < (D.lam g).det.val := by simp [D.det_one g]
  have := mob_im_pos (D.lam g) hpos (faceTau_im hx)
  simpa [faceSet, act] using this

theorem contDiffAt_mob (γ : GL (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℂ ∞ (mob γ) z := by
  unfold mob
  exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) (dnm_ne_zero γ hz)

theorem act_contDiffOn (g : G) : ContDiffOn ℝ ∞ (D.act g) faceSet := by
  rw [contDiffOn_pi]
  intro i
  have hτ := contDiff_faceTau
  have hmob : ∀ x ∈ faceSet, ContDiffAt ℝ ∞ (fun x : Face => mob (D.lam g) (faceTau x)) x :=
    fun x hx => ((contDiffAt_mob (D.lam g) (faceTau_im hx)).restrict_scalars ℝ).comp x
      hτ.contDiffAt
  fin_cases i
  · exact ((((contDiff_pi.mp contDiff_id 0).add contDiff_const).mul contDiff_const).sub
      (((contDiff_pi.mp contDiff_id 1).add contDiff_const).mul contDiff_const)).contDiffOn
  · exact ((((contDiff_pi.mp contDiff_id 0).add contDiff_const).neg.mul contDiff_const).add
      (((contDiff_pi.mp contDiff_id 1).add contDiff_const).mul contDiff_const)).contDiffOn
  · intro x hx
    exact (Complex.reCLM.contDiff.contDiffAt.comp x (hmob x hx)).contDiffWithinAt
  · intro x hx
    exact (Complex.imCLM.contDiff.contDiffAt.comp x (hmob x hx)).contDiffWithinAt

theorem act_mul (g h : G) {x : Face} (hx : x ∈ faceSet) :
    D.act (g * h) x = D.act g (D.act h x) := by
  have hdg := Matrix.GeneralLinearGroup.det_ne_zero (D.lam g)
  have hg := det_eq_one (D.lam g) (D.det_one g)
  have hh := det_eq_one (D.lam h) (D.det_one h)
  have hm : mob (D.lam (g * h)) (faceTau x) = mob (D.lam g) (mob (D.lam h) (faceTau x)) := by
    rw [map_mul, mob_mul (D.lam g) (D.lam h) (D.det_one g) (D.det_one h) (faceTau_im hx)]
  ext i
  fin_cases i
  · show D.act (g * h) x 0 = D.act g (D.act h x) 0
    rw [D.act_zero (g * h), D.act_zero g, D.act_zero h, D.act_one h, D.v_mul]
    simp only [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.vecMul, dotProduct]
    linear_combination ((D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) * hh
  · show D.act (g * h) x 1 = D.act g (D.act h x) 1
    rw [D.act_one (g * h), D.act_one g, D.act_zero h, D.act_one h, D.v_mul]
    simp only [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.vecMul, dotProduct]
    linear_combination ((-D.v g 0) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 +
      (D.v g 1) * (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * hh
  · show D.act (g * h) x 2 = D.act g (D.act h x) 2
    rw [D.act_two, D.act_two, D.faceTau_act, hm]
  · show D.act (g * h) x 3 = D.act g (D.act h x) 3
    rw [D.act_three, D.act_three, D.faceTau_act, hm]

/-- The action of the line parabolic group on the face, as a `ZigZag.Action`. -/
def action : ZigZag.Action G faceSet where
  act := D.act
  smooth := D.act_contDiffOn
  mapsTo := D.act_mapsTo
  mul g h _ hx := D.act_mul g h hx

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
