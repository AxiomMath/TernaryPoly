module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagDeRham

@[expose] public section


/-!
# The action of a plane parabolic group on the face `e(P) = ℝ² × ℍ`

Coordinates `x = (u₁, u₂, Re τ, Im τ)`. The group element with data `(λ, w)` acts by
`(u, τ) ↦ (λu + w, λτ)` (Möbius action of `λ`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial Complex
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- Coordinates `(u₁, u₂, x, y)` of the face. -/
abbrev Face := Fin 4 → ℝ

/-- The open convex face `{y > 0}`. -/
def faceSet : Set Face := {x | 0 < x 3}

/-- The point `τ = x + iy` of the upper half-plane. -/
def faceTau (x : Face) : ℂ := (x 2 : ℂ) + (x 3 : ℂ) * Complex.I

theorem isOpen_faceSet : IsOpen faceSet :=
  isOpen_lt continuous_const (continuous_apply 3)

theorem convex_faceSet : Convex ℝ faceSet := by
  intro x hx y hy a b ha hb hab
  change 0 < x 3 at hx
  change 0 < y 3 at hy
  change 0 < (a • x + b • y) 3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simpa using hy
  · have : 0 < a * x 3 := mul_pos ha' hx
    have : 0 ≤ b * y 3 := mul_nonneg hb hy.le
    linarith

theorem faceSet_nonempty : faceSet.Nonempty := ⟨![0, 0, 0, 1], by simp [faceSet]⟩

theorem faceTau_im {x : Face} (hx : x ∈ faceSet) : 0 < (faceTau x).im := by
  have : 0 < x 3 := hx
  simpa [faceTau] using this

theorem contDiff_faceTau : ContDiff ℝ ∞ faceTau := by
  unfold faceTau
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp contDiff_id 2)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp contDiff_id 3)).mul contDiff_const)

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G)

/-- The action on the face coordinates. -/
def act (g : G) (x : Face) : Face :=
  ![(D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * x 0 + (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * x 1
      + D.w g 0,
    (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * x 0 + (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * x 1
      + D.w g 1,
    (mob (D.lam g) (faceTau x)).re, (mob (D.lam g) (faceTau x)).im]

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
  · exact (((contDiff_const.mul (contDiff_pi.mp contDiff_id 0)).add
      (contDiff_const.mul (contDiff_pi.mp contDiff_id 1))).add contDiff_const).contDiffOn
  · exact (((contDiff_const.mul (contDiff_pi.mp contDiff_id 0)).add
      (contDiff_const.mul (contDiff_pi.mp contDiff_id 1))).add contDiff_const).contDiffOn
  · intro x hx
    exact (Complex.reCLM.contDiff.contDiffAt.comp x (hmob x hx)).contDiffWithinAt
  · intro x hx
    exact (Complex.imCLM.contDiff.contDiffAt.comp x (hmob x hx)).contDiffWithinAt

theorem act_zero (g : G) (x : Face) : D.act g x 0 =
    (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * x 0 + (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * x 1
      + D.w g 0 := by simp [act]

theorem act_one (g : G) (x : Face) : D.act g x 1 =
    (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * x 0 + (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * x 1
      + D.w g 1 := by simp [act]

theorem act_two (g : G) (x : Face) : D.act g x 2 = (mob (D.lam g) (faceTau x)).re := by
  simp [act]

theorem act_three (g : G) (x : Face) : D.act g x 3 = (mob (D.lam g) (faceTau x)).im := by
  simp [act]

theorem act_mul (g h : G) {x : Face} (hx : x ∈ faceSet) :
    D.act (g * h) x = D.act g (D.act h x) := by
  have hdg := D.det_one g
  have hdh := D.det_one h
  have hτ : faceTau (D.act h x) = mob (D.lam h) (faceTau x) := by
    simp only [faceTau, D.act_two, D.act_three]
    exact Complex.re_add_im _
  have hm : mob (D.lam (g * h)) (faceTau x) = mob (D.lam g) (mob (D.lam h) (faceTau x)) := by
    rw [map_mul, mob_mul (D.lam g) (D.lam h) hdg hdh (faceTau_im hx)]
  ext i
  fin_cases i
  · show D.act (g * h) x 0 = D.act g (D.act h x) 0
    rw [D.act_zero (g * h), D.act_zero g, D.act_zero h, D.act_one h, D.w_mul]
    simp only [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.mulVec, dotProduct]
    ring
  · show D.act (g * h) x 1 = D.act g (D.act h x) 1
    rw [D.act_one (g * h), D.act_one g, D.act_zero h, D.act_one h, D.w_mul]
    simp only [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.mulVec, dotProduct]
    ring
  · show D.act (g * h) x 2 = D.act g (D.act h x) 2
    rw [D.act_two, D.act_two, hτ, hm]
  · show D.act (g * h) x 3 = D.act g (D.act h x) 3
    rw [D.act_three, D.act_three, hτ, hm]

/-- The action of the plane parabolic group on the face, as a `ZigZag.Action`. -/
def action : ZigZag.Action G faceSet where
  act := D.act
  smooth := D.act_contDiffOn
  mapsTo := D.act_mapsTo
  mul g h _ hx := D.act_mul g h hx

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
