module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Gram
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FaceRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane

@[expose] public section


/-!
# The Gram cone maps equivariantly to the plane boundary model `e(P)`

Formalized by Claude Sonnet 5.5.

The first four plane coordinates `(u₁, u₂, x, y)` of the unimodular normalization `conePoint` of a Gram matrix give a smooth
map `coneFace : Gram cone → e(P)` equivariant for any plane parabolic group `D` realized by matrices in `SL₃(ℤ)`:
the seed `ω_h` ignores the fifth coordinate, and the first four coordinates transform under `[[λ, w], [0, 1]]` exactly by the
action of `D` on the face.
-/

open scoped Matrix.Norms.Elementwise ContDiff
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.FormCochainBridge

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The first four plane coordinates `(u₁, u₂, x, y)`. -/
def pr4 (p : Fin 5 → ℝ) : Face := ![p 0, p 1, p 2, p 3]

theorem pr4_mem {p : Fin 5 → ℝ} (hp : p ∈ Omega) : pr4 p ∈ faceSet := by
  have : 0 < p 3 := hp.1
  simpa [faceSet, pr4] using this

theorem seedTau_eq_faceTau (p : Fin 5 → ℝ) : seedTau p = faceTau (pr4 p) := by
  simp [seedTau, faceTau, pr4]
  ring

/-- **Equivariance of the first four coordinates**: for a plane parabolic group, the first four coordinates of
`planeAct (plm g) p` are the face action of `g` on those of `p` (translations do not involve the fifth coordinate, and the
Levi part has `t = 1`). -/
theorem planeAct_plm_pr4 {G : Type} [Group G] (D : PlaneData G) (g : G) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    pr4 (planeAct (D.plm g) p) = D.act g (pr4 p) := by
  have hdet : (D.lam g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have := D.det_one g
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val this
  have hd1 : (diagMat (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1).det = 1 := by
    rw [det_diagMat, hdet]; norm_num
  have hlev := planeAct_diag (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1
    (by rw [hdet]; exact one_pos) one_pos (by rw [hdet]; norm_num) hp
  have hL : leviMap (D.lam g : Matrix (Fin 2) (Fin 2) ℝ) 1 p ∈ Omega := by
    rw [← hlev]; exact planeAct_mem hd1 hp
  rw [PlaneData.plm, ConvergenceC4.parabolicMatrix_eq_mul, planeAct_mul hd1 hp, hlev,
    planeAct_transMat _ _ hL]
  funext i
  fin_cases i
  · simp [leviMap, pr4, PlaneData.act]
  · simp [leviMap, pr4, PlaneData.act]
  · simp [leviMap, pr4, PlaneData.act, mob]
    rw [seedTau_eq_faceTau]; rfl
  · simp [leviMap, pr4, PlaneData.act, mob]
    rw [seedTau_eq_faceTau]; rfl

theorem contDiff_pr4 : ContDiff ℝ ∞ pr4 := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simpa [pr4] using contDiff_pi.mp contDiff_id _

/-- The first four coordinates of the unimodular normalization: `Gram cone → e(P)`. -/
def coneFace (G : Mat3) : Face := pr4 (conePoint G)

theorem contDiffOn_coneFace : ContDiffOn ℝ ∞ coneFace gramCone :=
  contDiff_pr4.comp_contDiffOn contDiffOn_conePoint

theorem coneFace_mem {G : Mat3} (hG : G ∈ gramCone) : coneFace G ∈ faceSet :=
  pr4_mem (conePoint_mem hG)

/-- **The Gram cone maps equivariantly to the plane boundary model `e(P)`** for `Γ_P = Γ(N) ∩ P(ℤ)`. -/
def coneFaceEquiv (N : ℕ) :
    EquivMap isOpen_gramCone isOpen_faceSet (coneAction (gammaNP N)) (gammaNPlaneData N).action
      (MonoidHom.id (gammaNP N)) where
  φ := coneFace
  smooth := contDiffOn_coneFace
  mapsTo _ hG := coneFace_mem hG
  equiv g _ hG := by
    change pr4 (conePoint (realMat g.1 * _ * (realMat g.1).transpose)) = (gammaNPlaneData N).act g (pr4 (conePoint _))
    rw [conePoint_conj (det_realMat g.1) hG, ← gammaNPlaneData_plm N g]
    exact planeAct_plm_pr4 (gammaNPlaneData N) g (conePoint_mem hG)

end TernaryPeriodPolynomials.Argument.FormSeedBridge
