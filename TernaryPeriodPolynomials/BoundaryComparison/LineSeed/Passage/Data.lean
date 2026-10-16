module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Cusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces

@[expose] public section


/-!
# The Γ(N) line group `Γ(N) ∩ Q(ℤ)` as a line parabolic group (Passage 1)

The line group `Γ_Q = Γ(N) ∩ Q(ℤ)` of the paper (elements of `Γ(N)` with first column `(1, 0, 0)ᵗ`, radical `Nℤ²`, Levi `Γ₂(N)`) is the
group of the matrices `[[1, v], [0, C]]` of the line parabolic `⟨e₁⟩` itself, so no pivot is needed (unlike `Λ₁⁺`, whose line is `⟨e₃⟩`):
`gammaNQLineData N : LineData ↥(gammaNQ N)` has `lam g` the Levi block, `v g` the first row, and `lmat g` is the real matrix of `g`
(`gammaNQ_lmat`).  Consequently the geometric coefficient representation `rhoC n` is the ambient `E_n` restricted to the line group
(`gammaNQ_rhoC_ambient`, `lineNRep_eq`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (lineParabolic)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep)
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N]

/-- The Levi block of `Γ(N) ∩ Q(ℤ)` as a homomorphism to `GL₂(ℝ)`. -/
def gammaNQLam : ↥(gammaNQ N) →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp ((CongruenceSubgroup.Gamma N).subtype.comp (gammaNQProj N))

/-- The first row `(g₀₁, g₀₂)` (the radical coordinate) of an element of `Γ(N) ∩ Q(ℤ)`. -/
def gammaNQV (g : ↥(gammaNQ N)) : Fin 2 → ℝ :=
  ![(((g.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℤ) : ℝ), (((g.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℤ) : ℝ)]

omit [NeZero N] in
theorem gammaNQLam_entry (g : ↥(gammaNQ N)) (i j : Fin 2) :
    ((gammaNQLam N g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (((g.1 : Matrix (Fin 3) (Fin 3) ℤ) i.succ j.succ : ℤ) : ℝ) := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaNQProj N g).1 : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> rfl

omit [NeZero N] in
theorem gammaNQ_det_one (g : ↥(gammaNQ N)) : (gammaNQLam N g).det = 1 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ (gammaNQProj N g).1).det = 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have h := (RingHom.map_det (Int.castRingHom ℝ) ((gammaNQProj N g).1 : Matrix (Fin 2) (Fin 2) ℤ)).symm
  rw [Matrix.SpecialLinearGroup.det_coe] at h
  simpa using h

omit [NeZero N] in
theorem gammaNQ_v_mul (g h : ↥(gammaNQ N)) :
    gammaNQV N (g * h) = gammaNQV N h +
      Matrix.vecMul (gammaNQV N g) ((gammaNQLam N h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨g0, g1, g2⟩ := g.2.2
  funext j
  fin_cases j <;>
    simp [gammaNQV, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, gammaNQLam_entry,
      Matrix.mul_apply, g0] <;> ring

/-- **`Γ(N) ∩ Q(ℤ)` as a line parabolic group** (the line `⟨e₁⟩`, radical lattice `Nℤ²`, Levi `Γ₂(N)`). -/
def gammaNQLineData : LineData ↥(gammaNQ N) where
  lam := gammaNQLam N
  v := gammaNQV N
  det_one := gammaNQ_det_one N
  v_mul := gammaNQ_v_mul N

omit [NeZero N] in
theorem gammaNQ_lmat (g : ↥(gammaNQ N)) : (gammaNQLineData N).lmat g = realMat g.1 := by
  obtain ⟨g0, g1, g2⟩ := g.2.2
  ext i j
  simp only [LineData.lmat, gammaNQLineData, lineParabolic, realMat_apply]
  fin_cases i <;> fin_cases j <;>
    simp [gammaNQV, gammaNQLam_entry, g0, g1, g2]

omit [NeZero N] in
theorem gammaNQ_lam_mem (g : ↥(gammaNQ N)) : ((gammaNQLineData N).lam g : GL (Fin 2) ℝ) ∈ Lvl1 :=
  ⟨(gammaNQProj N g).1, rfl⟩

/-- The complex coefficient representation of the line parabolic data of `Γ(N) ∩ Q(ℤ)`. -/
def lineNRep (n : ℕ) : Rep ℂ ↥(gammaNQ N) := Rep.of ((gammaNQLineData N).rhoC n)

omit [NeZero N] in
theorem lineNRep_ambient (n : ℕ) (g : ↥(gammaNQ N)) : (lineNRep N n).ρ g = ambRep n g.1 := by
  change (GeneralEisenstein.realCoefficient n) ((gammaNQLineData N).sigma g) = _
  have : (gammaNQLineData N).sigma g = Matrix.SpecialLinearGroup.mapGL (n := Fin 3) (R := ℤ) ℝ g.1 := by
    apply Units.ext
    rw [LineData.sigma_val, gammaNQ_lmat, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    ext i j
    simp [realMat]
  rw [this]
  rfl

omit [NeZero N] in
theorem lineStdRep_ρ (n : ℕ) (g : ↥(gammaNQ N)) : (lineStdRep N n).ρ g = ambRep n g.1 := rfl

omit [NeZero N] in
/-- The geometric coefficient action on `Coef n` is the ambient action. -/
theorem lineNRep_ρ_std (n : ℕ) (g : ↥(gammaNQ N)) (x : Coef n) :
    (lineStdRep N n).ρ g x = (gammaNQLineData N).rhoR n g x := by
  rw [lineStdRep_ρ, ← lineNRep_ambient]
  rfl

end TernaryPeriodPolynomials.Argument.LineSeed
