module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.HaarLattice
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.AdelicSection

@[expose] public section


/-!
# (C), step 2: the elements `w₀⁻¹ u(s,t)` of the intertwiner and the congruence lattice `N Ẑ`

Formalized by Claude Sonnet 5.5.
Paper: `ar:eq:intertwiner`.

`gFin σ = w₀⁻¹ u(σ₁, σ₂) ∈ GL₃(𝔸_f)` and `gReal w = w₀⁻¹ u(w₀, w₁) ∈ GL₃(ℝ)` (the repository's `weyl`, `upperUnipotent`).
* `gFin_add_lat`: translating `σ` by `ν ∈ (N Ẑ)²` multiplies `gFin σ` on the right by an element of `K(N)`.
* `adelicSection_gFin_add_lat`: hence the adelic section does not change.
* `gFin_rational`: `gFin (r₀, r₁) = rationalFinite (w₀⁻¹ u(r₀, r₁))` for rational `r`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The finite adele `w₀⁻¹ u(σ₁, σ₂)`. -/
def gFin (σ : FiniteAdeles × FiniteAdeles) : FiniteGL := weyl⁻¹ * upperUnipotent σ.1 σ.2

/-- The real matrix `w₀⁻¹ u(w₀, w₁)`. -/
def gReal (w : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((weyl⁻¹ * upperUnipotent (w 0) (w 1) : GL3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ)

theorem gReal_eq (w : Fin 2 → ℝ) : gReal w = !![0, 1, 0; 0, 0, 1; 1, w 0, w 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gReal, weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem gReal_det (w : Fin 2 → ℝ) : (gReal w).det = 1 := by
  rw [gReal_eq, Matrix.det_fin_three]; simp

theorem map_upperUnipotent {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s t : R) :
    GeneralLinearGroup.map φ (upperUnipotent s t) = upperUnipotent (φ s) (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent, GeneralLinearGroup.map_apply]

theorem gFin_add (σ ν : FiniteAdeles × FiniteAdeles) :
    gFin (σ + ν) = gFin σ * upperUnipotent ν.1 ν.2 := by
  unfold gFin
  rw [mul_assoc, ← lineUnipotent_add]
  rfl

variable (N : ℕ) [NeZero N]

/-- The unipotent of a vector of `(N Ẑ)²` lies in the image of `K(N)`. -/
theorem upper_lat_mem (ν : FiniteAdeles × FiniteAdeles) (h1 : ν.1 ∈ latSet N) (h2 : ν.2 ∈ latSet N) :
    ∃ κ ∈ levelKernel N 3, upperUnipotent ν.1 ν.2 = GeneralLinearGroup.map integralEmbedding κ := by
  obtain ⟨y1, hy1⟩ := (mem_latSet_iff N _).1 h1
  obtain ⟨y2, hy2⟩ := (mem_latSet_iff N _).1 h2
  refine ⟨upperUnipotent ((N : IntegralAdeles) * y1) ((N : IntegralAdeles) * y2), ?_, ?_⟩
  · rw [mem_levelKernel_iff]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent]
  · rw [map_upperUnipotent, map_mul, map_mul, map_natCast, ← hy1, ← hy2]

theorem gFin_add_lat (σ ν : FiniteAdeles × FiniteAdeles) (h1 : ν.1 ∈ latSet N) (h2 : ν.2 ∈ latSet N) :
    ∃ κ ∈ levelKernel N 3, gFin (σ + ν) = gFin σ * GeneralLinearGroup.map integralEmbedding κ := by
  obtain ⟨κ, hκ, e⟩ := upper_lat_mem N ν h1 h2
  exact ⟨κ, hκ, by rw [gFin_add, e]⟩

/-- **The adelic section is constant on the cosets `σ + (N Ẑ)²`.** -/
theorem adelicSection_gFin_add_lat (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (w : Fin 2 → ℝ) (σ ν : FiniteAdeles × FiniteAdeles) (h1 : ν.1 ∈ latSet N) (h2 : ν.2 ∈ latSet N)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) (gReal w) (gFin (σ + ν)) y a b =
      adelicSection N n (hfun f) (gReal w) (gFin σ) y a b := by
  obtain ⟨κ, hκ, e⟩ := gFin_add_lat N σ ν h1 h2
  rw [e]
  exact adelicSection_mul_ker N hN n f (gReal_det w) _ hκ hy a b

theorem gFin_rational (r : ℚ × ℚ) :
    gFin (algebraMap ℚ FiniteAdeles r.1, algebraMap ℚ FiniteAdeles r.2) =
      rationalFinite (weyl⁻¹ * upperUnipotent r.1 r.2 : GL3 ℚ) := by
  unfold gFin rationalFinite
  rw [map_mul, map_inv, map_weyl, map_upperUnipotent]

end TernaryPeriodPolynomials.Argument.FormClassK
