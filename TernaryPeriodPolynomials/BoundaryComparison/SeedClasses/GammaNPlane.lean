module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneOfSubgroup
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Instance

@[expose] public section


/-!
# Lemma C.3 for the paper's principal congruence level: `Γ_P = Γ(N) ∩ P(ℤ)`

Paper: Lemma C.3 (`ar:lem:seed`),: `Γ_P = Γ ∩ P(ℚ)`, `Λ_P` its projection onto the determinant-one Levi,
`h ∈ S_k(Λ_P)`. The carrier `gammaNP N` is `Γ(N) ∩ P(ℤ)` (bottom row `(0, 0, 1)`); it equals the
rational-plane stabilizer `Γ(N) ∩ P(ℚ)` only for `N ≥ 3` (`ConvergenceC4.gammaN_inf_rationalPlane`);
for `N = 1, 2` it can be strictly smaller (`diag(-1, 1, -1) ∈ Γ(2)` stabilizes the plane but has
bottom-right entry `-1`).

`PlaneData.ofHom` makes any group with a representation `σ` into determinant-one matrices
`[[λ, w], [0, 1]]` a plane parabolic group. For `Γ = Γ(N) ⊂ SL₃(ℤ)` (`ConvergenceC4.gammaN`,
`3 ∣ N` not needed here) the plane group `Γ_P = Γ(N) ∩ P(ℤ)` (`gammaNP`) is such a group
(`gammaNPlaneData`), its coefficient matrix is the real matrix of the element
(`gammaNPlaneData_plm`, so `ρ` is `SeedC3.rho (realMat γ)`, the action of the convergence theorem),
and its Levi block lies in `Λ_P = Γ₂(N)` (`gammaNPlaneData_lam_mem`, from `leviIn_gammaN`).
Hence the whole zig-zag construction for the seed of `h ∈ S_{n+3}(Γ₂(N))` (`cuspSeedClass`,
`toPoly_cuspSeedCochain`, the antiholomorphic seed) applies to `Γ_P`. All plane cusps of `Γ(N)` are
`SL₃(ℤ)`-conjugate to the standard one and `Γ(N)` is normal, so conjugation gives no further groups.

Formalized by Claude Sonnet 5.5.
-/

open Matrix
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- **A plane parabolic group from a representation.** A group `G` with a homomorphism
`σ : G → GL₃(ℝ)` into determinant-one matrices `[[λ, w], [0, 1]]` is a `PlaneData`. -/
def PlaneData.ofHom {G : Type} [Group G] (σ : G →* GL (Fin 3) ℝ)
    (hshape : ∀ g, IsPlaneShape (σ g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g, (σ g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) : PlaneData G where
  lam :=
    { toFun := fun g => Matrix.GeneralLinearGroup.mkOfDetNeZero (blockA (σ g : Matrix _ _ ℝ)) (by
        rw [det_blockA (hshape g), hdet g]; exact one_ne_zero)
      map_one' := by
        apply Units.ext
        change blockA ((σ 1 : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1
        rw [map_one]
        exact blockA_one
      map_mul' := fun g h => by
        apply Units.ext
        change blockA ((σ (g * h) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
          blockA (σ g : Matrix _ _ ℝ) * blockA (σ h : Matrix _ _ ℝ)
        rw [map_mul]
        exact blockA_mul (hshape g) (hshape h) }
  w := fun g => blockW (σ g : Matrix _ _ ℝ)
  det_one := fun g => by
    apply Units.ext
    change (blockA (σ g : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
    rw [det_blockA (hshape g), hdet g]
  w_mul := fun g h => by
    show blockW ((σ (g * h) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = _
    rw [map_mul]
    exact blockW_mul (hshape g) (hshape h)

theorem PlaneData.ofHom_plm {G : Type} [Group G] (σ : G →* GL (Fin 3) ℝ)
    (hshape : ∀ g, IsPlaneShape (σ g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g, (σ g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (g : G) :
    (PlaneData.ofHom σ hshape hdet).plm g = (σ g : Matrix (Fin 3) (Fin 3) ℝ) :=
  (eq_parabolicMatrix (hshape g)).symm

/-! ### The paper's plane group `Γ_P = Γ(N) ∩ P(ℤ)` -/

/-- The plane group `Γ_P = Γ(N) ∩ P(ℤ)`: the elements of `Γ(N)` with bottom row `(0, 0, 1)`. -/
def gammaNP (N : ℕ) : Subgroup SL(3, ℤ) := gammaN N ⊓ planeStab

/-- The real matrix representation of `Γ_P`. -/
def gammaNSigma (N : ℕ) : ↥(gammaNP N) →* GL (Fin 3) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp (gammaNP N).subtype

theorem gammaNSigma_val (N : ℕ) (g : ↥(gammaNP N)) :
    ((gammaNSigma N g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = realMat g.1 := by
  rw [show ((gammaNSigma N g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
    (Matrix.SpecialLinearGroup.mapGL ℝ g.1 : GL (Fin 3) ℝ) from rfl,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  simp [realMat]

theorem gammaNSigma_shape (N : ℕ) (g : ↥(gammaNP N)) :
    IsPlaneShape ((gammaNSigma N g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨h0, h1, h2⟩ := g.2.2
  rw [gammaNSigma_val]
  refine ⟨?_, ?_, ?_⟩ <;> simp [realMat_apply, h0, h1, h2]

/-- **`Γ_P = Γ(N) ∩ P(ℤ)` as a plane parabolic group.** -/
def gammaNPlaneData (N : ℕ) : PlaneData ↥(gammaNP N) :=
  PlaneData.ofHom (gammaNSigma N) (gammaNSigma_shape N) (fun g => by
    rw [gammaNSigma_val]; exact det_realMat g.1)

/-- The coefficient matrix `[[λ, w], [0, 1]]` of an element of `Γ_P` is its real matrix. -/
theorem gammaNPlaneData_plm (N : ℕ) (g : ↥(gammaNP N)) :
    (gammaNPlaneData N).plm g = realMat g.1 := by
  rw [gammaNPlaneData, PlaneData.ofHom_plm, gammaNSigma_val]

/-- **The Levi block of `Γ_P` lies in `Λ_P = Γ₂(N)`.** -/
theorem gammaNPlaneData_lam_mem (N : ℕ) (g : ↥(gammaNP N)) :
    ((gammaNPlaneData N).lam g : GL (Fin 2) ℝ) ∈ leviGroup N := by
  obtain ⟨g', hg', he⟩ := leviIn_gammaN N g.1 g.2.1 g.2.2
  have : (gammaNPlaneData N).lam g = g' := by
    apply Units.ext
    rw [he]
    change blockA ((gammaNSigma N g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = _
    rw [gammaNSigma_val]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [this]
  exact hg'

end TernaryPeriodPolynomials.Argument.SeedC3
