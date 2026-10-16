module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Seed
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Uniq
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# The full integral line parabolic `Q⁺(ℤ)` as a line parabolic group (Passage 7)

`lineStab = {x ∈ SL₃(ℤ) : first column (1, 0, 0)ᵗ} = ℤ² ⋊ SL₂(ℤ)` contains `Γ(N) ∩ Q(ℤ)`.  `lineStabData : LineData ↥lineStab` is its line parabolic data (Levi block, first row); the line seed
of a level-one cusp form is a closed equivariant form for the whole of `Q⁺(ℤ)`.  `cuspSeedCochain_comap`: if two line parabolic data are compatible along a homomorphism `φ` and the forms have the
same values on `ℍ`, the zig-zag cochains correspond, `c'(x, y) = c(φ x, φ y)` (a closed-form statement, independent of the choice of primitives).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (lineParabolic)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep)
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The Levi block of an element of the line parabolic `Q⁺(ℤ)`, as a homomorphism to `SL₂(ℤ)`. -/
def lineStabLevi : ↥lineStab →* SL(2, ℤ) where
  toFun g := leviBlockQ g.1 g.2
  map_one' := leviBlockQ_one
  map_mul' g h := leviBlockQ_mul g.1 h.1 g.2 h.2

/-- The Levi block of `Q⁺(ℤ)` as a homomorphism to `GL₂(ℝ)`. -/
def lineStabLam : ↥lineStab →* GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ).comp lineStabLevi

/-- The first row `(g₀₁, g₀₂)` of an element of `Q⁺(ℤ)`. -/
def lineStabV (g : ↥lineStab) : Fin 2 → ℝ :=
  ![(((g.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℤ) : ℝ), (((g.1 : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℤ) : ℝ)]

theorem lineStabLam_entry (g : ↥lineStab) (i j : Fin 2) :
    ((lineStabLam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (((g.1 : Matrix (Fin 3) (Fin 3) ℤ) i.succ j.succ : ℤ) : ℝ) := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ (lineStabLevi g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> rfl

theorem lineStab_det_one (g : ↥lineStab) : (lineStabLam g).det = 1 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ (lineStabLevi g)).det = 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have h := (RingHom.map_det (Int.castRingHom ℝ) ((lineStabLevi g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).symm
  rw [Matrix.SpecialLinearGroup.det_coe] at h
  simpa using h

theorem lineStab_v_mul (g h : ↥lineStab) :
    lineStabV (g * h) = lineStabV h +
      Matrix.vecMul (lineStabV g) ((lineStabLam h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨g0, g1, g2⟩ := g.2
  funext j
  fin_cases j <;>
    simp [lineStabV, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, lineStabLam_entry,
      Matrix.mul_apply, g0] <;> ring

/-- **`Q⁺(ℤ) = ℤ² ⋊ SL₂(ℤ)` as a line parabolic group.** -/
def lineStabData : LineData ↥lineStab where
  lam := lineStabLam
  v := lineStabV
  det_one := lineStab_det_one
  v_mul := lineStab_v_mul

theorem lineStab_lmat (g : ↥lineStab) : lineStabData.lmat g = realMat g.1 := by
  obtain ⟨g0, g1, g2⟩ := g.2
  ext i j
  simp only [LineData.lmat, lineStabData, lineParabolic, realMat_apply]
  fin_cases i <;> fin_cases j <;>
    simp [lineStabV, lineStabLam_entry, g0, g1, g2]

theorem lineStab_lam_mem (g : ↥lineStab) : (lineStabData.lam g : GL (Fin 2) ℝ) ∈ Lvl1 :=
  ⟨(lineStabLevi g), rfl⟩

/-- The inclusion `Γ(N) ∩ Q(ℤ) ≤ Q⁺(ℤ)`. -/
def gammaNQToStab (N : ℕ) : ↥(gammaNQ N) →* ↥lineStab := Subgroup.inclusion inf_le_right

/-- The line group `Γ(N) ∩ Q(ℤ)` is a line parabolic subgroup of `Q⁺(ℤ)`: same Levi block. -/
theorem gammaNQ_lam_incl (N : ℕ) (x : ↥(gammaNQ N)) :
    lineStabData.lam (gammaNQToStab N x) = (gammaNQLineData N).lam x := by
  apply Units.ext
  ext i j
  change ((lineStabLam _ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [lineStabLam_entry]
  exact (gammaNQLam_entry N x i j).symm

/-- … and the same radical row. -/
theorem gammaNQ_v_incl (N : ℕ) (x : ↥(gammaNQ N)) :
    lineStabData.v (gammaNQToStab N x) = (gammaNQLineData N).v x := rfl

theorem lmat_comap_eq {G H : Type} [Group G] [Group H] (D : LineData G) (D' : LineData H) (φ : H →* G)
    (hlam : ∀ x, D.lam (φ x) = D'.lam x) (hv : ∀ x, D.v (φ x) = D'.v x) (x : H) :
    D.lmat (φ x) = D'.lmat x := by
  simp only [LineData.lmat, hlam, hv]

theorem mob_I_im_pos {G : Type} [Group G] (D : LineData G) (y : G) : 0 < (mob (D.lam y) Complex.I).im := by
  have hpos : 0 < (D.lam y).det.val := by simp [D.det_one y]
  exact mob_im_pos (D.lam y) hpos (by simp)

/-- **Comparison of the zig-zag cochains of compatible line parabolic data** (closed form; independent of the choice of primitives). -/
theorem cuspSeedCochain_comap {Λ Λ' : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] [Λ'.HasDetOne] {n : ℕ}
    {G H : Type} [Group G] [Group H] (D : LineData G) (D' : LineData H) (φ : H →* G)
    (hlam : ∀ x, D.lam (φ x) = D'.lam x) (hv : ∀ x, D.v (φ x) = D'.v x)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) (hΛ' : ∀ g, (D'.lam g : GL (Fin 2) ℝ) ∈ Λ')
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (f' : CuspForm Λ' ((n + 3 : ℕ) : ℤ))
    (hff : ∀ z : ℂ, 0 < z.im → cuspH Λ n f z = cuspH Λ' n f' z) (x y : H) :
    cuspSeedCochain D' hΛ' (f := f') x y = cuspSeedCochain D hΛ (f := f) (φ x) (φ y) := by
  apply Coef.toPoly_injective
  rw [toPoly_cuspSeedCochain, toPoly_cuspSeedCochain, lmat_comap_eq D D' φ hlam hv x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hv x, hlam y, momentPrim_congr f' f (fun z hz => (hff z hz).symm) j _ (mob_I_im_pos D' y),
    momentPrim_congr f' f (fun z hz => (hff z hz).symm) (j + 1) _ (mob_I_im_pos D' y)]

/-- The antiholomorphic version. -/
theorem cuspSeedConjCochain_comap {Λ Λ' : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] [Λ'.HasDetOne] {n : ℕ}
    {G H : Type} [Group G] [Group H] (D : LineData G) (D' : LineData H) (φ : H →* G)
    (hlam : ∀ x, D.lam (φ x) = D'.lam x) (hv : ∀ x, D.v (φ x) = D'.v x)
    (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ) (hΛ' : ∀ g, (D'.lam g : GL (Fin 2) ℝ) ∈ Λ')
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (f' : CuspForm Λ' ((n + 3 : ℕ) : ℤ))
    (hff : ∀ z : ℂ, 0 < z.im → cuspH Λ n f z = cuspH Λ' n f' z) (x y : H) :
    cuspSeedConjCochain D' hΛ' (f := f') x y = cuspSeedConjCochain D hΛ (f := f) (φ x) (φ y) := by
  rw [cuspSeedConjCochain_eq, cuspSeedConjCochain_eq, cuspSeedCochain_comap D D' φ hlam hv hΛ hΛ' f f' hff]

end TernaryPeriodPolynomials.Argument.LineSeed
