module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Relative
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PivotPoly
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.EdgeComb

@[expose] public section


/-!
# The mixed radical cocycle of the line seed (LS14c)

For a level-one cusp form `f` and `m ∈ SL₂(ℤ)`, the mixed radical cocycle `edgeCyc f m = (r ↦ c(s_m, ·) - c(u_r, s_m))` of the relative seed cocycle of `Λ₁⁺` has the values
(`toPoly_edgeCyc`) `bind₁ ![X 2, X 1, X 0] (∑_j C(b_j (3 r₂ G_{j+1}(μ) + 3 r₁ G_j(μ))) Z^j Y^{n-j})`, `b_j = C(n,j) (-1)^{n-j}`, `μ = m'·i` the Möbius image of the
pivoted Levi block, i.e. only `X, Y` occur (the radical generators kill such polynomials).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 specialToSL2Z)

theorem rho_inl_mono (r : RadicalLattice) (j k : ℕ) :
    rho (linePlusData.lmat (linePlusInl r)) (X 2 ^ j * X 1 ^ k) = X 2 ^ j * X 1 ^ k := by
  have hinv : (linePlusData.lmat (linePlusInl r))⁻¹ = linePlusData.lmat (linePlusInl r)⁻¹ :=
    Matrix.inv_eq_right_inv (by
      rw [← linePlusData.lmat_mul, mul_inv_cancel, linePlusData.lmat_one])
  have hl : linePlusData.lam (linePlusInl r)⁻¹ = 1 := by
    rw [map_inv]
    change (linePlusLam (linePlusInl r))⁻¹ = 1
    rw [linePlusLam_inl, inv_one]
  rw [rho_eq_bind_of_det (linePlusData.det_lmat _), hinv]
  simp only [map_mul, map_pow, bind₁_X_right, Fin.sum_univ_three]
  simp [LineData.lmat, hl, TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineParabolic]

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The moment primitives of `f` (normalized at `i`). -/
abbrev Gf : ℕ → ℂ → ℂ := momentPrim Lvl1 n f

theorem lineSeedChain_section_left (m : SpecialLinearGroup (Fin 2) ℤ) (k : Lam1Plus) :
    lineSeedChain f (linePlusSectionS m) k = 0 := by
  apply Coef.toPoly_injective
  rw [lineSeedChain, TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain]
  have h0 : linePlusData.v (linePlusSectionS m) = 0 := linePlusV_section m
  simp [h0]

/-- The seed cochain with values in `HomogeneousPoly n`. -/
def chainP (g k : Lam1Plus) : HomogeneousPoly n := lineSeedChain f g k

/-- The mixed radical cocycle of the seed. -/
def edgeCyc (m : SpecialLinearGroup (Fin 2) ℤ) : cocycles₁ (lowerRadicalLatticeRep n) :=
  splitEdgeCycle linePlusSplittingS (linePlusRep n) m (lineSeedRelCocycle f)

/-- The values of the mixed radical cocycle, in `HomogeneousPoly n`. -/
def edgeVal (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : HomogeneousPoly n := edgeCyc f m r

theorem edgeCyc_eq_neg (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    edgeVal f m r = -(pivotT n (chainP f (linePlusInl r) (linePlusSectionS m))) := by
  change ((lineSeedRelCocycle f).val.val (linePlusSectionS m, linePlusInl (splitRadicalInput linePlusSplittingS m r)) -
      (lineSeedRelCocycle f).val.val (linePlusInl r, linePlusSectionS m) : linePlusRep n) = _
  have hA : (lineSeedRelCocycle f).val.val
      (linePlusSectionS m, linePlusInl (splitRadicalInput linePlusSplittingS m r)) = (0 : linePlusRep n) := by
    change pivotT n (lineSeedChain f (linePlusSectionS m) _) = 0
    rw [lineSeedChain_section_left]
    exact map_zero _
  have hB : (lineSeedRelCocycle f).val.val (linePlusInl r, linePlusSectionS m) =
      pivotT n (lineSeedChain f (linePlusInl r) (linePlusSectionS m)) := rfl
  rw [hA, hB]
  exact zero_sub _

theorem toPoly_edgeCyc (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    ((edgeVal f m r : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      bind₁ (![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (∑ j ∈ Finset.range (n + 1),
          C ((n.choose j : ℂ) * (-1) ^ (n - j) *
              ((3 * (r.toAdd.2 : ℂ)) * Gf f (j + 1) (mob (linePlusData.lam (linePlusSectionS m)) Complex.I) +
                (3 * (r.toAdd.1 : ℂ)) * Gf f j (mob (linePlusData.lam (linePlusSectionS m)) Complex.I))) *
            (X 2 ^ j * X 1 ^ (n - j))) := by
  rw [edgeCyc_eq_neg, Submodule.coe_neg, toPoly_pivotT, neg_neg]
  congr 1
  have hc := TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain linePlusData linePlus_hΛ
    (f := f) (linePlusInl r) (linePlusSectionS m)
  change Coef.toPoly (cuspSeedCochain linePlusData linePlus_hΛ (f := f) (linePlusInl r) (linePlusSectionS m)) = _ at hc
  have hv : linePlusData.v (linePlusInl r) = ![3 * (r.toAdd.2 : ℝ), 3 * (r.toAdd.1 : ℝ)] := linePlusV_inl r
  change (lineSeedChain f (linePlusInl r) (linePlusSectionS m) : Coef n).toPoly = _
  rw [lineSeedChain, hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rho_inl_mono, hv]
  simp [Gf]

end

end TernaryPeriodPolynomials.Argument.LineSeed
