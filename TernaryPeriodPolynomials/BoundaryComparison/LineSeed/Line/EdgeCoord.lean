module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.EdgeCalc

@[expose] public section


/-!
# The binary coordinate of the mixed radical cocycle of the line seed (LS14d)

`edge_coordinate_line`: the lower-radical coordinate of `edgeCyc f m` is `-3 · Sw(ε_{m'})`, `ε_{m'}` the Eichler cocycle of the moment primitives at the pivoted Levi block
`m' = lam (s_m)` (`epsB`) and `Sw` the swap of the binary variables.  The generators of the lower radical `-3 X_i ∂_Z` kill the values (they do not involve `Z`), so the
averaged pair is the pair of values; its contraction `Y α - X β` is `-3 Sw ε` by `LineEdgeComb.contraction_identity`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses (binarySwap)
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)

attribute [local instance] complexEndRationalAlgebra

/-- An operator that kills `a` has the trivial exponential average on `a`. -/
theorem avg_of_killed {V : Type*} [AddCommGroup V] [Module ℂ V] (op : Module.End ℂ V) (cutoff : ℕ) (a : V)
    (h : op a = 0) : nilpotentExponentialAverage op (cutoff + 1) a = a := by
  unfold nilpotentExponentialAverage
  rw [Finset.sum_range_succ', LinearMap.add_apply, LinearMap.sum_apply]
  have h1 : ∀ i ∈ Finset.range cutoff, (((i + 1 + 1).factorial : ℚ)⁻¹ • op ^ (i + 1)) a = 0 := by
    intro i _
    rw [rationalEnd_smul_apply, pow_succ, Module.End.mul_apply, h, map_zero, smul_zero]
  rw [Finset.sum_eq_zero h1, zero_add, rationalEnd_smul_apply]
  simp

theorem lowerGen_killed (n : ℕ) (a : HomogeneousPoly n) (ha : pderiv (2 : Fin 3) a.1 = 0) (i : Fin 2) :
    lowerRadicalGenerator n i a = 0 := by
  apply Subtype.ext
  change ((-3 : ℂ) • homogeneousShearDerivation n 2 i.castSucc a).1 = 0
  rw [Submodule.coe_smul]
  change (-3 : ℂ) • (X i.castSucc * pderiv 2 a.1) = 0
  rw [ha, mul_zero, smul_zero]

theorem avgSymm_of_killed (n : ℕ) (a : HomogeneousPoly n) (ha : pderiv (2 : Fin 3) a.1 = 0) (i : Fin 2) :
    (lowerRadicalAverageEquiv n i).symm a = a := by
  rw [LinearEquiv.symm_apply_eq]
  exact (avg_of_killed _ n a (lowerGen_killed n a ha i)).symm

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The binary form underlying the value of the mixed radical cocycle at `r`. -/
def edgeBin (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    C ((n.choose j : ℂ) * (-1) ^ (n - j) *
        ((3 * (r.toAdd.2 : ℂ)) * Gf f (j + 1) (mob (linePlusData.lam (linePlusSectionS m)) Complex.I) +
          (3 * (r.toAdd.1 : ℂ)) * Gf f j (mob (linePlusData.lam (linePlusSectionS m)) Complex.I))) *
      (X 0 ^ j * X 1 ^ (n - j))

theorem edgeCyc_lift (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    ((edgeVal f m r : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      binaryPolynomialLift (edgeBin f m r) := by
  rw [toPoly_edgeCyc]
  simp only [edgeBin, map_sum, map_mul, bind₁_C_right, map_pow, bind₁_X_right, binaryPolynomialLift,
    rename_C, rename_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- The Eichler cocycle of the moment primitives at the pivoted Levi block of `s_m`, as a binary form of degree `n + 1`. -/
def epsB (m : SpecialLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  ⟨eichlerCocycle n (Gf f) (linePlusData.lam (linePlusSectionS m)),
    (mem_homogeneousSubmodule _ _).mpr (eichlerCocycle_isHomogeneous n _ _)⟩

theorem edgeBin_gen (m : SpecialLinearGroup (Fin 2) ℤ) :
    edgeBin f m radicalLatticeFirst = combSum n (fun j => C (3 * Gf f j (mob (linePlusData.lam (linePlusSectionS m)) Complex.I)))
        (X 0) (X 1) ∧
    edgeBin f m radicalLatticeSecond = combSum n (fun j => C (3 * Gf f (j + 1) (mob (linePlusData.lam (linePlusSectionS m)) Complex.I)))
        (X 0) (X 1) := by
  constructor
  · unfold edgeBin combSum
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [radicalLatticeFirst]
    ring
  · unfold edgeBin combSum
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [radicalLatticeSecond]
    ring

theorem swap_epsB (m : SpecialLinearGroup (Fin 2) ℤ) :
    (binarySwap n (epsB f m)).val =
      combSum (n + 1) (fun j => C (Gf f j (mob (linePlusData.lam (linePlusSectionS m)) Complex.I))) (X 0) (X 1) := by
  change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (eichlerPoly n (Gf f) (mob (linePlusData.lam (linePlusSectionS m)) Complex.I)) = _
  unfold eichlerPoly combSum
  simp only [map_sum, map_mul, rename_C, map_pow, rename_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem contraction_edgeBin (m : SpecialLinearGroup (Fin 2) ℤ) :
    X 1 * edgeBin f m radicalLatticeFirst - X 0 * edgeBin f m radicalLatticeSecond =
      ((-3 : ℂ) • binarySwap n (epsB f m)).val := by
  rw [(edgeBin_gen f m).1, (edgeBin_gen f m).2,
    contraction_identity n (fun j => C (3 * Gf f j (mob (linePlusData.lam (linePlusSectionS m)) Complex.I))) (X 0) (X 1)]
  change _ = (-3 : ℂ) • (binarySwap n (epsB f m)).val
  rw [swap_epsB, smul_eq_C_mul]
  unfold combSum
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_neg, map_ofNat]
  ring

theorem coordinate_of_bin (c : cocycles₁ (lowerRadicalLatticeRep n)) (b₁ b₂ : MvPolynomial (Fin 2) ℂ)
    (h₁ : ((show HomogeneousPoly n from c radicalLatticeFirst) : MvPolynomial (Fin 3) ℂ) = binaryPolynomialLift b₁)
    (h₂ : ((show HomogeneousPoly n from c radicalLatticeSecond) : MvPolynomial (Fin 3) ℂ) = binaryPolynomialLift b₂) :
    (lowerRadicalCocycleCoordinate n c).val = X 1 * b₁ - X 0 * b₂ := by
  rw [lowerRadicalCocycleCoordinate_value]
  have hpair : ∀ i : Fin 2, (lowerRadicalAverageEquiv n i).symm (c (radicalLatticeGenerator i)) =
      c (radicalLatticeGenerator i) := fun i => by
    apply avgSymm_of_killed
    change pderiv 2 ((show HomogeneousPoly n from c (radicalLatticeGenerator i)) : MvPolynomial (Fin 3) ℂ) = 0
    have g0 : radicalLatticeGenerator 0 = radicalLatticeFirst := by simp [radicalLatticeGenerator]
    have g1 : radicalLatticeGenerator 1 = radicalLatticeSecond := by simp [radicalLatticeGenerator]
    fin_cases i
    · change pderiv 2 ((show HomogeneousPoly n from c (radicalLatticeGenerator 0)) : MvPolynomial (Fin 3) ℂ) = 0
      rw [g0, h₁]; exact binaryPolynomialLift_pderiv_third _
    · change pderiv 2 ((show HomogeneousPoly n from c (radicalLatticeGenerator 1)) : MvPolynomial (Fin 3) ℂ) = 0
      rw [g1, h₂]; exact binaryPolynomialLift_pderiv_third _
  simp only [hpair]
  change binaryPolynomialRestrict (lowerRadicalContraction
      ((show HomogeneousPoly n from c (radicalLatticeGenerator 0)) : MvPolynomial (Fin 3) ℂ)
      ((show HomogeneousPoly n from c (radicalLatticeGenerator 1)) : MvPolynomial (Fin 3) ℂ)) = _
  have g0 : radicalLatticeGenerator 0 = radicalLatticeFirst := by simp [radicalLatticeGenerator]
  have g1 : radicalLatticeGenerator 1 = radicalLatticeSecond := by simp [radicalLatticeGenerator]
  rw [g0, g1, h₁, h₂]
  have hlift : lowerRadicalContraction (binaryPolynomialLift b₁) (binaryPolynomialLift b₂) =
      binaryPolynomialLift (X 1 * b₁ - X 0 * b₂) := by
    unfold lowerRadicalContraction
    simp [binaryPolynomialLift]
  rw [hlift, binaryPolynomialRestrict_lift]

/-- **The binary coordinate of the mixed radical cocycle of the line seed**: `-3 · Sw(ε_{m'})`. -/
theorem edge_coordinate_line (m : SpecialLinearGroup (Fin 2) ℤ) :
    lowerRadicalCocycleCoordinate n (edgeCyc f m) = (-3 : ℂ) • binarySwap n (epsB f m) := by
  apply Subtype.ext
  rw [coordinate_of_bin (edgeCyc f m) _ _ (edgeCyc_lift f m radicalLatticeFirst) (edgeCyc_lift f m radicalLatticeSecond),
    contraction_edgeBin]

end

end TernaryPeriodPolynomials.Argument.LineSeed
