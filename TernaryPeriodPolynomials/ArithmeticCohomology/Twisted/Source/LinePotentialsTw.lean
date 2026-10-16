module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineDetectTwEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineTwCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CohomologyCoordinates

@[expose] public section


/-!
# The potentials of the line source at the good-line reflection

For the odd character `χ` of conductor three the line source at the adelic point
`rationalGroup rationalGoodLine⁻¹` is the cup product of two potentials (`linePot_cup`).  With the real
permutation matrix `W = lpW` of the good line (the swap of the indices `0` and `2`), the Iwasawa
factor of `W x` in the line parabolic and the swap `Sw` of the two binary variables (which
intertwines the line Levi block `A = σ m σ` with the arithmetic Levi block `m`), they are

* `a x = Sw (α(iwAL(W x)) 1)`,
* `l x Q = ρ_χ(W) (R(iwL(W x)) (Sw Q))`,
* `lam r Q = ρ_χ(W) (R(u(3b, 3a)) (Sw Q))`  for `r = (a, b)`,

where `α` is the untwisted Levi cocycle of `LeviCocycleData` (for odd `χ` the sign of `lineStar` is
the sign of the corner alone), `R` is the radical cocycle of the real line parabolic and `u(s, t)` is
the line unipotent.  They form a `LineCupDataTw` (`lineCupDataTw`): the Levi potential does not see
the lower radical lattice (`linePotA_radical`), `l` satisfies the cocycle law along it
(`linePotL_radical`, since `W` conjugates the lower unipotent `(3a, 3b)` to `u(3b, 3a)`), and `lam`
is free of `x₂` (`lp_pderiv_two_linePotLam`: the conjugation by `W` moves the variables of the
radical to `x₀`, `x₁`).  In these coordinates `lam (1,0) Q = 3 ∂₁Q`, `lam (0,1) Q = -3 ∂₀Q`, so the
lower radical coordinate is `3 (n+1) Q` by Euler's identity (`lowerKostant_lineCupData`).  The Levi
side is `a (s m) - a 1 = Sw (α(σ m σ) 1)` (`lineCupDataTw_levi`), where `σ m σ` is the pivot
conjugate.

The class of this Levi cocycle in `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is the transport of the class of the
period cocycle `m ↦ α(m) 1` along the automorphism `m ↦ σ m σ` of `GL₂(ℤ)` and the equivariant
map `Sw` (`lineCocycleOf`), hence is nonzero as soon as the period class is
(`exists_lineLeviCocycle_ne_zero`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice arithmeticBinaryRep goodLineLeviSection goodLineRadicalInclusion
    rationalGoodLine lowerRadicalCoordinate lowerRadicalContraction radicalLatticeGenerator
    radicalLatticeFirst radicalLatticeSecond
    binaryPivotSwap binaryPivotSwap_map binaryPolynomialLift binaryPolynomialRestrict
    binaryPolynomialRestrict_lift binaryPolynomialRestrict_X binaryPolynomialLift_pderiv_third)
open TernaryPeriodPolynomials.AnalyticClasses
  (binarySwap pivotConjugate binarySwap_binaryCoefficient)

namespace TernaryPeriodPolynomials.TwistedSource

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The permutation matrix of the good line -/

section Permutation

/-- The real permutation matrix of the good line. -/
def lpW : RealGL3 := ratReal rationalGoodLine

theorem lpW_val : lpW.val = !![(0 : ℝ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpW, rationalGoodLine, GeneralLinearGroup.map_apply]

theorem lpW_mul_self : lpW * lpW = 1 := by
  apply Units.ext
  rw [Units.val_mul, lpW_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem lpW_inv : lpW⁻¹ = lpW := inv_eq_of_mul_eq_one_right lpW_mul_self

theorem lpW_orth : IsOrthogonalReal lpW := by
  unfold IsOrthogonalReal
  rw [lpW_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The Iwasawa factor of the permutation matrix is trivial. -/
theorem lpW_iwL : iwL lpW = 1 := by
  apply Subtype.ext
  have h := iwasawaB_mul_orth (1 : RealGL3) lpW_orth
  rw [one_mul, iwasawaB_one] at h
  exact h

theorem lpW_iwAL : iwAL lpW = 1 := by
  unfold iwAL
  rw [lpW_iwL]
  exact lineLeviBlockHom.map_one

theorem lp_ratReal_one : ratReal (1 : RationalGL3) = 1 := map_one _

theorem lp_alpha_one {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) (x : BinaryAdelicGL) :
    E.α 1 x = 0 :=
  E.orth 1 (by simp) x

theorem lp_alpha_iwAL_lpW {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) :
    E.α (iwAL lpW) = fun _ => 0 := by
  rw [lpW_iwAL]
  exact funext (lp_alpha_one E)

/-- The Levi cocycle along the Iwasawa factor of `p W`: only the block of `p` remains. -/
theorem lp_alpha_iwAL_mul {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (p : lineParabolic ℝ) : E.α (iwAL (p.1 * lpW)) 1 = E.α (lineLeviBlock p) 1 := by
  rw [alpha_iwAL_mul E p lpW 1, lp_alpha_iwAL_lpW]
  simp [binaryCohomologicalAction]

theorem lp_rename_swap_rename_swap (P : Binary.Poly) :
    rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) P) = P := by
  rw [rename_rename]
  have h : ((Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) ∘ (Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2))
      = id := by
    funext i
    exact Equiv.swap_apply_self _ _ _
  rw [h, rename_id]
  rfl

theorem lp_rho_mul_apply (χ : RankOneCharacter) (g h : RealGL3) (v : HomogeneousPoly n) :
    realCoefficientComponent n χ (g * h) v =
      realCoefficientComponent n χ g (realCoefficientComponent n χ h v) := by
  rw [map_mul, Module.End.mul_apply]

end Permutation

/-! ## Line elements attached to the radical lattice and to Levi blocks -/

section Elements

/-- The line Levi element with trivial corner and block `A`. -/
def lpLevi (A : BinaryRealGL) : lineParabolic ℝ := ⟨lineLevi 1 A, lineLevi_mem 1 A⟩

/-- The line unipotent of the real line parabolic. -/
def lpUnipotent (s t : ℝ) : lineParabolic ℝ := ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩

/-- The line unipotent `u(3b, 3a)` conjugate under `W` to the lower unipotent of the lattice point
`(a, b)`. -/
def lpUnip (r : RadicalLattice) : lineParabolic ℝ :=
  lpUnipotent (3 * ((r.toAdd.2 : ℤ) : ℝ)) (3 * ((r.toAdd.1 : ℤ) : ℝ))

theorem lpLevi_block (A : BinaryRealGL) : lineLeviBlock (lpLevi A) = A :=
  lineLeviBlock_levi 1 A

theorem lpUnipotent_block (s t : ℝ) : lineLeviBlock (lpUnipotent s t) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLeviBlock, lrBlockP, lrLowerBlock, lpUnipotent, lineUnipotent, upperUnipotent]

theorem lpUnip_block (r : RadicalLattice) : lineLeviBlock (lpUnip r) = 1 :=
  lpUnipotent_block _ _

theorem lp_componentCharacter_upper (χ : RankOneCharacter) (s t : ℝ) :
    componentCharacter χ (upperUnipotent s t) = 1 := by
  have hdet : GeneralLinearGroup.det (upperUnipotent s t) = 1 := by
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, upperUnipotent, Matrix.det_fin_three]
  simp [componentCharacter, hdet]

/-- The Levi action `lineStar` is trivial on the line unipotent. -/
theorem lpUnipotent_star (χ : RankOneCharacter) (k : ℕ) (s t : ℝ) (Q : Binary.HomogeneousPoly k) :
    lineStar χ k (lpUnipotent s t) Q = Q := by
  have hθ : lineTheta χ (lpUnipotent s t) = 1 := by
    rw [lineTheta_apply, lpUnipotent_block]
    have h00 : (lpUnipotent s t).1.val 0 0 = 1 := rfl
    have hc : componentCharacter χ (lpUnipotent s t).1 = 1 :=
      lp_componentCharacter_upper χ s t
    rw [hc, h00]
    simp
  rw [lineStar_apply, hθ, lpUnipotent_block]
  simp

theorem lpUnipotent_star_inv (χ : RankOneCharacter) (k : ℕ) (s t : ℝ)
    (Q : Binary.HomogeneousPoly k) : lineStar χ k (lpUnipotent s t)⁻¹ Q = Q := by
  have h := lineStar_inv_cancel χ k (lpUnipotent s t) Q
  rwa [lpUnipotent_star] at h

theorem lpW_mul_lower (x y : ℝ) :
    lpW * lowerPlaneUnipotent x y = upperUnipotent y x * lpW := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lpW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerPlaneUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem lpW_mul_upper (s t : ℝ) :
    lpW * upperUnipotent s t = lowerPlaneUnipotent t s * lpW := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lpW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerPlaneUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem lp_ratReal_radical (r : RadicalLattice) :
    ratReal (goodLineRadicalInclusion r).val =
      lowerPlaneUnipotent (3 * ((r.toAdd.1 : ℤ) : ℝ)) (3 * ((r.toAdd.2 : ℤ) : ℝ)) := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (lowerPlaneUnipotent (3 * ((r.toAdd.1 : ℤ) : ℚ)) (3 * ((r.toAdd.2 : ℤ) : ℚ))) = _
  rw [TernaryPeriodPolynomials.SphericalDetection.Helpers.map_lowerPlaneUnipotent]
  simp

/-- Conjugation by `W`: the lower unipotent `(3a, 3b)` becomes the line unipotent `u(3b, 3a)`. -/
theorem lpW_mul_radical (r : RadicalLattice) :
    lpW * ratReal (goodLineRadicalInclusion r).val = (lpUnip r).1 * lpW := by
  rw [lp_ratReal_radical]
  exact lpW_mul_lower (3 * ((r.toAdd.1 : ℤ) : ℝ)) (3 * ((r.toAdd.2 : ℤ) : ℝ))

theorem lpW_mul_radical' (r : RadicalLattice) :
    lpW * (lpUnip r).1 = ratReal (goodLineRadicalInclusion r).val * lpW := by
  rw [lp_ratReal_radical]
  exact lpW_mul_upper (3 * ((r.toAdd.2 : ℤ) : ℝ)) (3 * ((r.toAdd.1 : ℤ) : ℝ))

theorem lp_ratReal_levi (m : GeneralLinearGroup (Fin 2) ℤ) :
    ratReal (goodLineLeviSection m).val =
      planeLevi (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi m 1)) = _
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

/-- Conjugation by `W`: the Levi element `diag(m, 1)` becomes the line Levi element with block the
pivot conjugate of `m`. -/
theorem lpW_mul_levi (m : GeneralLinearGroup (Fin 2) ℤ) :
    lpW * ratReal (goodLineLeviSection m).val =
      (lpLevi (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m))).1 * lpW := by
  rw [lp_ratReal_levi]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lpW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpLevi, lineLevi_val, pivotConjugate, binaryPivotSwap, planeLevi, planeBlock,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      GeneralLinearGroup.map_apply]

end Elements

/-! ## The potentials -/

section Potentials

variable {σ : CuspidalRepresentation}

/-- **The Levi potential of the line source at the good-line reflection.** -/
def linePotA (E : LeviCocycleData σ n) (x : RationalGL3) : Binary.HomogeneousPoly (n + 1) :=
  binarySwap n (E.α (iwAL (lpW * ratReal x)) 1)

/-- **The radical potential of the line source at the good-line reflection.** -/
def linePotL (n : ℕ) (χ : RankOneCharacter) (x : RationalGL3) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  realCoefficientComponent n χ lpW ∘ₗ lineRadical n χ (iwL (lpW * ratReal x)) ∘ₗ binarySwap n

/-- **The radical cocycle on the lower radical lattice.** -/
def linePotLam (n : ℕ) (χ : RankOneCharacter) (r : RadicalLattice) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  realCoefficientComponent n χ lpW ∘ₗ lineRadical n χ (lpUnip r) ∘ₗ binarySwap n

theorem lp_binarySwap_binarySwap (Q : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (binarySwap n Q) = Q :=
  Subtype.ext (lp_rename_swap_rename_swap Q.val)

theorem linePotA_one (E : LeviCocycleData σ n) : linePotA E 1 = 0 := by
  unfold linePotA
  rw [lp_ratReal_one, mul_one, lpW_iwAL, lp_alpha_one, map_zero]

theorem linePotA_radical (E : LeviCocycleData σ n) (r : RadicalLattice) :
    linePotA E (goodLineRadicalInclusion r).val = linePotA E 1 := by
  rw [linePotA_one]
  unfold linePotA
  rw [lpW_mul_radical r, lp_alpha_iwAL_mul, lpUnip_block, lp_alpha_one, map_zero]

/-- **The Levi side of the potential**: `a (s m) - a 1 = Sw (α(σ m σ) 1)`. -/
theorem linePotA_levi (E : LeviCocycleData σ n) (m : GeneralLinearGroup (Fin 2) ℤ) :
    linePotA E (goodLineLeviSection m).val - linePotA E 1 =
      binarySwap n
        (E.α (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m)) 1) := by
  rw [linePotA_one, sub_zero]
  unfold linePotA
  rw [lpW_mul_levi, lp_alpha_iwAL_mul, lpLevi_block]

/-- **The cocycle law of the radical potential along the lower radical lattice.** -/
theorem linePotL_radical (χ : RankOneCharacter) (r : RadicalLattice) (g : RationalGL3)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    linePotL n χ ((goodLineRadicalInclusion r).val * g) Q =
      linePotLam n χ r Q +
        realCoefficientComponent n χ (ratReal (goodLineRadicalInclusion r).val)
          (linePotL n χ g Q) := by
  have hm : lpW * ratReal ((goodLineRadicalInclusion r).val * g) =
      (lpUnip r).1 * (lpW * ratReal g) := by
    rw [map_mul, ← mul_assoc, lpW_mul_radical, mul_assoc]
  have hcomm : ∀ X : HomogeneousPoly n,
      realCoefficientComponent n χ lpW (realCoefficientComponent n χ (lpUnip r).1 X) =
        realCoefficientComponent n χ (ratReal (goodLineRadicalInclusion r).val)
          (realCoefficientComponent n χ lpW X) := by
    intro X
    calc realCoefficientComponent n χ lpW (realCoefficientComponent n χ (lpUnip r).1 X)
        = realCoefficientComponent n χ (lpW * (lpUnip r).1) X :=
          (lp_rho_mul_apply χ _ _ X).symm
      _ = realCoefficientComponent n χ (ratReal (goodLineRadicalInclusion r).val * lpW) X := by
          rw [lpW_mul_radical']
      _ = realCoefficientComponent n χ (ratReal (goodLineRadicalInclusion r).val)
            (realCoefficientComponent n χ lpW X) := lp_rho_mul_apply χ _ _ X
  have hstar : lineStar χ (n + 1) (lpUnip r)⁻¹ (binarySwap n Q) = binarySwap n Q :=
    lpUnipotent_star_inv χ (n + 1) _ _ _
  simp only [linePotL, linePotLam, LinearMap.comp_apply]
  rw [hm, lineRadical_iwL_mul χ (lpUnip r) (lpW * ratReal g) (binarySwap n Q), hstar, map_add,
    hcomm]

end Potentials

/-! ## The cup product of the potentials is the line source at the reflection -/

section Cup

variable {σ : CuspidalRepresentation}

/-- **The line source at the good-line reflection is the cup product of the potentials**: the right
hand side is the expression of `lineSourceTw_w` at the vertices `ratReal ∘ x`. -/
theorem linePot_cup (E : LeviCocycleData σ n) (χ : RankOneCharacter) (x : Fin 3 → RationalGL3) :
    (linePotL n χ (x 2) - linePotL n χ (x 1)) (linePotA E (x 1) - linePotA E (x 0)) =
      realCoefficientComponent n χ (ratReal rationalGoodLine)⁻¹
        ((lineRadical n χ (iwL (ratReal rationalGoodLine * ratReal (x 2))) -
            lineRadical n χ (iwL (ratReal rationalGoodLine * ratReal (x 1))))
          (E.α (iwAL (ratReal rationalGoodLine * ratReal (x 1))) 1 -
            E.α (iwAL (ratReal rationalGoodLine * ratReal (x 0))) 1)) := by
  show _ = realCoefficientComponent n χ lpW⁻¹
    ((lineRadical n χ (iwL (lpW * ratReal (x 2))) - lineRadical n χ (iwL (lpW * ratReal (x 1))))
      (E.α (iwAL (lpW * ratReal (x 1))) 1 - E.α (iwAL (lpW * ratReal (x 0))) 1))
  simp only [LinearMap.sub_apply, linePotL, linePotA, LinearMap.comp_apply, map_sub,
    lp_binarySwap_binarySwap, lpW_inv]

end Cup

/-! ## The radical cocycle: explicit form, freedom and the Kostant law -/

section Kostant

theorem lp_complex_val :
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) lpW).val = !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lpW_val, GeneralLinearGroup.map_apply]

theorem lp_inv_val :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) lpW)⁻¹ : GL3).val =
      !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  have h : (GeneralLinearGroup.map (algebraMap ℝ ℂ) lpW)⁻¹ =
      GeneralLinearGroup.map (algebraMap ℝ ℂ) lpW := by
    have h1 := map_inv
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) :
        GeneralLinearGroup (Fin 3) ℝ →* GeneralLinearGroup (Fin 3) ℂ) lpW
    rw [lpW_inv] at h1
    exact h1.symm
  rw [h]
  exact lp_complex_val

theorem lp_det_complex :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) lpW) : ℂˣ) : ℂ) = -1 := by
  rw [GeneralLinearGroup.val_det_apply, lp_complex_val]
  simp [Matrix.det_fin_three]

theorem lp_componentCharacter (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) : componentCharacter χ lpW = -1 := by
  have hd : ((GeneralLinearGroup.det lpW : ℝˣ) : ℝ) = -1 := by
    rw [GeneralLinearGroup.val_det_apply, lpW_val]
    simp [Matrix.det_fin_three]
  have hneg : ¬ ((0 : ℝ) < -1) := by norm_num
  have h := chi_real_signL χ hodd (GeneralLinearGroup.det lpW)
  rw [hd, ite_eq_right hneg] at h
  exact h

/-- Substitution by the permutation matrix on forms free of `x₀`. -/
theorem lp_substitute_rename_succ (N : Matrix (Fin 3) (Fin 3) ℂ)
    (hN : N = !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0]) (G : Binary.Poly) :
    substitute N (rename (Fin.succ : Fin 2 → Fin 3) G) =
      binaryPolynomialLift (rename (Equiv.swap (0 : Fin 2) 1) G) := by
  subst hN
  have key : (substitute !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0]).comp
      (rename (Fin.succ : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly) =
      binaryPolynomialLift.comp
        (rename (Equiv.swap (0 : Fin 2) 1) : Binary.Poly →ₐ[ℂ] Binary.Poly) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [substitute, linearForm, Fin.sum_univ_three, binaryPolynomialLift]
    · simp [substitute, linearForm, Fin.sum_univ_three, binaryPolynomialLift]
  exact AlgHom.congr_fun key G

theorem lp_pderiv_zero_rename_swap (P : Binary.Poly) :
    pderiv (0 : Fin 2) (rename (Equiv.swap (0 : Fin 2) 1) P) =
      rename (Equiv.swap (0 : Fin 2) 1) (pderiv (1 : Fin 2) P) := by
  have h := pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) P
  rwa [Equiv.swap_apply_right] at h

theorem lp_pderiv_one_rename_swap (P : Binary.Poly) :
    pderiv (1 : Fin 2) (rename (Equiv.swap (0 : Fin 2) 1) P) =
      rename (Equiv.swap (0 : Fin 2) 1) (pderiv (0 : Fin 2) P) := by
  have h := pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) P
  rwa [Equiv.swap_apply_left] at h

theorem lp_coe_lineRadical_unip (χ : RankOneCharacter) (r : RadicalLattice)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    ((lineRadical n χ (lpUnip r) Q : HomogeneousPoly n) : Poly) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (C (algebraMap ℝ ℂ (3 * ((r.toAdd.1 : ℤ) : ℝ))) * pderiv (0 : Fin 2) (Q : Binary.Poly) -
          C (algebraMap ℝ ℂ (3 * ((r.toAdd.2 : ℤ) : ℝ))) * pderiv (1 : Fin 2) (Q : Binary.Poly)) :=
  coe_lineRadical_unipotent n χ (3 * ((r.toAdd.2 : ℤ) : ℝ)) (3 * ((r.toAdd.1 : ℤ) : ℝ)) Q

/-- **The explicit form of the radical cocycle**: the conjugation by `W` turns the radical at the
line unipotent into a form in `x₀`, `x₁` only. -/
theorem lp_coe_linePotLam (χ : RankOneCharacter) (r : RadicalLattice)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    ((linePotLam n χ r Q : HomogeneousPoly n) : Poly) =
      (componentCharacter χ lpW * ((-1 : ℂ))⁻¹) •
        binaryPolynomialLift
          (C (algebraMap ℝ ℂ (3 * ((r.toAdd.1 : ℤ) : ℝ))) * pderiv (1 : Fin 2) (Q : Binary.Poly) -
            C (algebraMap ℝ ℂ (3 * ((r.toAdd.2 : ℤ) : ℝ))) *
              pderiv (0 : Fin 2) (Q : Binary.Poly)) := by
  have h1 : ((linePotLam n χ r Q : HomogeneousPoly n) : Poly) =
      fullCoefficientComponent χ lpW
        ((lineRadical n χ (lpUnip r) (binarySwap n Q) : HomogeneousPoly n) : Poly) := rfl
  have hsw : ((binarySwap n Q : Binary.HomogeneousPoly (n + 1)) : Binary.Poly) =
      rename (Equiv.swap (0 : Fin 2) 1) (Q : Binary.Poly) := rfl
  rw [h1, fullCoefficientComponent_apply, lp_det_complex, lp_coe_lineRadical_unip,
    lp_substitute_rename_succ _ lp_inv_val]
  refine congrArg (fun z => (componentCharacter χ lpW * ((-1 : ℂ))⁻¹) • binaryPolynomialLift z) ?_
  rw [hsw]
  simp only [map_sub, map_mul, rename_C, lp_pderiv_zero_rename_swap, lp_pderiv_one_rename_swap,
    lp_rename_swap_rename_swap]

/-- **The radical cocycle is free of `x₂`.** -/
theorem lp_pderiv_two_linePotLam (χ : RankOneCharacter) (r : RadicalLattice)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    pderiv (2 : Fin 3) ((linePotLam n χ r Q : HomogeneousPoly n) : Poly) = 0 := by
  rw [lp_coe_linePotLam, Derivation.map_smul, binaryPolynomialLift_pderiv_third, smul_zero]

theorem lp_restrict_contraction (P R : Binary.Poly) :
    binaryPolynomialRestrict (X 1 * binaryPolynomialLift P - X 0 * binaryPolynomialLift R) =
      X 1 * P - X 0 * R := by
  have hX0 : binaryPolynomialRestrict (X (0 : Fin 3)) = X (0 : Fin 2) := by
    simp [binaryPolynomialRestrict_X]
  have hX1 : binaryPolynomialRestrict (X (1 : Fin 3)) = X (1 : Fin 2) := by
    simp [binaryPolynomialRestrict_X]
  simp only [map_sub, map_mul, hX0, hX1, binaryPolynomialRestrict_lift]

/-- **The Kostant law for the radical cocycle**, with the constant `3 (n + 1)`. -/
theorem lp_lowerRadicalCoordinate (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (Q : Binary.HomogeneousPoly (n + 1)) :
    lowerRadicalCoordinate n (fun i => linePotLam n χ (radicalLatticeGenerator i) Q) =
      (3 * ((n : ℂ) + 1)) • Q := by
  apply Subtype.ext
  have hε : componentCharacter χ lpW * ((-1 : ℂ))⁻¹ = 1 := by
    rw [lp_componentCharacter χ hodd]
    norm_num
  have p0 : ((linePotLam n χ radicalLatticeFirst Q : HomogeneousPoly n) : Poly) =
      binaryPolynomialLift (C (3 : ℂ) * pderiv (1 : Fin 2) (Q : Binary.Poly)) := by
    rw [lp_coe_linePotLam, hε, one_smul]
    refine congrArg binaryPolynomialLift ?_
    simp [radicalLatticeFirst]
  have p1 : ((linePotLam n χ radicalLatticeSecond Q : HomogeneousPoly n) : Poly) =
      binaryPolynomialLift (-(C (3 : ℂ) * pderiv (0 : Fin 2) (Q : Binary.Poly))) := by
    rw [lp_coe_linePotLam, hε, one_smul]
    refine congrArg binaryPolynomialLift ?_
    simp [radicalLatticeSecond]
  have hq : (Q : Binary.Poly).IsHomogeneous (n + 1) :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp Q.2
  have euler := hq.sum_X_mul_pderiv
  rw [Fin.sum_univ_two] at euler
  have euler' : (X 0 : Binary.Poly) * pderiv (0 : Fin 2) (Q : Binary.Poly) +
      X 1 * pderiv (1 : Fin 2) (Q : Binary.Poly) = ((n : ℂ) + 1) • (Q : Binary.Poly) := by
    rw [euler, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add, Nat.cast_one]
  show binaryPolynomialRestrict (lowerRadicalContraction
    ((linePotLam n χ (radicalLatticeGenerator 0) Q : HomogeneousPoly n) : Poly)
    ((linePotLam n χ (radicalLatticeGenerator 1) Q : HomogeneousPoly n) : Poly)) =
      (3 * ((n : ℂ) + 1)) • (Q : Binary.Poly)
  rw [radicalLatticeGenerator_zero, radicalLatticeGenerator_one, p0, p1, lowerRadicalContraction,
    lp_restrict_contraction]
  calc (X 1 : Binary.Poly) * (C (3 : ℂ) * pderiv (1 : Fin 2) (Q : Binary.Poly)) -
        X 0 * -(C (3 : ℂ) * pderiv (0 : Fin 2) (Q : Binary.Poly))
      = C (3 : ℂ) * (X 0 * pderiv (0 : Fin 2) (Q : Binary.Poly) +
          X 1 * pderiv (1 : Fin 2) (Q : Binary.Poly)) := by ring
    _ = C (3 : ℂ) * (((n : ℂ) + 1) • (Q : Binary.Poly)) := by rw [euler']
    _ = (3 * ((n : ℂ) + 1)) • (Q : Binary.Poly) := by
        rw [smul_eq_C_mul, smul_eq_C_mul, C_mul, mul_assoc]

end Kostant

/-! ## The line cup data -/

section CupData

variable {σ : CuspidalRepresentation}

/-- **The potentials of the line source at the good-line reflection.** -/
def lineCupDataTw (E : LeviCocycleData σ n) (χ : RankOneCharacter) : LineCupDataTw n χ where
  a := linePotA E
  l := linePotL n χ
  lam := linePotLam n χ
  a_radical r := linePotA_radical E r
  l_radical r g := by
    apply LinearMap.ext
    intro Q
    rw [LinearMap.add_apply, linHom_radical_applyLineTw]
    exact linePotL_radical χ r g.val Q
  lam_free r Q := lp_pderiv_two_linePotLam χ r Q

/-- **The Levi side**: `a (s m) - a 1 = Sw (α(σ m σ) 1)`. -/
theorem lineCupDataTw_levi (E : LeviCocycleData σ n) (χ : RankOneCharacter)
    (m : GeneralLinearGroup (Fin 2) ℤ) :
    (lineCupDataTw E χ).a (goodLineLeviSection m).val - (lineCupDataTw E χ).a 1 =
      binarySwap n
        (E.α (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m)) 1) :=
  linePotA_levi E m

/-- **The Kostant law** for the radical cocycle of the line cup data, with the constant
`3 (n + 1)`. -/
theorem lowerKostant_lineCupData (E : LeviCocycleData σ n) (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    LowerKostant n (lineCupDataTw E χ).lam (3 * ((n : ℂ) + 1)) :=
  fun Q => lp_lowerRadicalCoordinate χ hodd Q

theorem lineKostant_constant_ne_zero (n : ℕ) : (3 * ((n : ℂ) + 1)) ≠ 0 := by
  have hne : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact mul_ne_zero (by norm_num) hne

/-- The cup product of the potentials of `lineCupDataTw` on the vertices `x` is the real Iwasawa
expression of the line source at the good-line reflection (`lineSourceTw_w`). -/
theorem lineCupDataTw_cup (E : LeviCocycleData σ n) (χ : RankOneCharacter)
    (x : Fin 3 → RationalGL3) :
    ((lineCupDataTw E χ).l (x 2) - (lineCupDataTw E χ).l (x 1))
        ((lineCupDataTw E χ).a (x 1) - (lineCupDataTw E χ).a (x 0)) =
      realCoefficientComponent n χ (ratReal rationalGoodLine)⁻¹
        ((lineRadical n χ (iwL (ratReal rationalGoodLine * ratReal (x 2))) -
            lineRadical n χ (iwL (ratReal rationalGoodLine * ratReal (x 1))))
          (E.α (iwAL (ratReal rationalGoodLine * ratReal (x 1))) 1 -
            E.α (iwAL (ratReal rationalGoodLine * ratReal (x 0))) 1)) :=
  linePot_cup E χ x

end CupData

/-! ## The period class of the line Levi cocycle -/

section Period

/-- The conjugation `m ↦ σ m σ` of `GL₂(ℤ)` by the pivot swap. -/
def lpIntPivot (m : GeneralLinearGroup (Fin 2) ℤ) : GeneralLinearGroup (Fin 2) ℤ :=
  binaryPivotSwap * m * binaryPivotSwap

theorem lp_pivot_mul_self {R : Type*} [CommRing R] :
    (binaryPivotSwap * binaryPivotSwap : GeneralLinearGroup (Fin 2) R) = 1 := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem lpIntPivot_mul (g h : GeneralLinearGroup (Fin 2) ℤ) :
    lpIntPivot (g * h) = lpIntPivot g * lpIntPivot h := by
  unfold lpIntPivot
  calc binaryPivotSwap * (g * h) * binaryPivotSwap
      = binaryPivotSwap * g * (binaryPivotSwap * binaryPivotSwap) * h * binaryPivotSwap := by
        rw [lp_pivot_mul_self, mul_one]
        simp only [mul_assoc]
    _ = (binaryPivotSwap * g * binaryPivotSwap) * (binaryPivotSwap * h * binaryPivotSwap) := by
        simp only [mul_assoc]

theorem lpIntPivot_involutive (m : GeneralLinearGroup (Fin 2) ℤ) :
    lpIntPivot (lpIntPivot m) = m := by
  unfold lpIntPivot
  calc binaryPivotSwap * (binaryPivotSwap * m * binaryPivotSwap) * binaryPivotSwap
      = (binaryPivotSwap * binaryPivotSwap) * m * (binaryPivotSwap * binaryPivotSwap) := by
        simp only [mul_assoc]
    _ = m := by rw [lp_pivot_mul_self, one_mul, mul_one]

theorem lpIntPivot_map (m : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (lpIntPivot m) =
      pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m) := by
  unfold lpIntPivot pivotConjugate
  simp only [map_mul, binaryPivotSwap_map]

/-- The swap of the binary variables intertwines the arithmetic action of `σ g σ` with that of `g`. -/
theorem lp_swap_rho (g : GeneralLinearGroup (Fin 2) ℤ) (v : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (periodAct n (lpIntPivot g) v) = periodAct n g (binarySwap n v) := by
  have h1 := binaryCoefficient_map_int n (lpIntPivot g) v
  have h2 := binaryCoefficient_map_int n g (binarySwap n v)
  have h3 := binarySwap_binaryCoefficient (n := n)
    (GeneralLinearGroup.map (Int.castRingHom ℝ) g) v
  rw [lpIntPivot_map] at h1
  rw [h1, h2] at h3
  exact h3

/-- The values of a one-cocycle of `GL₂(ℤ)` as a plain function with values in the binary forms. -/
def lpPhi (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (m : GeneralLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) := φ m

/-- **The transported cocycle**: `m ↦ Sw (φ (σ m σ))`. -/
def lineCocycleOf (n : ℕ) (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) :=
  ⟨fun m => binarySwap n (lpPhi n φ (lpIntPivot m)), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have hφ : lpPhi n φ (lpIntPivot g * lpIntPivot h) =
        periodAct n (lpIntPivot g) (lpPhi n φ (lpIntPivot h)) + lpPhi n φ (lpIntPivot g) :=
      (groupCohomology.mem_cocycles₁_iff φ).mp φ.property (lpIntPivot g) (lpIntPivot h)
    change binarySwap n (lpPhi n φ (lpIntPivot (g * h))) =
      periodAct n g (binarySwap n (lpPhi n φ (lpIntPivot h))) +
        binarySwap n (lpPhi n φ (lpIntPivot g))
    calc binarySwap n (lpPhi n φ (lpIntPivot (g * h)))
        = binarySwap n (lpPhi n φ (lpIntPivot g * lpIntPivot h)) := by rw [lpIntPivot_mul]
      _ = binarySwap n (periodAct n (lpIntPivot g) (lpPhi n φ (lpIntPivot h)) +
            lpPhi n φ (lpIntPivot g)) := congrArg (binarySwap n) hφ
      _ = binarySwap n (periodAct n (lpIntPivot g) (lpPhi n φ (lpIntPivot h))) +
            binarySwap n (lpPhi n φ (lpIntPivot g)) := map_add _ _ _
      _ = periodAct n g (binarySwap n (lpPhi n φ (lpIntPivot h))) +
            binarySwap n (lpPhi n φ (lpIntPivot g)) :=
          congrArg (fun z => z + binarySwap n (lpPhi n φ (lpIntPivot g))) (lp_swap_rho g _)⟩

/-- **The transported cocycle has nonzero class** if the original one has. -/
theorem lineCocycleOf_ne_zero (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (lineCocycleOf n φ) ≠ 0 := by
  intro h
  apply hφ
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff _).mp h
  let w : Binary.HomogeneousPoly (n + 1) := v
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  refine ⟨binarySwap n w, ?_⟩
  funext m
  have hm := congrFun hv (lpIntPivot m)
  rw [groupCohomology.d₀₁_hom_apply] at hm
  have h2 : periodAct n (lpIntPivot m) w - w = binarySwap n (lpPhi n φ m) := by
    refine hm.trans ?_
    show binarySwap n (lpPhi n φ (lpIntPivot (lpIntPivot m))) = binarySwap n (lpPhi n φ m)
    rw [lpIntPivot_involutive]
  have key : periodAct n m (binarySwap n w) - binarySwap n w = lpPhi n φ m :=
    calc periodAct n m (binarySwap n w) - binarySwap n w
        = binarySwap n (periodAct n (lpIntPivot m) w) - binarySwap n w :=
          congrArg (fun z => z - binarySwap n w) (lp_swap_rho m w).symm
      _ = binarySwap n (periodAct n (lpIntPivot m) w - w) := (map_sub (binarySwap n) _ _).symm
      _ = binarySwap n (binarySwap n (lpPhi n φ m)) := congrArg (binarySwap n) h2
      _ = lpPhi n φ m := lp_binarySwap_binarySwap _
  exact key

/-- **A line Levi cocycle with nonzero class.**  For an inducing datum with spherical cuspidal part
and `n` odd there are Levi cocycle data `E` and a one-cocycle `φL` of `GL₂(ℤ)` in
`arithmeticBinaryRep (n + 1) (-1)` with `φL m = a (s m) - a 1` for the potential `a` of
`lineCupDataTw E D.chi` and nonzero class. -/
theorem exists_lineLeviCocycle_ne_zero {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ (E : LeviCocycleData D.cusp n)
      (φL : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1))),
      (∀ m : GeneralLinearGroup (Fin 2) ℤ, (φL m : Binary.HomogeneousPoly (n + 1)) =
        (lineCupDataTw E D.chi).a (goodLineLeviSection m).val - (lineCupDataTw E D.chi).a 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φL ≠ 0 := by
  obtain ⟨E, φ, hφ, hφ0⟩ := exists_leviCocycleData_period_ne_zero D spherical odd
  refine ⟨E, lineCocycleOf n φ, fun m => ?_, lineCocycleOf_ne_zero φ hφ0⟩
  rw [lineCupDataTw_levi]
  exact congrArg (binarySwap n)
    ((hφ (lpIntPivot m)).trans (congrArg (fun A => E.α A 1) (lpIntPivot_map m)))

end Period

end TernaryPeriodPolynomials.TwistedSource
