module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineKostant
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle

@[expose] public section


/-!
# The potentials of the line source at the good-line reflection

For a character trivial on the integral units the line source `lineSource D E` at the adelic point
`rationalGroup rationalGoodLine⁻¹` is the cup product of two potentials.  With the real permutation
matrix `W = dlW` of the good line (the swap of the indices `0` and `2`), the Iwasawa factor of
`W x` in the line parabolic and the swap `Sw` of the two binary variables (which intertwines the
line Levi block `A = σ m σ` with the arithmetic Levi block `m`), they are

* `a x = Sw (α(iwALine(W x)) 1)`,
* `l x Q = ρ(W) (R(iwPLine(W x)) (Sw Q))`,
* `lam r Q = ρ(W) (R(u(3 r₂, 3 r₁)) (Sw Q))`   for `r = (r₁, r₂)`,

where `α` is the sign-twisted Levi cocycle of `LineLeviCocycleData`, `R` the radical cocycle of the
real line parabolic and `u(s, t)` the line unipotent.  They form a `LineCupData` (`dlCupData`): the
Levi potential does not see the lower radical lattice (`dlA_radical`), `l` satisfies the cocycle law
along it (`dlL_radical`, since `W` conjugates the lower unipotent `(3 r₁, 3 r₂)` to
`u(3 r₂, 3 r₁)`), and `lam` is free of `x₃` (`dl_pderiv_two_lam`: the conjugation by `W` moves the
variables of the radical to `x₁, x₂`).  In these coordinates `lam (1,0) Q = -3 ∂₁ Q`,
`lam (0,1) Q = 3 ∂₀ Q` (the factor `-1` is `χ(W) det(W)⁻¹` for trivial `χ`), so the Kostant law
holds with the constant `-3 (n + 1)` (`dl_lineKostantLaw`).  The Levi side is
`a (s m) - a 1 = Sw (α(σ m σ) 1)` (`dlA_levi`), `σ m σ` the pivot conjugate.

The headline is `lineSource_cuspRes_goodLine_ne_zero`: the good-line cusp coordinate of the line
source is nonzero as soon as a one-cocycle `φ` of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` with
`φ m = Sw (α(σ m σ) 1)` has nonzero class.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice arithmeticBinaryRep goodLineLeviSection goodLineRadicalInclusion
    rationalGoodLine rationalGoodLine_inverse lowerRadicalCoordinate lowerRadicalContraction
    radicalLatticeGenerator radicalLatticeFirst radicalLatticeSecond binaryPivotSwap
    binaryPolynomialLift binaryPolynomialRestrict binaryPolynomialRestrict_lift
    binaryPolynomialRestrict_X binaryPolynomialLift_pderiv_third)
open TernaryPeriodPolynomials.AnalyticClasses (binarySwap pivotConjugate)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The permutation matrix of the good line -/

section Permutation

/-- The real permutation matrix of the good line. -/
def dlW : RealGL3 := ratReal rationalGoodLine

theorem dlW_val : dlW.val = !![(0 : ℝ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dlW, rationalGoodLine, GeneralLinearGroup.map_apply]

theorem dlW_mul_self : dlW * dlW = 1 := by
  apply Units.ext
  rw [Units.val_mul, dlW_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem dlW_inv : dlW⁻¹ = dlW := inv_eq_of_mul_eq_one_right dlW_mul_self

theorem dlW_orth : IsOrthogonalReal dlW := by
  unfold IsOrthogonalReal
  rw [dlW_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The Iwasawa factor of the permutation matrix is trivial. -/
theorem dlW_iwPLine : iwPLine dlW = 1 := by
  apply Subtype.ext
  have h := iwasawaB_mul_orth (1 : RealGL3) dlW_orth
  rw [one_mul, iwasawaB_one] at h
  exact h

theorem dlW_iwALine : iwALine dlW = 1 := by
  unfold iwALine
  rw [dlW_iwPLine]
  exact lineLeviBlockHom.map_one

theorem dl_ratReal_one : ratReal (1 : RationalGL3) = 1 := map_one _

theorem dl_alpha_one {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (x : BinaryAdelicGL) : E.α 1 x = 0 :=
  E.orth 1 (by simp) x

theorem dl_alpha_iwALine_W {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n) :
    E.α (iwALine dlW) = fun _ => 0 := by
  rw [dlW_iwALine]
  exact funext (dl_alpha_one E)

/-- The Levi cocycle along the Iwasawa factor of `p W`: only the block of `p` remains. -/
theorem dl_alpha_iwALine_mul {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (p : lineParabolic ℝ) : E.α (iwALine (p.1 * dlW)) 1 = E.α (lineLeviBlock p) 1 := by
  rw [alpha_iwALine_mul E p dlW 1, dl_alpha_iwALine_W]
  simp [binaryCohomologicalAction]

theorem dl_rho_mul_apply (χ : RankOneCharacter) (g h : RealGL3) (v : HomogeneousPoly n) :
    realCoefficientComponent n χ (g * h) v =
      realCoefficientComponent n χ g (realCoefficientComponent n χ h v) := by
  rw [map_mul, Module.End.mul_apply]

end Permutation

/-! ## Line elements attached to the radical lattice and to Levi blocks -/

section Elements

/-- The line Levi element with trivial corner and block `A`. -/
def dlLevi (A : BinaryRealGL) : lineParabolic ℝ := ⟨lineLevi 1 A, lineLevi_mem 1 A⟩

/-- The line unipotent of the real line parabolic. -/
def dlUnipotent (s t : ℝ) : lineParabolic ℝ := ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩

/-- The line unipotent `u(3 r₂, 3 r₁)` conjugate under `W` to the lower unipotent of the lattice
point `(r₁, r₂)`. -/
def dlUnip (r : RadicalLattice) : lineParabolic ℝ :=
  dlUnipotent (3 * ((r.toAdd.2 : ℤ) : ℝ)) (3 * ((r.toAdd.1 : ℤ) : ℝ))

theorem dlLevi_block (A : BinaryRealGL) : lineLeviBlock (dlLevi A) = A :=
  lineLeviBlock_levi 1 A

theorem dlUnipotent_block (s t : ℝ) : lineLeviBlock (dlUnipotent s t) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLeviBlock, lrBlockP, lrLowerBlock, dlUnipotent, lineUnipotent, upperUnipotent]

theorem dlUnip_block (r : RadicalLattice) : lineLeviBlock (dlUnip r) = 1 :=
  dlUnipotent_block _ _

theorem dl_componentCharacter_upperUnipotent (χ : RankOneCharacter) (s t : ℝ) :
    componentCharacter χ (upperUnipotent s t) = 1 := by
  have hdet : GeneralLinearGroup.det (upperUnipotent s t) = 1 := by
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, upperUnipotent, Matrix.det_fin_three]
  simp [componentCharacter, hdet]

/-- The Levi action `lineStar` is trivial on the line unipotent. -/
theorem dlUnipotent_star (χ : RankOneCharacter) (k : ℕ) (s t : ℝ) (Q : Binary.HomogeneousPoly k) :
    lineStar χ k (dlUnipotent s t) Q = Q := by
  have hθ : lineTheta χ (dlUnipotent s t) = 1 := by
    rw [lineTheta_apply, dlUnipotent_block]
    have h00 : (dlUnipotent s t).1.val 0 0 = 1 := rfl
    have hc : componentCharacter χ (dlUnipotent s t).1 = 1 :=
      dl_componentCharacter_upperUnipotent χ s t
    rw [hc, h00]
    simp
  rw [lineStar_apply, hθ, dlUnipotent_block]
  simp

theorem dlUnipotent_star_inv (χ : RankOneCharacter) (k : ℕ) (s t : ℝ)
    (Q : Binary.HomogeneousPoly k) : lineStar χ k (dlUnipotent s t)⁻¹ Q = Q := by
  have h := lineStar_inv_cancel χ k (dlUnipotent s t) Q
  rwa [dlUnipotent_star] at h

theorem dlW_mul_lower (x y : ℝ) :
    dlW * lowerPlaneUnipotent x y = upperUnipotent y x * dlW := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dlW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerPlaneUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem dlW_mul_upper (s t : ℝ) :
    dlW * upperUnipotent s t = lowerPlaneUnipotent t s * dlW := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dlW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerPlaneUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem dl_ratReal_radical (r : RadicalLattice) :
    ratReal (goodLineRadicalInclusion r).val =
      lowerPlaneUnipotent (3 * ((r.toAdd.1 : ℤ) : ℝ)) (3 * ((r.toAdd.2 : ℤ) : ℝ)) := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (lowerPlaneUnipotent (3 * ((r.toAdd.1 : ℤ) : ℚ)) (3 * ((r.toAdd.2 : ℤ) : ℚ))) = _
  rw [TernaryPeriodPolynomials.SphericalDetection.Helpers.map_lowerPlaneUnipotent]
  simp

/-- Conjugation by `W`: the lower unipotent `(3 r₁, 3 r₂)` becomes the line unipotent
`u(3 r₂, 3 r₁)`. -/
theorem dlW_mul_radical (r : RadicalLattice) :
    dlW * ratReal (goodLineRadicalInclusion r).val = (dlUnip r).1 * dlW := by
  rw [dl_ratReal_radical]
  exact dlW_mul_lower (3 * ((r.toAdd.1 : ℤ) : ℝ)) (3 * ((r.toAdd.2 : ℤ) : ℝ))

theorem dlW_mul_radical' (r : RadicalLattice) :
    dlW * (dlUnip r).1 = ratReal (goodLineRadicalInclusion r).val * dlW := by
  rw [dl_ratReal_radical]
  exact dlW_mul_upper (3 * ((r.toAdd.2 : ℤ) : ℝ)) (3 * ((r.toAdd.1 : ℤ) : ℝ))

theorem dl_ratReal_levi (m : GeneralLinearGroup (Fin 2) ℤ) :
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
theorem dlW_mul_levi (m : GeneralLinearGroup (Fin 2) ℤ) :
    dlW * ratReal (goodLineLeviSection m).val =
      (dlLevi (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m))).1 * dlW := by
  rw [dl_ratReal_levi]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dlW_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dlLevi, lineLevi_val, pivotConjugate, binaryPivotSwap, planeLevi, planeBlock,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, GeneralLinearGroup.map_apply,
      Matrix.vecMul, dotProduct]

end Elements

/-! ## The potentials -/

section Potentials

variable {σ : CuspidalRepresentation}

/-- **The Levi potential of the line source at the good-line reflection.** -/
def dlA (E : LineLeviCocycleData σ n) (x : RationalGL3) : Binary.HomogeneousPoly (n + 1) :=
  binarySwap n (E.α (iwALine (dlW * ratReal x)) 1)

/-- **The radical potential of the line source at the good-line reflection.** -/
def dlL (n : ℕ) (x : RationalGL3) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  realCoefficientComponent n trivialCharacter dlW ∘ₗ
    lineRadical n trivialCharacter (iwPLine (dlW * ratReal x)) ∘ₗ binarySwap n

/-- **The radical cocycle on the lower radical lattice.** -/
def dlLam (n : ℕ) (r : RadicalLattice) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  realCoefficientComponent n trivialCharacter dlW ∘ₗ
    lineRadical n trivialCharacter (dlUnip r) ∘ₗ binarySwap n

theorem binarySwap_binarySwap' (Q : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (binarySwap n Q) = Q :=
  Subtype.ext (by
    show rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) Q.val) = Q.val
    rw [rename_rename]
    have h : ((Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) ∘
        (Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2)) = id := by
      funext i
      exact Equiv.swap_apply_self _ _ _
    rw [h, rename_id]
    try rfl)

theorem dlA_one (E : LineLeviCocycleData σ n) : dlA E 1 = 0 := by
  unfold dlA
  rw [dl_ratReal_one, mul_one, dlW_iwALine, dl_alpha_one, map_zero]

theorem dlA_radical (E : LineLeviCocycleData σ n) (r : RadicalLattice) :
    dlA E (goodLineRadicalInclusion r).val = dlA E 1 := by
  rw [dlA_one]
  unfold dlA
  rw [dlW_mul_radical r, dl_alpha_iwALine_mul, dlUnip_block, dl_alpha_one, map_zero]

/-- **The Levi side of the potential**: `a (s m) - a 1 = Sw (α(σ m σ) 1)`. -/
theorem dlA_levi (E : LineLeviCocycleData σ n) (m : GeneralLinearGroup (Fin 2) ℤ) :
    dlA E (goodLineLeviSection m).val - dlA E 1 =
      binarySwap n
        (E.α (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m)) 1) := by
  rw [dlA_one, sub_zero]
  unfold dlA
  rw [dlW_mul_levi, dl_alpha_iwALine_mul, dlLevi_block]

/-- **The cocycle law of the radical potential along the lower radical lattice.** -/
theorem dlL_radical (r : RadicalLattice) (g : RationalGL3) (Q : Binary.HomogeneousPoly (n + 1)) :
    dlL n ((goodLineRadicalInclusion r).val * g) Q =
      dlLam n r Q +
        realCoefficientComponent n trivialCharacter (ratReal (goodLineRadicalInclusion r).val)
          (dlL n g Q) := by
  have hm : dlW * ratReal ((goodLineRadicalInclusion r).val * g) =
      (dlUnip r).1 * (dlW * ratReal g) := by
    rw [map_mul, ← mul_assoc, dlW_mul_radical, mul_assoc]
  have hcomm : ∀ X : HomogeneousPoly n,
      realCoefficientComponent n trivialCharacter dlW
          (realCoefficientComponent n trivialCharacter (dlUnip r).1 X) =
        realCoefficientComponent n trivialCharacter (ratReal (goodLineRadicalInclusion r).val)
          (realCoefficientComponent n trivialCharacter dlW X) := by
    intro X
    calc realCoefficientComponent n trivialCharacter dlW
          (realCoefficientComponent n trivialCharacter (dlUnip r).1 X)
        = realCoefficientComponent n trivialCharacter (dlW * (dlUnip r).1) X :=
          (dl_rho_mul_apply trivialCharacter _ _ X).symm
      _ = realCoefficientComponent n trivialCharacter
            (ratReal (goodLineRadicalInclusion r).val * dlW) X := by
          rw [dlW_mul_radical']
      _ = realCoefficientComponent n trivialCharacter (ratReal (goodLineRadicalInclusion r).val)
            (realCoefficientComponent n trivialCharacter dlW X) :=
          dl_rho_mul_apply trivialCharacter _ _ X
  have hstar : lineStar trivialCharacter (n + 1) (dlUnip r)⁻¹ (binarySwap n Q) =
      binarySwap n Q :=
    dlUnipotent_star_inv trivialCharacter (n + 1) _ _ _
  simp only [dlL, dlLam, LinearMap.comp_apply]
  rw [hm, lineRadical_iwPLine_mul trivialCharacter (dlUnip r) (dlW * ratReal g)
    (binarySwap n Q), hstar, map_add, hcomm]

end Potentials

/-! ## The cup product of the potentials is the line source at the reflection -/

section Cup

variable {σ : CuspidalRepresentation}

/-- **The cup product of the potentials**, as the expression of the line source at the
reflection. -/
theorem dl_cup (E : LineLeviCocycleData σ n) (x : Fin 3 → RationalGL3) :
    (dlL n (x 2) - dlL n (x 1)) (dlA E (x 1) - dlA E (x 0)) =
      realCoefficientComponent n trivialCharacter dlW
        ((lineRadical n trivialCharacter (iwPLine (dlW * ratReal (x 2))) -
            lineRadical n trivialCharacter (iwPLine (dlW * ratReal (x 1))))
          (E.α (iwALine (dlW * ratReal (x 1))) 1 - E.α (iwALine (dlW * ratReal (x 0))) 1)) := by
  simp only [LinearMap.sub_apply, dlL, dlA, LinearMap.comp_apply, map_sub, binarySwap_binarySwap']

/-- A permutation matrix as an integral matrix. -/
def dlPerm : GeneralLinearGroup (Fin 3) ℤ :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The finite part of the good-line reflection point is an integral matrix. -/
theorem dl_finite_integral :
    ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
      finiteGroup (rationalGroup (rationalGoodLine : RationalGL3)⁻¹) =
        GeneralLinearGroup.map integralEmbedding k := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) dlPerm, ?_⟩
  rw [rationalGoodLine_inverse]
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [finiteGroup_rational, rationalFinite, rationalGoodLine, dlPerm,
      GeneralLinearGroup.map_apply]

theorem dl_realGroup :
    realGroup (rationalGroup (rationalGoodLine : RationalGL3)⁻¹) = dlW⁻¹ := by
  rw [realGroup_rational, map_inv]
  rfl

/-- **The line source at the good-line reflection and rational vertices.** -/
theorem dl_lineSource_rational (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    lineSource D E (fun i => ratReal (x i)) (rationalGroup (rationalGoodLine : RationalGL3)⁻¹) =
      realCoefficientComponent n D.chi dlW
        ((lineRadical n D.chi (iwPLine (dlW * ratReal (x 2))) -
            lineRadical n D.chi (iwPLine (dlW * ratReal (x 1))))
          (E.α (iwALine (dlW * ratReal (x 1))) 1 - E.α (iwALine (dlW * ratReal (x 0))) 1)) := by
  obtain ⟨k, hk⟩ := dl_finite_integral
  unfold lineSource
  rw [lineSourceAt_integral D E hχ _ k hk, dl_realGroup, inv_inv, dlW_inv]

end Cup

/-! ## The radical cocycle: explicit form, freedom and the Kostant law -/

section Kostant

theorem dl_complex_val :
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) dlW).val = !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dlW_val, GeneralLinearGroup.map_apply]

theorem dl_inv_val :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) dlW)⁻¹ : GL3).val =
      !![(0 : ℂ), 0, 1; 0, 1, 0; 1, 0, 0] := by
  have h : (GeneralLinearGroup.map (algebraMap ℝ ℂ) dlW)⁻¹ =
      GeneralLinearGroup.map (algebraMap ℝ ℂ) dlW := by
    have h1 := map_inv
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) :
        GeneralLinearGroup (Fin 3) ℝ →* GeneralLinearGroup (Fin 3) ℂ) dlW
    rw [dlW_inv] at h1
    exact h1.symm
  rw [h]
  exact dl_complex_val

theorem dl_det_complex :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) dlW) : ℂˣ) : ℂ) = -1 := by
  rw [GeneralLinearGroup.val_det_apply, dl_complex_val, Matrix.det_fin_three]
  show (0 : ℂ) * 1 * 0 - 0 * 0 * 0 - 0 * 0 * 0 + 0 * 0 * 1 + 1 * 0 * 0 - 1 * 1 * 1 = -1
  norm_num

/-- Substitution by the permutation matrix on forms free of `x₀`. -/
theorem dl_substitute_rename_succ (N : Matrix (Fin 3) (Fin 3) ℂ)
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

theorem dl_pderiv_zero_rename_swap (P : Binary.Poly) :
    pderiv (0 : Fin 2) (rename (Equiv.swap (0 : Fin 2) 1) P) =
      rename (Equiv.swap (0 : Fin 2) 1) (pderiv (1 : Fin 2) P) := by
  have h := pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) P
  rwa [Equiv.swap_apply_right] at h

theorem dl_pderiv_one_rename_swap (P : Binary.Poly) :
    pderiv (1 : Fin 2) (rename (Equiv.swap (0 : Fin 2) 1) P) =
      rename (Equiv.swap (0 : Fin 2) 1) (pderiv (0 : Fin 2) P) := by
  have h := pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) P
  rwa [Equiv.swap_apply_left] at h

theorem dl_rename_swap_rename_swap (P : Binary.Poly) :
    rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) P) = P := by
  rw [rename_rename]
  have h : ((Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) ∘
      (Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2)) = id := by
    funext i
    exact Equiv.swap_apply_self _ _ _
  rw [h, rename_id]
  try rfl

theorem dl_coe_lineRadical_unip (r : RadicalLattice) (Q : Binary.HomogeneousPoly (n + 1)) :
    ((lineRadical n trivialCharacter (dlUnip r) Q : HomogeneousPoly n) : Poly) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (C (algebraMap ℝ ℂ (3 * ((r.toAdd.1 : ℤ) : ℝ))) * pderiv (0 : Fin 2) (Q : Binary.Poly) -
          C (algebraMap ℝ ℂ (3 * ((r.toAdd.2 : ℤ) : ℝ))) * pderiv (1 : Fin 2) (Q : Binary.Poly)) :=
  coe_lineRadical_unipotent n trivialCharacter _ _ Q

/-- **The explicit form of the radical cocycle**: the conjugation by `W` turns the radical at the
line unipotent into a form in `x₁, x₂` only. -/
theorem dl_coe_lam (r : RadicalLattice) (Q : Binary.HomogeneousPoly (n + 1)) :
    ((dlLam n r Q : HomogeneousPoly n) : Poly) =
      (componentCharacter trivialCharacter dlW * ((-1 : ℂ))⁻¹) •
        binaryPolynomialLift
          (C (algebraMap ℝ ℂ (3 * ((r.toAdd.1 : ℤ) : ℝ))) * pderiv (1 : Fin 2) (Q : Binary.Poly) -
            C (algebraMap ℝ ℂ (3 * ((r.toAdd.2 : ℤ) : ℝ))) *
              pderiv (0 : Fin 2) (Q : Binary.Poly)) := by
  have h1 : ((dlLam n r Q : HomogeneousPoly n) : Poly) =
      fullCoefficientComponent trivialCharacter dlW
        ((lineRadical n trivialCharacter (dlUnip r) (binarySwap n Q) : HomogeneousPoly n) :
          Poly) := rfl
  have hsw : ((binarySwap n Q : Binary.HomogeneousPoly (n + 1)) : Binary.Poly) =
      rename (Equiv.swap (0 : Fin 2) 1) (Q : Binary.Poly) := rfl
  rw [h1, fullCoefficientComponent_apply, dl_det_complex, dl_coe_lineRadical_unip,
    dl_substitute_rename_succ _ dl_inv_val]
  refine congrArg
    (fun z => (componentCharacter trivialCharacter dlW * ((-1 : ℂ))⁻¹) • binaryPolynomialLift z) ?_
  rw [hsw]
  simp only [map_sub, map_mul, rename_C, dl_pderiv_zero_rename_swap, dl_pderiv_one_rename_swap,
    dl_rename_swap_rename_swap]

/-- **The radical cocycle is free of `x₃`.** -/
theorem dl_pderiv_two_lam (r : RadicalLattice) (Q : Binary.HomogeneousPoly (n + 1)) :
    pderiv (2 : Fin 3) ((dlLam n r Q : HomogeneousPoly n) : Poly) = 0 := by
  rw [dl_coe_lam, Derivation.map_smul, binaryPolynomialLift_pderiv_third, smul_zero]

theorem dl_scalar : componentCharacter trivialCharacter dlW * ((-1 : ℂ))⁻¹ = -1 := by
  have hc : componentCharacter trivialCharacter dlW = 1 := rfl
  rw [hc]
  norm_num

theorem dl_lift_C_mul (a : ℂ) (P : Binary.Poly) :
    binaryPolynomialLift (C a * P) = a • binaryPolynomialLift P := by
  rw [← smul_eq_C_mul, map_smul]

theorem dl_lam_first (Q : Binary.HomogeneousPoly (n + 1)) :
    ((dlLam n radicalLatticeFirst Q : HomogeneousPoly n) : Poly) =
      binaryPolynomialLift ((-3 : ℂ) • pderiv (1 : Fin 2) (Q : Binary.Poly)) := by
  have hs : ((radicalLatticeFirst.toAdd.1 : ℤ) : ℝ) = 1 := by simp [radicalLatticeFirst]
  have ht : ((radicalLatticeFirst.toAdd.2 : ℤ) : ℝ) = 0 := by simp [radicalLatticeFirst]
  have e3 : algebraMap ℝ ℂ (3 * (1 : ℝ)) = (3 : ℂ) := by simp
  have e0 : algebraMap ℝ ℂ (3 * (0 : ℝ)) = (0 : ℂ) := by simp
  rw [dl_coe_lam, dl_scalar, hs, ht, e3, e0, C_0, zero_mul, sub_zero, dl_lift_C_mul,
    map_smul, smul_smul]
  norm_num

theorem dl_lam_second (Q : Binary.HomogeneousPoly (n + 1)) :
    ((dlLam n radicalLatticeSecond Q : HomogeneousPoly n) : Poly) =
      binaryPolynomialLift (-((-3 : ℂ) • pderiv (0 : Fin 2) (Q : Binary.Poly))) := by
  have hs : ((radicalLatticeSecond.toAdd.1 : ℤ) : ℝ) = 0 := by simp [radicalLatticeSecond]
  have ht : ((radicalLatticeSecond.toAdd.2 : ℤ) : ℝ) = 1 := by simp [radicalLatticeSecond]
  have e3 : algebraMap ℝ ℂ (3 * (1 : ℝ)) = (3 : ℂ) := by simp
  have e0 : algebraMap ℝ ℂ (3 * (0 : ℝ)) = (0 : ℂ) := by simp
  rw [dl_coe_lam, dl_scalar, hs, ht, e3, e0, C_0, zero_mul, zero_sub, map_neg, map_neg,
    dl_lift_C_mul, map_smul, smul_neg, smul_smul]
  norm_num

/-- **The Kostant law for the radical cocycle of the line cup data**, with the constant
`-3 (n + 1)`. -/
theorem dl_lineKostantLaw (n : ℕ) :
    LineKostantLaw n (dlLam n) ((-3 : ℂ) * ((n + 1 : ℕ) : ℂ)) :=
  lineKostantLaw_of_derivative (κ := (-3 : ℂ)) (fun q => dl_lam_first q) (fun q => dl_lam_second q)

theorem dl_kostant_constant_ne_zero (n : ℕ) : ((-3 : ℂ) * ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact mul_ne_zero (by norm_num) hne

end Kostant

/-! ## The line cup data and the headline -/

section CupData

variable {σ : CuspidalRepresentation}

/-- **The potentials of the line source at the good-line reflection.** -/
def dlCupData (E : LineLeviCocycleData σ n) : LineCupData n where
  a := dlA E
  l := dlL n
  lam := dlLam n
  a_radical r := dlA_radical E r
  l_radical r g := by
    apply LinearMap.ext
    intro Q
    rw [LinearMap.add_apply, lineHom_radical_apply]
    exact dlL_radical r g.val Q

/-- **The Levi side**: `a (s m) - a 1 = Sw (α(σ m σ) 1)`. -/
theorem dlCupData_levi (E : LineLeviCocycleData σ n) (m : GeneralLinearGroup (Fin 2) ℤ) :
    (dlCupData E).a (goodLineLeviSection m).val - (dlCupData E).a 1 =
      binarySwap n (E.α (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m)) 1) :=
  dlA_levi E m

/-- The line source at the good-line reflection and rational vertices is the cup product of the
potentials of `dlCupData`. -/
theorem dlCupData_source (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (x : Fin 3 → RationalGL3) :
    lineSource D E (fun i => ratReal (x i)) (rationalGroup (rationalGoodLine : RationalGL3)⁻¹) =
      ((dlCupData E).l (x 2) - (dlCupData E).l (x 1))
        ((dlCupData E).a (x 1) - (dlCupData E).a (x 0)) := by
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  rw [dl_lineSource_rational D E hχ x, hchi]
  exact (dl_cup E x).symm

/-- **The good-line cusp coordinate of the line source is nonzero**, provided the one-cocycle
`m ↦ Sw (α(σ m σ) 1)` of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` (the Eichler cocycle of the
line Levi block at the identity adele, transported by the pivot swap) has nonzero class. -/
theorem lineSource_cuspRes_goodLine_ne_zero (D : InducingData n)
    (E : LineLeviCocycleData D.cusp n) (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m =
      binarySwap n (E.α (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m)) 1))
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line (lineSource D E) z) :
    TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n D.chi .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) ≠ 0 :=
  cuspRes_line_true_ne_zero_of_evaluates D hchi (dlCupData E) (dl_lineKostantLaw n)
    (dl_kostant_constant_ne_zero n) φ (fun m => (hφ m).trans (dlCupData_levi E m).symm) hφ0 pos hz
    (dlCupData_source D E hchi)

end CupData

end TernaryPeriodPolynomials.SourceConstruction
