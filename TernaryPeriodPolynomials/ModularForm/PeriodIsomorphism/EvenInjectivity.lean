module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneEichlerShimura
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CocycleParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CuspTValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodPolynomial
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleReflection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.PositiveWords
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreCosets
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CentralCharacter
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CuspPeriodBridge
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.RepUnfolding
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialParity
public import TernaryPeriodPolynomials.ModularForm.Periods.PeriodHomogeneous

@[expose] public section


/-!
# Corollary 1.4, Step 2: even-side injectivity

For even `n > 0` and `h : CuspForm levelOne (n+2)`,
`normalizedEvenPeriodPart n h = 0 → h = 0`.

**Step (a)** (this file, first lemma): reduces this to showing the `H1π`-class of `h`'s
`classicalArithmeticCocycle` (at `degree := n`, `twist := 0`) vanishes, via `per_injective`
(`ParabolicES.lean`) and `levelOnePeriodMap_apply` (`LevelOneEichlerShimura.lean`, `rfl`). The two
private helpers transport across the specific weight parametrization `-2 * hw r` that `per` is
stated for, without ever touching `h` itself except by a propositional cast.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.ModularH1
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open Matrix Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup MvPolynomial
open GeneralEisenstein.Binary (substitute substitute_comp substitute_X linearForm HomogeneousPoly Poly)

/-- `substitute` by the identity matrix is the identity map on `Poly`. -/
private theorem substitute_one (p : Poly) :
    substitute (1 : Matrix (Fin 2) (Fin 2) ℂ) p = p := by
  have hid : substitute (1 : Matrix (Fin 2) (Fin 2) ℂ) = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [substitute_X]
    fin_cases i <;> simp [linearForm, Matrix.one_apply]
  rw [hid, AlgHom.id_apply]

/-- Negating every variable is substitution by `-1` (local re-derivation of
`SquareInvolution.lean`'s private `linearForm_neg_one`/`substitute_neg_one`, not visible from this
file). -/
private theorem linearForm_neg_one (i : Fin 2) :
    linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ) i = -X i := by
  fin_cases i <;> simp [linearForm, Matrix.neg_apply, Matrix.one_apply]

private theorem substitute_neg_one (p : Poly) :
    substitute (-1 : Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ (fun i => -X i) p := by
  show bind₁ (linearForm (-1 : Matrix (Fin 2) (Fin 2) ℂ)) p = bind₁ (fun i => -X i) p
  rw [funext linearForm_neg_one]

/-- For `P` homogeneous of even degree, substituting `(X,Y) ↦ (X,-Y)` (`binaryParityReflection`'s
underlying substitution) agrees with substituting `(X,Y) ↦ (-X,Y)` (the substitution
`evenPeriodPart` uses). Both differ from "negate everything" by one further negation of the
*other* variable, and negating everything fixes `P` (`bind₁_neg_X_of_isHomogeneous_even`). -/
private theorem substitute_negateSecond_eq_negateFirst {n : ℕ} (hn : Even n) {P : Poly}
    (hP : P.IsHomogeneous n) :
    substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P =
      substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) P := by
  have hτσ : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hσσ : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![-1, 0; 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have step1 : substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P) = P := by
    rw [← AlgHom.comp_apply, substitute_comp, hτσ, substitute_neg_one]
    exact bind₁_neg_X_of_isHomogeneous_even hP hn
  have step2 : substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
        (substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P)) =
      substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) P := by
    rw [← AlgHom.comp_apply, substitute_comp, hσσ, substitute_one]
  rw [step1] at step2
  exact step2.symm

/-- The substitution linear form of `!![-1,0;0,1]` is `![-X 0, X 1]`, matching `evenPeriodPart`'s
own substitution exactly. -/
private theorem linearForm_negateFirst :
    linearForm (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = ![-X 0, X 1] := by
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]

private theorem substitute_negateFirst (p : Poly) :
    substitute (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) p = bind₁ ![-X 0, X 1] p := by
  show bind₁ (linearForm (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) p = bind₁ ![-X 0, X 1] p
  rw [linearForm_negateFirst]

/-- `binaryParityReflection` unfolds, at the `Poly` level, to its underlying substitution
(mirrors the `change`-based unfolding already used in `BinaryPolynomialParity.lean`'s own
`binaryParityReflection_standardBasis`). -/
private theorem binaryParityReflection_val {n : ℕ} (x : HomogeneousPoly n) :
    (binaryParityReflection n x : Poly) =
      substitute (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) (x : Poly) := rfl

/-- `binaryParityComponent` at `parity = 0` unfolds to the averaging formula (mirrors the
`change`-based unfolding already used in `BinaryPolynomialParity.lean`'s own
`binaryParityComponent_coord`). -/
private theorem binaryParityComponent_zero_eq {n : ℕ} (x : HomogeneousPoly n) :
    binaryParityComponent n 0 x = (2 : ℂ)⁻¹ • (x + binaryParityReflection n x) := by
  show (2 : ℂ)⁻¹ • (x + (-1 : ℂ) ^ (0 : ℕ) • binaryParityReflection n x) = _
  rw [pow_zero, one_smul]

/-- **Step (c1).** The parity-zero projection of `cuspPeriodPolynomial h n` equals
`evenPeriodPart n h`, for even `n`. -/
theorem cuspPeriodPolynomial_parityComponent_eq_evenPeriodPart {n : ℕ} (hn : Even n)
    (h : CuspForm levelOne ((n : ℤ) + 2)) :
    (binaryParityComponent n 0 (cuspPeriodPolynomial h n) : Poly) =
      TernaryPeriodPolynomials.Argument.evenPeriodPart n h := by
  rw [binaryParityComponent_zero_eq]
  show (2 : ℂ)⁻¹ • ((cuspPeriodPolynomial h n : Poly) +
      (binaryParityReflection n (cuspPeriodPolynomial h n) : Poly)) =
    TernaryPeriodPolynomials.Argument.evenPeriodPart n h
  rw [binaryParityReflection_val, cuspPeriodPolynomial_eq_periodPolynomial hn h,
    substitute_negateSecond_eq_negateFirst hn
      (TernaryPeriodPolynomials.Argument.CuspForms.periodPolynomial_isHomogeneous h),
    substitute_negateFirst]
  rfl

/-- Casting a `CuspForm levelOne` along a propositional weight equality preserves vanishing. -/
private theorem castCuspForm_eq_zero_iff {k₁ k₂ : ℤ} (e : k₁ = k₂)
    (f : CuspForm levelOne k₁) : (e ▸ f : CuspForm levelOne k₂) = 0 ↔ f = 0 := by
  subst e
  rfl

/-- Casting a `CuspForm` argument along a propositional weight equality leaves
`classicalArithmeticCocycle` unchanged, up to re-deriving the `weight_eq` side condition for the
original weight (the two sides agree by proof irrelevance on the `Prop`-valued arguments). -/
private theorem classicalArithmeticCocycle_cast {degree : ℕ} {weight₁ weight₂ : ℤ}
    (e : weight₁ = weight₂) (form : CuspForm levelOne weight₁)
    (weq₂ : weight₂ = (degree : ℤ) + 2) (even : Even degree) (twist : ℤ) (parity : ℕ)
    (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    classicalArithmeticCocycle (e ▸ form : CuspForm levelOne weight₂) degree weq₂ even twist
        parity sign =
      classicalArithmeticCocycle form degree (e.trans weq₂) even twist parity sign := by
  subst e
  rfl

/-- **Step (a).** Reduces `h = 0` to vanishing of the `H1π`-class of `h`'s classical arithmetic
cocycle (degree `n`, twist `0`, the parity picked out by `σ = 0` via `per`). -/
theorem h_eq_zero_of_classicalArithmeticCocycle_H1_zero {n : ℕ} (hn : Even n)
    (h : CuspForm levelOne ((n : ℤ) + 2))
    (hzero : groupCohomology.H1π (arithmeticBinaryRep n 0)
        (classicalArithmeticCocycle h n rfl hn 0 (parityOf (0 : ℤ)).val (parityOf_sign 0)) = 0) :
    h = 0 := by
  obtain ⟨r, hr⟩ := hn
  have hr2 : n = 2 * r := by omega
  subst hr2
  rw [← castCuspForm_eq_zero_iff (weight_eq_r r).symm h]
  apply per_injective r 0
  rw [map_zero]
  show levelOnePeriodMap (hw r) (2 * r) (weight_eq_r r) (even_two_mul r) 0 (parityOf (0 : ℤ))
      (parityOf_sign 0) ((weight_eq_r r).symm ▸ h) = 0
  rw [levelOnePeriodMap_apply,
    classicalArithmeticCocycle_cast (weight_eq_r r).symm h (weight_eq_r r) (even_two_mul r) 0
      (parityOf (0 : ℤ)).val (parityOf_sign 0)]
  exact hzero

/-- The complex cast of an integer `SpecialLinearGroup` element, entrywise (local re-derivation;
`RepUnfolding.lean`'s private `castSL_apply` is not visible from this file). -/
private theorem castSL_entry (g : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g) :
        Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℂ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- `T⁻¹` is `!![1,-1;0,1]` as an integer matrix (mirrors `coe_modularS_inv`,
`AdjCoreCosets.lean`). -/
private theorem coe_modularT_inv :
    ((ModularGroup.T⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, -1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `T⁻¹` casts to `!![1,-1;0,1]` as a complex matrix. -/
private theorem castT_inv_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.T⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![1, -1; 0, 1] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [coe_modularT_inv]

/-- The substitution linear form of `cast T⁻¹` is `![X 0 - X 1, X 1]`. -/
private theorem linearForm_castT_inv :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) =
      ![X 0 - X 1, X 1] := by
  rw [castT_inv_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]; ring

private theorem substitute_castT_inv (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) p =
      bind₁ ![X 0 - X 1, X 1] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.T⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![X 0 - X 1, X 1] p
  rw [linearForm_castT_inv]

/-- `S⁻¹` is `!![0,1;-1,0]` as an integer matrix (local re-derivation; `AdjCoreCosets.lean`'s
`coe_modularS_inv` is not visible from this file). -/
private theorem coe_modularS_inv :
    ((ModularGroup.S⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `S⁻¹` casts to `!![0,1;-1,0]` as a complex matrix. -/
private theorem castS_inv_matrix :
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL ModularGroup.S⁻¹) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  ext i j
  rw [castSL_entry]
  fin_cases i <;> fin_cases j <;> norm_num [coe_modularS_inv]

/-- The substitution linear form of `cast S⁻¹` is `![X 1, -X 0]`. -/
private theorem linearForm_castS_inv :
    linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) =
      ![X 1, -X 0] := by
  rw [castS_inv_matrix]
  funext i
  fin_cases i <;> simp [linearForm, Fin.sum_univ_two]

private theorem substitute_castS_inv (p : Poly) :
    substitute (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) p =
      bind₁ ![X 1, -X 0] p := by
  show bind₁ (linearForm (GeneralLinearGroup.map (Int.castRingHom ℂ)
      (SpecialLinearGroup.toGL ModularGroup.S⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)) p =
    bind₁ ![X 1, -X 0] p
  rw [linearForm_castS_inv]

private theorem binaryStandardBasis_zero_coe (degree : ℕ) :
    (binaryStandardBasis degree 0 : Poly) = X 1 ^ degree := by
  rw [binaryStandardBasis_coe]
  simp

private theorem binaryStandardBasis_last_coe (degree : ℕ) :
    (binaryStandardBasis degree (Fin.last degree) : Poly) = X 0 ^ degree := by
  rw [binaryStandardBasis_coe]
  simp

private theorem parityOf_zero_val : (parityOf (0 : ℤ)).val = 0 := by
  have h0 : Even (0 : ℤ) := ⟨0, by ring⟩
  simp [parityOf, h0]

/-- **Step (c).** The parity-zero cocycle built from `h`'s cusp-normalized binary cocycle equals
the explicit one-boundary cycle on `v := -a • binaryStandardBasis n 0`, where `a` is the
`eval![1,0]`-coefficient of `evenPeriodPart n h`, once `normalizedEvenPeriodPart n h = 0`. -/
theorem modularCocycleParity_cuspNormalizedBinaryCocycle_eq_oneBoundaryCycle {n : ℕ} (hn : Even n)
    (h : CuspForm levelOne ((n : ℤ) + 2))
    (hzero : TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n h = 0) :
    modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) =
      oneBoundaryCycle (modularBinaryRep n 0)
        (-(eval (![1, 0] : Fin 2 → ℂ)
            (TernaryPeriodPolynomials.Argument.evenPeriodPart n h)) •
          binaryStandardBasis n 0) := by
  set a : ℂ :=
    eval (![1, 0] : Fin 2 → ℂ) (TernaryPeriodPolynomials.Argument.evenPeriodPart n h) with ha_def
  set v : HomogeneousPoly n := -a • binaryStandardBasis n 0 with hv_def
  have hpoly : TernaryPeriodPolynomials.Argument.evenPeriodPart n h =
      C a * (X 0 ^ n - X 1 ^ n) := by
    have h0 := hzero
    rw [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, ← ha_def, sub_eq_zero] at h0
    exact h0
  have hv_poly : (v : Poly) = -(C a) * X 1 ^ n := by
    show -a • (binaryStandardBasis n 0 : Poly) = -(C a) * X 1 ^ n
    rw [binaryStandardBasis_zero_coe, MvPolynomial.smul_eq_C_mul, map_neg]
  have hTv : (modularBinaryRep n 0).ρ ModularGroup.T v = v := by
    apply Subtype.ext
    rw [modularBinaryRep_apply, hv_poly, substitute_castT_inv]
    simp [bind₁_X_right]
  have hSv : ((modularBinaryRep n 0).ρ ModularGroup.S v).1 = -(C a) * X 0 ^ n := by
    rw [modularBinaryRep_apply, hv_poly, substitute_castS_inv]
    simp [bind₁_X_right, hn.neg_pow]
  have hS : modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) ModularGroup.S =
      oneBoundaryCycle (modularBinaryRep n 0) v ModularGroup.S := by
    rw [cuspNormalizedBinaryCocycle_parity_S (by positivity : (0:ℤ) < (n:ℤ) + 2) h n rfl hn 0 0]
    apply Subtype.ext
    show -(binaryParityComponent n 0 (cuspPeriodPolynomial h n) : Poly) =
      ((modularBinaryRep n 0).ρ ModularGroup.S v).1 - (v : Poly)
    rw [cuspPeriodPolynomial_parityComponent_eq_evenPeriodPart hn h, hpoly, hSv, hv_poly]
    ring
  have hT0 : modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) ModularGroup.T =
      0 :=
    modularCocycleParity_T n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0)
      (cuspNormalizedBinaryCocycle_T (by positivity : (0:ℤ) < (n:ℤ) + 2) h n rfl 0)
  apply cocycle_ext (modularBinaryRep n 0) hS
  have hLHS : modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) modularOrderSix =
      modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) ModularGroup.S := by
    show modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0)
        (ModularGroup.S * ModularGroup.T) =
      modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0) ModularGroup.S
    rw [cocycle_mul (modularBinaryRep n 0)
      (modularCocycleParity n 0 0 (cuspNormalizedBinaryCocycle h n rfl 0))
      ModularGroup.S ModularGroup.T, hT0, map_zero, zero_add]
  have hRHS : oneBoundaryCycle (modularBinaryRep n 0) v modularOrderSix =
      oneBoundaryCycle (modularBinaryRep n 0) v ModularGroup.S := by
    have e1 := oneBoundaryCycle_apply (modularBinaryRep n 0) v modularOrderSix
    have e2 := oneBoundaryCycle_apply (modularBinaryRep n 0) v ModularGroup.S
    rw [e1, e2, show modularOrderSix = ModularGroup.S * ModularGroup.T from rfl,
      ← rho_rho (modularBinaryRep n 0) ModularGroup.S ModularGroup.T v, hTv]
  rw [hLHS, hRHS]
  exact hS

/-- Casting the `parity`/`sign` arguments of `classicalArithmeticCocycle` along a propositional
equality of parities leaves the cocycle unchanged (mirrors `classicalArithmeticCocycle_cast`,
which casts along the weight argument instead). -/
private theorem classicalArithmeticCocycle_parity_cast {degree : ℕ} {weight : ℤ}
    (form : CuspForm levelOne weight) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    {twist : ℤ} {parity₁ parity₂ : ℕ} (e : parity₁ = parity₂)
    (sign₁ : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity₁) :
    classicalArithmeticCocycle form degree weight_eq even twist parity₁ sign₁ =
      classicalArithmeticCocycle form degree weight_eq even twist parity₂ (e ▸ sign₁) := by
  subst e
  rfl

/-- **Steps (b)+(c) combined.** Vanishing of `normalizedEvenPeriodPart n h` forces the `H1π`-class
of `h`'s classical arithmetic cocycle to vanish. -/
theorem H1π_classicalArithmeticCocycle_eq_zero_of_normalizedEvenPeriodPart_eq_zero {n : ℕ}
    (hn : Even n) (h : CuspForm levelOne ((n : ℤ) + 2))
    (hzero : TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n h = 0) :
    groupCohomology.H1π (arithmeticBinaryRep n 0)
      (classicalArithmeticCocycle h n rfl hn 0 (parityOf (0 : ℤ)).val (parityOf_sign 0)) = 0 := by
  rw [classicalArithmeticCocycle_parity_cast h rfl hn parityOf_zero_val (parityOf_sign 0)]
  show groupCohomology.H1π (arithmeticBinaryRep n 0)
    (arithmeticParityCocycle n 0 hn 0 (parityOf_zero_val ▸ parityOf_sign 0)
      (classicalBinaryCocycle h n rfl 0)) = 0
  rw [arithmeticParityCocycle_H1_zero_iff n 0 hn 0 (parityOf_zero_val ▸ parityOf_sign 0)
    (classicalBinaryCocycle h n rfl 0), ← cuspNormalizedBinaryCocycle_parity_H1 h n rfl 0 0,
    modularCocycleParity_cuspNormalizedBinaryCocycle_eq_oneBoundaryCycle hn h hzero]
  exact oneBoundaryCycle_H1_zero _ _

/-- **Corollary 1.4, even-side injectivity.** For even `n > 0` and `h : CuspForm levelOne (n+2)`,
`normalizedEvenPeriodPart n h = 0 → h = 0`. -/
theorem normalizedEvenPeriodPart_injective {n : ℕ} (_hn0 : n ≠ 0) (hn : Even n)
    (h : CuspForm levelOne ((n : ℤ) + 2))
    (hzero : TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n h = 0) : h = 0 :=
  h_eq_zero_of_classicalArithmeticCocycle_H1_zero hn h
    (H1π_classicalArithmeticCocycle_eq_zero_of_normalizedEvenPeriodPart_eq_zero hn h hzero)

end TernaryPeriodPolynomials.Argument.Corollary14
