module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveVanEst

@[expose] public section


/-!
# A primitive of the real good-line transfer on the radical

For a scalar form `F` with `EichlerData n F` and `n ≥ 5`, let `t` be the real good-line transfer
of the Eichler normal form. Fix an adelic point `h` and read the tests of `t` on the dual basis:
on radical pairs this gives a two-cocycle `T_h` of `ℝ²` with values in the coordinate space of
`Sym^n`, for the coefficient action of the radical. It is differentiable in its second variable,
its partial derivative at the origin of the second variable is `C¹`, and it vanishes when the
second argument is trivial. If the coinvariant part of the antisymmetrised mixed derivative
vanishes, the antisymmetrised mixed derivative is an infinitesimal coboundary, and the radial
van Est lemma produces a primitive. The primitive is built from `T_h` alone, so it is natural in
`h`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ}

/-! ### The radical action in coordinates -/

/-- Coordinates on `Sym^n` with respect to `homogeneousBasis n`. -/
abbrev RadicalCoordinates (n : ℕ) := Fin (Module.finrank ℂ (HomogeneousPoly n)) → ℂ

/-- The coefficient action of the radical element `e^Y`. -/
def radicalCoefficient (n : ℕ) (Y : Fin 2 → ℝ) : Module.End ℂ (HomogeneousPoly n) :=
  realCoefficientComponent n trivialCharacter (lineRadicalMatrix (Multiplicative.ofAdd Y))

theorem radicalCoefficient_add (Y Y' : Fin 2 → ℝ) :
    radicalCoefficient n (Y + Y') = radicalCoefficient n Y * radicalCoefficient n Y' := by
  unfold radicalCoefficient
  rw [ofAdd_add, map_mul, map_mul]

/-- The coefficient action of the radical in coordinates. -/
def radicalRep (n : ℕ) (Y : Fin 2 → ℝ) : RadicalCoordinates n →L[ℝ] RadicalCoordinates n :=
  (LinearMap.toContinuousLinearMap ((homogeneousBasis n).equivFun.toLinearMap ∘ₗ
    radicalCoefficient n Y ∘ₗ (homogeneousBasis n).equivFun.symm.toLinearMap)).restrictScalars ℝ

theorem radicalRep_apply (Y : Fin 2 → ℝ) (v : RadicalCoordinates n) :
    radicalRep n Y v = (homogeneousBasis n).equivFun
      (radicalCoefficient n Y ((homogeneousBasis n).equivFun.symm v)) := rfl

theorem equivFun_symm_radicalRep (Y : Fin 2 → ℝ) (v : RadicalCoordinates n) :
    (homogeneousBasis n).equivFun.symm (radicalRep n Y v) =
      radicalCoefficient n Y ((homogeneousBasis n).equivFun.symm v) := by
  rw [radicalRep_apply, LinearEquiv.symm_apply_apply]

theorem radicalRep_add (Y Y' : Fin 2 → ℝ) :
    radicalRep n (Y + Y') = (radicalRep n Y).comp (radicalRep n Y') := by
  ext v : 1
  rw [ContinuousLinearMap.comp_apply, radicalRep_apply, radicalRep_apply, radicalRep_apply,
    LinearEquiv.symm_apply_apply, radicalCoefficient_add, Module.End.mul_apply]

theorem contDiff_radicalRep : ContDiff ℝ 1 (radicalRep n) := by
  have inverse : ContDiff ℝ 1 (fun Y : Fin 2 → ℝ =>
      ((lineRadicalMatrix (Multiplicative.ofAdd Y))⁻¹).val) := by
    have equal : (fun Y : Fin 2 → ℝ => ((lineRadicalMatrix (Multiplicative.ofAdd Y))⁻¹).val) =
        fun Y => (lineMatrix (lineRadicalElement (-Y))).val := by
      funext Y
      rw [lineMatrix_lineRadicalElement, ofAdd_neg, map_inv]
    rw [equal]
    exact contDiff_lineMatrix_radical.comp contDiff_neg
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_pi]
  intro k
  exact contDiff_functional_realCoefficient _ inverse _ ((homogeneousBasis n).coord k)

theorem fderiv_radicalRep_apply (i : Fin 2) (v : RadicalCoordinates n) :
    fderiv ℝ (radicalRep n) 0 (Pi.single i 1) v = (homogeneousBasis n).equivFun
      (lowerShear n i ((homogeneousBasis n).equivFun.symm v)) := by
  have differentiable : DifferentiableAt ℝ (radicalRep n) 0 :=
    contDiff_radicalRep.differentiable one_ne_zero 0
  have applied : fderiv ℝ (fun Y => radicalRep n Y v) 0 = (fderiv ℝ (radicalRep n) 0).flip v := by
    rw [fderiv_clm_apply differentiable (differentiableAt_const v)]
    simp
  have outer : HasFDerivAt (fun Y => radicalRep n Y v) ((fderiv ℝ (radicalRep n) 0).flip v) 0 := by
    rw [← applied]
    exact ((contDiff_clm_apply_iff.mp contDiff_radicalRep v).differentiable one_ne_zero
      0).hasFDerivAt
  have line : HasDerivAt (fun s : ℝ => s • (Pi.single i 1 : Fin 2 → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 2 → ℝ)
  have axis : HasDerivAt (fun s : ℝ => radicalRep n (s • Pi.single i 1) v)
      ((homogeneousBasis n).equivFun
        (lowerShear n i ((homogeneousBasis n).equivFun.symm v))) 0 :=
    hasDerivAt_pi.mpr fun k => hasDerivAt_coefficient_lowerAxis ((homogeneousBasis n).coord k)
      _ i
  have unique := (outer.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)).unique axis
  rw [← unique]
  rfl

/-! ### The transfer on radical pairs in coordinates -/

/-- The tests of a two-cochain on radical pairs, read on the dual basis at the point `h`. -/
def radicalTransferVector (t : LineGroup → LineGroup → LineValues n) (h : BinaryAdelicGL)
    (p : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : RadicalCoordinates n :=
  fun k => t (lineRadicalElement p.1) (lineRadicalElement p.2) (h, (homogeneousBasis n).coord k)

theorem lineVector_eq_equivFun_symm (t : LineGroup → LineGroup → LineValues n)
    (h : BinaryAdelicGL) (Y Y' : Fin 2 → ℝ) :
    lineVector (t (lineRadicalElement Y) (lineRadicalElement Y')) h =
      (homogeneousBasis n).equivFun.symm (radicalTransferVector t h (Y, Y')) := by
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem radicalTransferVector_eichlerNormal (h : BinaryAdelicGL) :
    radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h =
      fun p k => radicalTransfer (eichlerNormal n F) h ((homogeneousBasis n).coord k) p.1 p.2 := by
  funext p k
  exact lineTransferCochain_radical_eq _ p.1 p.2 h _

theorem radicalTransferVector_cocycle {t : LineGroup → LineGroup → LineValues n}
    (cocycle : IsTwoCocycle t) (linear : ∀ a b, LinearTests (t a b)) (h : BinaryAdelicGL)
    (a b c : Fin 2 → ℝ) :
    radicalRep n a (radicalTransferVector t h (b, c)) - radicalTransferVector t h (a + b, c) +
      radicalTransferVector t h (a, b + c) - radicalTransferVector t h (a, b) = 0 := by
  have add (Y Y' : Fin 2 → ℝ) :
      lineRadicalElement Y * lineRadicalElement Y' = lineRadicalElement (Y + Y') :=
    (map_mul SemidirectProduct.inl (Multiplicative.ofAdd Y) (Multiplicative.ofAdd Y')).symm
  funext k
  have e := congrFun (cocycle (lineRadicalElement a) (lineRadicalElement b)
    (lineRadicalElement c)) (h, (homogeneousBasis n).coord k)
  rw [add, add] at e
  change (lineRadicalElement a • t (lineRadicalElement b) (lineRadicalElement c))
      (h, (homogeneousBasis n).coord k) - _ + _ - _ = (0 : ℂ) at e
  rw [lineRadical_smul_apply, linear, LinearMap.comp_apply, lineVector_eq_equivFun_symm] at e
  exact e

theorem radicalTransferVector_zero (h : BinaryAdelicGL) (a : Fin 2 → ℝ) :
    radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, 0) = 0 := by
  have trivial : lineRadicalElement (0 : Fin 2 → ℝ) = lineLeviElement 1 := by
    rw [lineRadicalElement, lineLeviElement, ofAdd_zero, map_one, map_one]
  have orthogonal : IsOrthogonalLevi (1 : unimodularLevi) := by
    simp [IsOrthogonalLevi]
  funext k
  change lineTransferCochain (eichlerNormal n F) (lineRadicalElement a)
    (lineRadicalElement 0) (h, (homogeneousBasis n).coord k) = 0
  rw [trivial, lineTransferCochain_orthogonal_right _ _ orthogonal]
  rfl

/-! ### Regularity of the transfer on radical pairs -/

theorem differentiable_radicalTransferVector (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (a : Fin 2 → ℝ) :
    Differentiable ℝ
      (fun c => radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, c)) := by
  rw [radicalTransferVector_eichlerNormal]
  exact differentiable_pi.mpr fun k => differentiable_radicalTransfer large hF h _ a

theorem fderiv_radicalTransferVector_single (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (a : Fin 2 → ℝ) (j : Fin 2) :
    fderiv ℝ (fun c => radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, c)) 0
      (Pi.single j 1) = fun k => radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) j a := by
  rw [radicalTransferVector_eichlerNormal]
  change fderiv ℝ (fun c k => radicalTransfer (eichlerNormal n F) h
    ((homogeneousBasis n).coord k) a c) 0 (Pi.single j 1) = _
  rw [fderiv_pi fun k => differentiable_radicalTransfer large hF h _ a 0]
  funext k
  exact fderiv_radicalTransfer_apply large hF h _ j a

theorem decompose_plane (y : Fin 2 → ℝ) : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp

theorem fderiv_radicalTransferVector_apply (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (a y : Fin 2 → ℝ) :
    fderiv ℝ (fun c => radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, c)) 0
      y = y 0 • (fun k => radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) 0 a) +
        y 1 • (fun k => radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) 1 a) := by
  conv_lhs => rw [decompose_plane y]
  rw [map_add, map_smul, map_smul, fderiv_radicalTransferVector_single large hF,
    fderiv_radicalTransferVector_single large hF]

theorem contDiff_partial_radicalTransferVector (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) :
    ContDiff ℝ 1 (fun a => fderiv ℝ
      (fun b => radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, b)) 0) := by
  rw [contDiff_clm_apply_iff]
  intro y
  simp only [fderiv_radicalTransferVector_apply large hF]
  have slope (j : Fin 2) : ContDiff ℝ 1 (fun a => fun k =>
      radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) j a) :=
    contDiff_pi.mpr fun k => contDiff_radicalSlopeIntegral large hF h _ j
  exact ((contDiff_const (c := y 0)).smul (slope 0)).add ((contDiff_const (c := y 1)).smul
    (slope 1))

theorem fderiv_mixed_radicalTransferVector (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (i j : Fin 2) :
    fderiv ℝ (fun a => fderiv ℝ (fun b =>
      radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, b)) 0
        (Pi.single j 1)) 0 (Pi.single i 1) =
      fun k => ∫ u, radicalMixed (eichlerNormal n F) u i j h ((homogeneousBasis n).coord k)
        ∂((volume : Measure ℝ).prod volume) := by
  simp only [fderiv_radicalTransferVector_single large hF]
  rw [fderiv_pi fun k => (contDiff_radicalSlopeIntegral large hF h _ j).differentiable
    one_ne_zero 0]
  funext k
  exact fderiv_radicalSlopeIntegral_apply large hF i j h _

/-- Tests of the integrated mixed derivative are linear in the test. -/
theorem integral_radicalMixed_eq_sum (large : 5 ≤ n) (hF : EichlerData n F) (i j : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∫ u, radicalMixed (eichlerNormal n F) u i j h functional ∂((volume : Measure ℝ).prod volume) =
      ∑ k, (∫ u, radicalMixed (eichlerNormal n F) u i j h ((homogeneousBasis n).coord k)
        ∂((volume : Measure ℝ).prod volume)) * functional (homogeneousBasis n k) := by
  have transfer (x b : Fin 2 → ℝ) : radicalTransfer (eichlerNormal n F) h functional x b =
      ∑ k, radicalTransfer (eichlerNormal n F) h ((homogeneousBasis n).coord k) x b *
        functional (homogeneousBasis n k) := by
    rw [← lineTransferCochain_radical_eq, lineTransferCochain_linear large hF,
      functional_lineVector]
    simp only [lineTransferCochain_radical_eq]
  have slope (x : Fin 2 → ℝ) : radicalSlopeIntegral n F h functional j x =
      ∑ k, radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) j x *
        functional (homogeneousBasis n k) := by
    rw [← fderiv_radicalTransfer_apply large hF h functional j x]
    have sum : HasFDerivAt (fun b => radicalTransfer (eichlerNormal n F) h functional x b)
        (∑ k, functional (homogeneousBasis n k) • fderiv ℝ (fun b =>
          radicalTransfer (eichlerNormal n F) h ((homogeneousBasis n).coord k) x b) 0) 0 := by
      rw [show (fun b => radicalTransfer (eichlerNormal n F) h functional x b) = fun b =>
        ∑ k, radicalTransfer (eichlerNormal n F) h ((homogeneousBasis n).coord k) x b *
          functional (homogeneousBasis n k) from funext (transfer x)]
      exact HasFDerivAt.fun_sum fun k _ =>
        (differentiable_radicalTransfer large hF h _ x 0).hasFDerivAt.mul_const _
    rw [sum.fderiv, _root_.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_apply, fderiv_radicalTransfer_apply large hF, smul_eq_mul,
      mul_comm]
  rw [← fderiv_radicalSlopeIntegral_apply large hF i j h functional]
  have sum : HasFDerivAt (radicalSlopeIntegral n F h functional j)
      (∑ k, functional (homogeneousBasis n k) •
        fderiv ℝ (radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) j) 0) 0 := by
    rw [show radicalSlopeIntegral n F h functional j = fun x =>
      ∑ k, radicalSlopeIntegral n F h ((homogeneousBasis n).coord k) j x *
        functional (homogeneousBasis n k) from funext slope]
    exact HasFDerivAt.fun_sum fun k _ => (((contDiff_radicalSlopeIntegral large hF h _
      j).differentiable one_ne_zero 0).hasFDerivAt).mul_const _
  rw [sum.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.smul_apply, fderiv_radicalSlopeIntegral_apply large hF, smul_eq_mul,
    mul_comm]

/-! ### The Lie condition -/

/-- The antisymmetrised mixed derivative at the origin of a two-cochain of the plane. -/
def lieVector (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → RadicalCoordinates n) : RadicalCoordinates n :=
  fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 1 1)) 0 (Pi.single 0 1) -
    fderiv ℝ (fun a => fderiv ℝ (fun b => T (a, b)) 0 (Pi.single 0 1)) 0 (Pi.single 1 1)

theorem topCoefficient_lieVector (large : 5 ≤ n) (hF : EichlerData n F)
    (lie : ∀ h, ∫ u, radicalObstruction (eichlerNormal n F) u h
      ∂((volume : Measure ℝ).prod volume) = 0) (h : BinaryAdelicGL) :
    topCoefficient n ((homogeneousBasis n).equivFun.symm
      (lieVector (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h))) = 0 := by
  unfold lieVector
  rw [fderiv_mixed_radicalTransferVector large hF, fderiv_mixed_radicalTransferVector large hF,
    Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [← integral_radicalMixed_eq_sum large hF, ← integral_radicalMixed_eq_sum large hF,
    ← integral_sub (integrable_radicalMixed large hF 0 1 h _)
      (integrable_radicalMixed large hF 1 0 h _)]
  exact lie h

/-- A preimage under the Lie-algebra coboundary, chosen as a function of the target only. -/
def lieSolution (ω : HomogeneousPoly n) : HomogeneousPoly n × HomogeneousPoly n :=
  Classical.epsilon fun p => lieBoundary n p = ω

/-- The linear map `η` of the radial van Est lemma attached to a two-cochain. -/
def lieEta (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → RadicalCoordinates n) :
    (Fin 2 → ℝ) →L[ℝ] RadicalCoordinates n :=
  (ContinuousLinearMap.proj 0).smulRight ((homogeneousBasis n).equivFun
      (lieSolution ((homogeneousBasis n).equivFun.symm (lieVector T))).1) +
    (ContinuousLinearMap.proj 1).smulRight ((homogeneousBasis n).equivFun
      (lieSolution ((homogeneousBasis n).equivFun.symm (lieVector T))).2)

theorem lieEta_lie (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → RadicalCoordinates n)
    (top : topCoefficient n ((homogeneousBasis n).equivFun.symm (lieVector T)) = 0) :
    fderiv ℝ (radicalRep n) 0 (Pi.single 0 1) (lieEta T (Pi.single 1 1)) -
      fderiv ℝ (radicalRep n) 0 (Pi.single 1 1) (lieEta T (Pi.single 0 1)) = lieVector T := by
  set ω := (homogeneousBasis n).equivFun.symm (lieVector T)
  have spec : lieBoundary n (lieSolution ω) = ω :=
    Classical.epsilon_spec (exists_lieBoundary_eq ω top)
  have first : lieEta T (Pi.single 1 1) = (homogeneousBasis n).equivFun (lieSolution ω).2 := by
    simp [lieEta, ω]
  have zeroth : lieEta T (Pi.single 0 1) = (homogeneousBasis n).equivFun (lieSolution ω).1 := by
    simp [lieEta, ω]
  rw [first, zeroth, fderiv_radicalRep_apply, fderiv_radicalRep_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, ← map_sub, ← lieBoundary_apply,
    spec, LinearEquiv.apply_symm_apply]

/-! ### The primitive -/

/-- The radial primitive of a two-cochain of the plane in coordinates. -/
def radicalPrimitiveOf (T : (Fin 2 → ℝ) × (Fin 2 → ℝ) → RadicalCoordinates n) :
    (Fin 2 → ℝ) → RadicalCoordinates n :=
  radialPrimitive (radicalRep n) T (lieEta T)

/-- **The radical primitive** of a two-cochain of the real good-line stabilizer, as scalar
tests: at the point `h` it is the radial primitive of the tests of the cochain at `h`. -/
def radicalPrimitiveTests (t : LineGroup → LineGroup → LineValues n) (Y : Fin 2 → ℝ) :
    LineValues n :=
  fun p => p.2 ((homogeneousBasis n).equivFun.symm
    (radicalPrimitiveOf (radicalTransferVector t p.1) Y))

theorem radicalPrimitiveOf_spec (large : 5 ≤ n) (hF : EichlerData n F)
    (lie : ∀ h, ∫ u, radicalObstruction (eichlerNormal n F) u h
      ∂((volume : Measure ℝ).prod volume) = 0) (h : BinaryAdelicGL) :
    (∀ a b, radicalRep n a (radicalPrimitiveOf
        (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h) b) -
      radicalPrimitiveOf (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h)
        (a + b) +
      radicalPrimitiveOf (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h) a =
        radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h (a, b)) ∧
    Differentiable ℝ
      (radicalPrimitiveOf (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h)) :=
  boundary_radialPrimitive_of_partial_plane (radicalRep n) _ _ contDiff_radicalRep radicalRep_add
    (differentiable_radicalTransferVector large hF h)
    (contDiff_partial_radicalTransferVector large hF h)
    (radicalTransferVector_cocycle (lineTransfer_isTwoCocycle large hF.pointCocycle)
      (lineTransferCochain_linear large hF) h) (radicalTransferVector_zero h)
    (lieEta_lie _ (topCoefficient_lieVector large hF lie h))

/-- **A primitive of the real good-line transfer on the radical.** If the coinvariant part of
the antisymmetrised mixed derivative of the transfer at the origin vanishes, the transfer is, on
radical pairs, the coboundary of a family of linear tests that is differentiable at the origin
and depends at each point `h` only on the tests of the transfer at `h`. -/
theorem exists_radicalPrimitive (large : 5 ≤ n) (hF : EichlerData n F)
    (lie : ∀ h, ∫ u, radicalObstruction (eichlerNormal n F) u h
      ∂((volume : Measure ℝ).prod volume) = 0) :
    ∃ a : (Fin 2 → ℝ) → LineValues n,
      (∀ Y, LinearTests (a Y)) ∧
      (∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0) ∧
      (∀ Y Y', lineTransferCochain (eichlerNormal n F) (lineRadicalElement Y)
          (lineRadicalElement Y') = lineRadicalElement Y • a Y' - a (Y + Y') + a Y) ∧
      (∀ h h', (∀ Y Y' ℓ, lineTransferCochain (eichlerNormal n F) (lineRadicalElement Y)
          (lineRadicalElement Y') (h, ℓ) = lineTransferCochain (eichlerNormal n F)
            (lineRadicalElement Y) (lineRadicalElement Y') (h', ℓ)) →
        ∀ Y ℓ, a Y (h, ℓ) = a Y (h', ℓ)) := by
  refine ⟨radicalPrimitiveTests (lineTransferCochain (eichlerNormal n F)), fun Y => ?_,
    fun p => ?_, fun Y Y' => ?_, fun h h' same Y ℓ => ?_⟩
  · intro h functional
    exact (congrArg functional (lineVector_vector (fun h => (homogeneousBasis n).equivFun.symm
      (radicalPrimitiveOf (radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h)
        Y)) h)).symm
  · set L : RadicalCoordinates n →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap
      (p.2 ∘ₗ (homogeneousBasis n).equivFun.symm.toLinearMap)).restrictScalars ℝ
    exact L.differentiableAt.comp (0 : Fin 2 → ℝ) ((radicalPrimitiveOf_spec large hF lie p.1).2 0)
  · funext p
    obtain ⟨h, functional⟩ := p
    have boundary := (radicalPrimitiveOf_spec large hF lie h).1 Y Y'
    change lineTransferCochain (eichlerNormal n F) _ _ (h, functional) =
      (lineRadicalElement Y • radicalPrimitiveTests (lineTransferCochain (eichlerNormal n F)) Y')
        (h, functional) - radicalPrimitiveTests (lineTransferCochain (eichlerNormal n F)) (Y + Y')
          (h, functional) + radicalPrimitiveTests (lineTransferCochain (eichlerNormal n F)) Y
            (h, functional)
    rw [lineTransferCochain_linear large hF, lineVector_eq_equivFun_symm, lineRadical_smul_apply]
    unfold radicalPrimitiveTests
    rw [LinearMap.comp_apply, ← boundary, map_add, map_sub, equivFun_symm_radicalRep, map_add,
      map_sub]
    rfl
  · have equal : radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h =
        radicalTransferVector (lineTransferCochain (eichlerNormal n F)) h' := by
      funext q k
      exact same q.1 q.2 _
    unfold radicalPrimitiveTests
    dsimp only
    rw [equal]

end TernaryPeriodPolynomials.AnalyticClasses
