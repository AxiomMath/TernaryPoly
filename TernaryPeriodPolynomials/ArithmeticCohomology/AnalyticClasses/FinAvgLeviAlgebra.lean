module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneCoordinateIndependence
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ThreeCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeReduction

@[expose] public section


/-!
# The finite good-line argument under the integral Levi

For an integral `GL₂` matrix `A` acting on the finite radical coordinates as a row vector,
`w⁻¹ n(f) γ_good = m(A) · w⁻¹ n(f A) γ_good · k(A)` with `m(A)` the plane Levi of `A` and `k(A)` an
integral matrix. Hence every finite plane coordinate system of the argument at `f A` transports to
one at `f`, with block multiplied on the left by `A`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The generic matrix identity behind the transport. -/
theorem finArg_levi_core {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R) (f1 f2 : R) :
    planeLevi A 1 * weyl⁻¹ *
        lineUnipotent (f1 * A.val 0 0 + f2 * A.val 1 0) (f1 * A.val 0 1 + f2 * A.val 1 1) =
      weyl⁻¹ * lineUnipotent f1 f2 * lineLevi 1 A := by
  apply Units.ext
  have hw : ((weyl : GL3 R)⁻¹).val = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl
  simp only [Units.val_mul, hw, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The row-vector action of an integral matrix on the finite radical coordinates. -/
def leviRowAction (A : GeneralLinearGroup (Fin 2) ℤ) (f : FiniteAwayThree × FiniteAwayThree) :
    FiniteAwayThree × FiniteAwayThree :=
  (A.val 0 0 • f.1 + A.val 1 0 • f.2, A.val 0 1 • f.1 + A.val 1 1 • f.2)

/-- The finite image of an integral matrix. -/
def finiteLeviMatrix (A : GeneralLinearGroup (Fin 2) ℤ) : BinaryFiniteGL :=
  GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) A

theorem leviRowAction_fst (A : GeneralLinearGroup (Fin 2) ℤ) (f : FiniteAwayThree × FiniteAwayThree) :
    ((leviRowAction A f).1 : FiniteAdeles) =
      f.1.val * (finiteLeviMatrix A).val 0 0 + f.2.val * (finiteLeviMatrix A).val 1 0 := by
  simp only [leviRowAction, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, zsmul_eq_mul, finiteLeviMatrix,
    GeneralLinearGroup.map_apply, eq_intCast]
  ring

theorem leviRowAction_snd (A : GeneralLinearGroup (Fin 2) ℤ) (f : FiniteAwayThree × FiniteAwayThree) :
    ((leviRowAction A f).2 : FiniteAdeles) =
      f.1.val * (finiteLeviMatrix A).val 0 1 + f.2.val * (finiteLeviMatrix A).val 1 1 := by
  simp only [leviRowAction, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, zsmul_eq_mul, finiteLeviMatrix,
    GeneralLinearGroup.map_apply, eq_intCast]
  ring

/-- The good-line permutation as an integral matrix. -/
def goodLineIntegerPermutation : GeneralLinearGroup (Fin 3) ℤ :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem rationalFinite_goodLine_eq :
    rationalFinite rationalGoodLine =
      GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) goodLineIntegerPermutation := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalFinite, rationalGoodLine, goodLineIntegerPermutation, GeneralLinearGroup.map_apply]

theorem map_lineLevi_one {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (A : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.map hom (lineLevi 1 A) = lineLevi 1 (GeneralLinearGroup.map hom A) := by
  apply Units.ext
  have h1 := lineLevi_val (1 : Sˣ) (GeneralLinearGroup.map hom A)
  ext row column
  rw [h1]
  change hom ((lineLevi 1 A).val row column) = _
  rw [lineLevi_val]
  fin_cases row <;> fin_cases column <;> simp [GeneralLinearGroup.map_apply]


/-- The integral compact factor of the transport. -/
def leviCompactInteger (A : GeneralLinearGroup (Fin 2) ℤ) : GeneralLinearGroup (Fin 3) ℤ :=
  goodLineIntegerPermutation⁻¹ * (lineLevi 1 A)⁻¹ * goodLineIntegerPermutation

/-- **The finite argument under the integral Levi.** -/
theorem standardGoodLineFiniteArgument_levi (A : GeneralLinearGroup (Fin 2) ℤ)
    (f : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteArgument f =
      planeLevi (finiteLeviMatrix A) 1 * standardGoodLineFiniteArgument (leviRowAction A f) *
        GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A) := by
  have core := finArg_levi_core (finiteLeviMatrix A) f.1.val f.2.val
  rw [← leviRowAction_fst, ← leviRowAction_snd] at core
  have hK : GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A) =
      (rationalFinite rationalGoodLine)⁻¹ * (lineLevi 1 (finiteLeviMatrix A))⁻¹ *
        rationalFinite rationalGoodLine := by
    rw [leviCompactInteger, map_mul, map_mul, map_inv, map_inv, map_lineLevi_one, ← rationalFinite_goodLine_eq]
    rfl
  rw [hK]
  unfold standardGoodLineFiniteArgument
  set G := rationalFinite rationalGoodLine
  have rearranged : weyl⁻¹ * lineUnipotent f.1.val f.2.val =
      planeLevi (finiteLeviMatrix A) 1 * weyl⁻¹ *
        lineUnipotent (leviRowAction A f).1.val (leviRowAction A f).2.val *
          (lineLevi 1 (finiteLeviMatrix A))⁻¹ := by
    rw [core, mul_inv_cancel_right]
  rw [rearranged]
  group

/-- The finite image of an integral matrix comes from the integral adeles. -/
theorem map_integralEmbedding_intCast {k : ℕ} (K : GeneralLinearGroup (Fin k) ℤ) :
    GeneralLinearGroup.map integralEmbedding (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) K) =
      GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) K := by
  apply Units.ext
  ext row column
  simp [GeneralLinearGroup.map_apply]

/-- **Transport of finite plane coordinates along the integral Levi.** -/
def transportCoordinates (A : GeneralLinearGroup (Fin 2) ℤ) (f : FiniteAwayThree × FiniteAwayThree)
    (coords : FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument (leviRowAction A f))) :
    FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument f) where
  first := (finiteLeviMatrix A).val 0 0 * coords.first + (finiteLeviMatrix A).val 0 1 * coords.second
  second := (finiteLeviMatrix A).val 1 0 * coords.first + (finiteLeviMatrix A).val 1 1 * coords.second
  scalar := coords.scalar
  block := finiteLeviMatrix A * coords.block
  compact := coords.compact * GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) (leviCompactInteger A)
  factorization := by
    have fac := coords.factorization
    rw [standardGoodLineFiniteArgument_levi A f, map_mul, map_integralEmbedding_intCast]
    conv_lhs => rw [fac]
    set B := finiteLeviMatrix A
    have hconj : planeLevi B 1 * planeUnipotent coords.first coords.second =
        planeUnipotent (B.val 0 0 * coords.first + B.val 0 1 * coords.second)
          (B.val 1 0 * coords.first + B.val 1 1 * coords.second) * planeLevi B 1 := by
      apply Units.ext
      apply Matrix.ext
      intro row column
      fin_cases row <;> fin_cases column <;>
        simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
    have hcomm : planeLevi B 1 * planeLevi 1 coords.scalar = planeLevi 1 coords.scalar * planeLevi B 1 := by
      have hleft := (planeLeviHom FiniteAdeles).map_mul (B, 1) (1, coords.scalar)
      have hright := (planeLeviHom FiniteAdeles).map_mul (1, coords.scalar) (B, 1)
      change planeLevi (B * 1) (1 * coords.scalar) = planeLevi B 1 * planeLevi 1 coords.scalar at hleft
      change planeLevi (1 * B) (coords.scalar * 1) = planeLevi 1 coords.scalar * planeLevi B 1 at hright
      simp only [mul_one, one_mul] at hleft hright
      exact hleft.symm.trans hright
    have hblock : planeLevi B 1 * planeLevi coords.block 1 = planeLevi (B * coords.block) 1 :=
      (planeLeviOneHom.map_mul B coords.block).symm
    calc planeLevi B 1 * (planeUnipotent coords.first coords.second *
          (planeLevi 1 coords.scalar * (planeLevi coords.block 1 *
            GeneralLinearGroup.map integralEmbedding coords.compact))) *
          GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A)
        = (planeLevi B 1 * planeUnipotent coords.first coords.second) *
          (planeLevi 1 coords.scalar * (planeLevi coords.block 1 *
            GeneralLinearGroup.map integralEmbedding coords.compact)) *
          GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A) := by group
      _ = planeUnipotent (B.val 0 0 * coords.first + B.val 0 1 * coords.second)
          (B.val 1 0 * coords.first + B.val 1 1 * coords.second) *
          ((planeLevi B 1 * planeLevi 1 coords.scalar) * (planeLevi coords.block 1 *
            GeneralLinearGroup.map integralEmbedding coords.compact)) *
          GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A) := by
        rw [hconj]; group
      _ = planeUnipotent (B.val 0 0 * coords.first + B.val 0 1 * coords.second)
          (B.val 1 0 * coords.first + B.val 1 1 * coords.second) *
          (planeLevi 1 coords.scalar * ((planeLevi B 1 * planeLevi coords.block 1) *
            (GeneralLinearGroup.map integralEmbedding coords.compact *
              GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (leviCompactInteger A)))) := by
        rw [hcomm]; group
      _ = _ := by rw [hblock]

end TernaryPeriodPolynomials.AnalyticClasses
