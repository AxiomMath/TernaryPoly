module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PrimeForwardRepresentatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspSmoothAction_mul (cusp : CuspidalRepresentation) (first second : BinaryAdelicGL) (vector : cusp.smooth) :
    cuspSmoothAction cusp (first * second) vector = cuspSmoothAction cusp first (cuspSmoothAction cusp second vector) := by
  apply Subtype.ext
  exact congrArg (fun operator : Module.End ℂ cusp.H => operator vector.val) (cusp.π.map_mul first second)

theorem cuspSmoothAction_scalar (cusp : CuspidalRepresentation) (unit : Adelesˣ) (vector : cusp.smooth) :
    cuspSmoothAction cusp (GeneralLinearGroup.scalar (Fin 2) unit) vector = cusp.centralCharacter unit • vector := by
  apply cusp.injective
  funext argument
  rw [cuspSmoothAction_realize, ← GeneralLinearGroup.scalar_commute, cusp.central, map_smul]
  rfl

theorem cuspSmoothAction_finite_spherical (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (matrix : BinaryFiniteGL)
    (integral : matrix ∈ finiteIntegralGLLevel 2) : cuspSmoothAction cusp (atFinite matrix) vector = vector := by
  obtain ⟨compact, rfl⟩ := integral
  exact Subtype.ext (spherical compact)

theorem binary_atFinite_scalar (unit : FiniteAdelesˣ) :
    atFinite (GeneralLinearGroup.scalar (Fin 2) unit) =
      GeneralLinearGroup.scalar (Fin 2) (finiteAdeleUnit unit) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, finiteAdeleUnit, GeneralLinearGroup.coe_scalar,
      Matrix.scalar]

theorem finiteAtPadicGL_reflection_integral (place : FinitePlace) :
    finiteAtPadicGL 2 place binaryPivotReflection ∈ finiteIntegralGLLevel 2 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have integral := finiteAtPadicGL_integral 2 place
    (binaryPivotReflection : GeneralLinearGroup (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
  rwa [binaryPivotReflection_map] at integral

theorem cuspLocalPadic_inverseHecke_sum (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∑ index : Option (Fin (Rat.HeightOneSpectrum.primesEquiv place).val),
      cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place (padicHeckeRepresentative index))⁻¹) vector) =
      cuspPrimeHeckeSum cusp (Rat.HeightOneSpectrum.primesEquiv place) vector := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  apply Subtype.ext
  rw [cuspPrimeHeckeSum_eq_sum]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro index _
  change cusp.π (atFinite (finiteAtPadicGL 2 place (padicHeckeRepresentative index))⁻¹) vector.val = _
  rw [← binaryHeckeLocalized_eq_padicRepresentative]
  exact cuspHeckeLocalized_eq cusp _ vector spherical index

theorem cuspLocalPadicPrimitiveOperator_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cuspLocalPadicPrimitiveOperator cusp place 1 vector =
      cusp.centralCharacter (finiteAdeleUnit (finiteAtPadicUnit place (padicPrimePowerUnit 1))) •
        cuspPrimeHeckeSum cusp (Rat.HeightOneSpectrum.primesEquiv place) vector := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have fixed : cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place binaryPivotReflection)) vector = vector :=
    cuspSmoothAction_finite_spherical cusp vector spherical _ (finiteAtPadicGL_reflection_integral place)
  have central (value : cusp.smooth) :
      cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place
        (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1)))) value =
        cusp.centralCharacter (finiteAdeleUnit (finiteAtPadicUnit place (padicPrimePowerUnit 1))) • value := by
    rw [finiteAtPadicGL_scalar, binary_atFinite_scalar, cuspSmoothAction_scalar]
  rw [cuspLocalPadicPrimitiveOperator, LinearMap.sum_apply,
    padicPrimitive_one_sum (fun matrix => cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place matrix)) vector)]
  simp_rw [padicPrimeForwardRepresentative_inverse_hecke, map_mul, map_inv, atFinite_mul, cuspSmoothAction_mul,
    fixed, central, map_smul]
  rw [← Finset.smul_sum, ← map_sum, cuspLocalPadic_inverseHecke_sum cusp vector spherical place]
  rw [cuspSmoothAction_finite_spherical cusp _ (cuspPrimeHeckeSum_spherical cusp _ vector spherical) _
    (finiteAtPadicGL_reflection_integral place)]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
