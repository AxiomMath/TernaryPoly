module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial

@[expose] public section


/-! Literal coefficientwise scalar extension of the rational homogeneous deck action. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpaceCovering IntegralGL3Congruence
open MvPolynomial Matrix

abbrev RationalCoefficients (n : ℕ) := PolynomialGLAction.HomogeneousPoly n

def scalarExtensionPolynomial : PolynomialGLAction.Poly →+* Poly := MvPolynomial.map (algebraMap ℚ ℝ)

theorem scalarExtension_substitute (A : Matrix (Fin 3) (Fin 3) ℚ) (p : PolynomialGLAction.Poly) :
    scalarExtensionPolynomial (PolynomialGLAction.substitute A p) =
      realSubstitute (A.map (algebraMap ℚ ℝ)) (scalarExtensionPolynomial p) := by
  simp [scalarExtensionPolynomial, PolynomialGLAction.substitute, realSubstitute, map_bind₁,
    PolynomialGLAction.linearForm]
  rfl

def rationalDeckMatrix : DeckGroup →* PolynomialGLAction.GL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp deckInclusion

theorem rationalDeckMatrix_real (g : DeckGroup) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (rationalDeckMatrix g) = deckMatrix g := by
  ext i j
  simp [rationalDeckMatrix, deckMatrix, SymmetricSpaceArithmeticProper.realIntegral]

def rationalDeckRepresentation (n : ℕ) (e : ℤ) : Representation ℚ DeckGroup (RationalCoefficients n) :=
  (PolynomialGLAction.integralAction n e).comp deckInclusion

def scalarExtensionCoefficient (n : ℕ) (p : RationalCoefficients n) : Coefficients n :=
  ⟨scalarExtensionPolynomial p.val, p.property.map (algebraMap ℚ ℝ)⟩

theorem scalarExtensionCoefficient_equivariant (n : ℕ) (e : ℤ) (g : DeckGroup)
    (p : RationalCoefficients n) :
    scalarExtensionCoefficient n (rationalDeckRepresentation n e g p) =
      deckRepresentation n g (scalarExtensionCoefficient n p) := by
  apply Subtype.ext
  change scalarExtensionPolynomial (PolynomialGLAction.action e (rationalDeckMatrix g) p.val) = _
  rw [show PolynomialGLAction.action e (rationalDeckMatrix g) =
    PolynomialGLAction.untwisted (rationalDeckMatrix g) from
      principalSix_action_eq_untwisted e (deckInclusion g) (deckInclusion_mem g)]
  change scalarExtensionPolynomial (PolynomialGLAction.substitute (↑(rationalDeckMatrix g)⁻¹) p.val) = _
  rw [scalarExtension_substitute]
  have hm : ((↑(rationalDeckMatrix g)⁻¹ : Matrix (Fin 3) (Fin 3) ℚ).map (algebraMap ℚ ℝ)) =
      (↑(deckMatrix g)⁻¹ : Mat) := by
    change (↑(GeneralLinearGroup.map (algebraMap ℚ ℝ) ((rationalDeckMatrix g)⁻¹)) : Mat) = _
    rw [map_inv, rationalDeckMatrix_real]
  rw [hm]
  rfl

def deckPrincipal : DeckGroup →* principalSix where
  toFun g := ⟨deckInclusion g, deckInclusion_mem g⟩
  map_one' := by apply Subtype.ext; exact map_one deckInclusion
  map_mul' g h := by apply Subtype.ext; exact map_mul deckInclusion g h

theorem rationalDeckRepresentation_literal (n : ℕ) (e : ℤ) :
    rationalDeckRepresentation n e =
      (SymmetricSpaceAllTopBoundary.polynomialCoefficients n e).ρ.comp deckPrincipal := rfl

def scalarExtensionLinear (n : ℕ) : RationalCoefficients n →ₗ[ℚ] Coefficients n where
  toFun := scalarExtensionCoefficient n
  map_add' p q := Subtype.ext (map_add scalarExtensionPolynomial p.val q.val)
  map_smul' r p := by
    apply Subtype.ext
    exact (MvPolynomial.mapAlgHom (Algebra.ofId ℚ ℝ)).toLinearMap.map_smul r p.val

@[simp] theorem scalarExtensionLinear_apply (n : ℕ) (p : RationalCoefficients n) :
    scalarExtensionLinear n p = scalarExtensionCoefficient n p := rfl

end TernaryPoly.PolynomialCoefficientMetric
