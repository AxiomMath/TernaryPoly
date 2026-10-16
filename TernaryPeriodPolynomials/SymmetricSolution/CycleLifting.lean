module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Orbit.KernelLifting
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices
public import TernaryPeriodPolynomials.Building.Reference.ApartmentRelations
public import TernaryPeriodPolynomials.Building.Good.ChainComplex
public import TernaryPeriodPolynomials.Building.Good.OrbitCompleteness

@[expose] public section


/-! The exact period and swap equations give the actual cycle-map
reference relations. The actual incidence presentation now lifts them
unconditionally to cycle maps and genuine H2 classes. -/

noncomputable section
open CategoryTheory
namespace TernaryPoly.CycleLifting

open GoodBuilding GoodUnimodularOrbit GoodOrbitRelations
open ReferenceCoefficientMatrices
open PolynomialGLAction

/-- The determinant character gives the precise swap equation needed by the actual
homogeneous reference action, while the norm and cyclic equations are unchanged. -/
theorem referenceRelations_of_period_swap_character {n : ℕ} (e : ℤ)
    (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : (-1 : ℚ) ^ e • S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    OrbitKernelLifting.ReferenceRelations (GoodChainComplex.coefficientAction n e) f := by
  constructor
  · apply Subtype.ext
    have h := (ReferenceCoefficientMatrices.norm_iff e (f : TernaryPolynomial)).mp hf.2
    simp only [Submodule.coe_add, Submodule.coe_zero,
      ReferenceApartmentRelations.coefficientAction_coe, Subgroup.coe_pow]
    change (f : TernaryPolynomial) +
      ReferenceCoefficientMatrices.coefficientAction e a (f : TernaryPolynomial) +
      ReferenceCoefficientMatrices.coefficientAction e (a ^ 2) (f : TernaryPolynomial) = 0
    exact h
  · apply Subtype.ext
    rw [ReferenceApartmentRelations.coefficientAction_coe]
    exact (ReferenceCoefficientMatrices.cyclic_iff e (f : TernaryPolynomial)).mp hf.1
  · apply Subtype.ext
    rw [ReferenceApartmentRelations.coefficientAction_coe]
    change ReferenceCoefficientMatrices.coefficientAction e s (f : TernaryPolynomial) =
      -(f : TernaryPolynomial)
    rw [ReferenceCoefficientMatrices.coefficientAction_s]
    exact hswap

/-- Alternating solutions have the required reference relations for twist zero. -/
theorem alternating_referenceRelations {n : ℕ} (f : HomogeneousPoly n)
    (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    OrbitKernelLifting.ReferenceRelations (GoodChainComplex.coefficientAction n 0) f := by
  apply referenceRelations_of_period_swap_character 0 f hf
  simpa only [zpow_zero, one_smul] using hswap

/-- Symmetric solutions have the required reference relations for twist minus one. -/
theorem symmetric_referenceRelations {n : ℕ} (f : HomogeneousPoly n)
    (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) :
    OrbitKernelLifting.ReferenceRelations (GoodChainComplex.coefficientAction n (-1)) f := by
  apply referenceRelations_of_period_swap_character (-1) f hf
  rw [hswap]
  norm_num

/-- Actual cycle-map lift of an alternating homogeneous solution. -/
def alternatingCycleMap {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    GoodChainComplex.PolynomialCycleMap n 0 :=
  OrbitKernelLifting.polynomialCycleMap GoodOrbitCompleteness.complete f (alternating_referenceRelations f hf hswap)

/-- Actual cycle-map lift of a symmetric homogeneous solution. -/
def symmetricCycleMap {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) :
    GoodChainComplex.PolynomialCycleMap n (-1) :=
  OrbitKernelLifting.polynomialCycleMap GoodOrbitCompleteness.complete f (symmetric_referenceRelations f hf hswap)

@[simp] theorem alternatingCycleMap_reference {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    (alternatingCycleMap f hf hswap).map referenceApartment = f :=
  OrbitKernelLifting.polynomialCycleMap_reference GoodOrbitCompleteness.complete f
    (alternating_referenceRelations f hf hswap)

@[simp] theorem symmetricCycleMap_reference {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) :
    (symmetricCycleMap f hf hswap).map referenceApartment = f :=
  OrbitKernelLifting.polynomialCycleMap_reference GoodOrbitCompleteness.complete f
    (symmetric_referenceRelations f hf hswap)

/-- The alternating lift is unique from its reference value. -/
theorem alternatingCycleMap_existsUnique {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    ∃! F : GoodChainComplex.PolynomialCycleMap n 0, F.map referenceApartment = f :=
  OrbitKernelLifting.polynomialCycleMap_existsUnique GoodOrbitCompleteness.complete f
    (alternating_referenceRelations f hf hswap)

/-- The symmetric lift is unique from its reference value. -/
theorem symmetricCycleMap_existsUnique {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) :
    ∃! F : GoodChainComplex.PolynomialCycleMap n (-1), F.map referenceApartment = f :=
  OrbitKernelLifting.polynomialCycleMap_existsUnique GoodOrbitCompleteness.complete f
    (symmetric_referenceRelations f hf hswap)

/-- The actual H2 class associated to the alternating sector. -/
def alternatingPathClass {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) :
    groupCohomology.H2 (Rep.of (GoodChainComplex.coefficientAction n 0)) :=
  (alternatingCycleMap f hf hswap).pathClass

/-- The actual H2 class associated to the symmetric determinant-twisted sector. -/
def symmetricPathClass {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) :
    groupCohomology.H2 (Rep.of (GoodChainComplex.coefficientAction n (-1))) :=
  (symmetricCycleMap f hf hswap).pathClass

/-- The alternating class restricts to zero on every good-vertex stabilizer. -/
theorem alternatingPathClass_restrict_stabilizer_eq_zero
    {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = -(f : TernaryPolynomial)) (v : GoodVertex) :
    groupCohomology.map (MulAction.stabilizer K v).subtype
      (𝟙 (Rep.res (MulAction.stabilizer K v).subtype
        (Rep.of (GoodChainComplex.coefficientAction n 0)))) 2
      (alternatingPathClass f hf hswap) = 0 :=
  (alternatingCycleMap f hf hswap).restrict_stabilizer_eq_zero v

/-- The symmetric class restricts to zero on every good-vertex stabilizer. -/
theorem symmetricPathClass_restrict_stabilizer_eq_zero
    {n : ℕ} (f : HomogeneousPoly n) (hf : PeriodRelations (f : TernaryPolynomial))
    (hswap : S (f : TernaryPolynomial) = (f : TernaryPolynomial)) (v : GoodVertex) :
    groupCohomology.map (MulAction.stabilizer K v).subtype
      (𝟙 (Rep.res (MulAction.stabilizer K v).subtype
        (Rep.of (GoodChainComplex.coefficientAction n (-1))))) 2
      (symmetricPathClass f hf hswap) = 0 :=
  (symmetricCycleMap f hf hswap).restrict_stabilizer_eq_zero v

end TernaryPoly.CycleLifting
