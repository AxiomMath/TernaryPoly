module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootModule
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCommonRoot
open OrdinaryCovectors ModThreeGoodAction PolynomialGLAction

/-- The actual coinduced representation from the congruence subgroup. -/
abbrev Coinduced (n : ℕ) (e : ℤ) :=
  Representation.coindV K.subtype ((integralAction n e).comp K.subtype)

/-- The finite covector coefficient system is mapped to genuine equivariant functions on GL3(Z). -/
def toCoinduced (n : ℕ) (e : ℤ) : Coefficients n →ₗ[ℚ] Coinduced n e where
  toFun F := ⟨fun g => integralAction n e g (F (nonzeroRow g)), by
    intro k g
    have hr : nonzeroRow (k.val*g) = nonzeroRow g := Subtype.ext (row_left_K k g)
    change integralAction n e (k.val*g) (F (nonzeroRow (k.val*g))) =
      integralAction n e k.val (integralAction n e g (F (nonzeroRow g)))
    rw [hr, map_mul, Module.End.mul_apply]⟩
  map_add' F H := by apply Subtype.ext; funext g; exact map_add _ _ _
  map_smul' q F := by
    apply Subtype.ext
    funext g
    exact (integralAction n e g).map_smul q _

/-- Choose an actual integral representative of each of the 26 residue covectors. -/
def representative (r : NonzeroCovector) : IntegralGL :=
  (nonzeroRow_surjective r).choose

 theorem representative_row (r : NonzeroCovector) : nonzeroRow (representative r) = r :=
  (nonzeroRow_surjective r).choose_spec

/-- Inverse trivialization uses the literal inverse polynomial coefficient action. -/
def fromCoinduced (n : ℕ) (e : ℤ) : Coinduced n e →ₗ[ℚ] Coefficients n where
  toFun f r := integralAction n e (representative r)⁻¹ (f.val (representative r))
  map_add' f h := by funext r; exact map_add _ _ _
  map_smul' q f := by
    funext r
    exact (integralAction n e (representative r)⁻¹).map_smul q _

 theorem fromCoinduced_toCoinduced (n : ℕ) (e : ℤ) (F : Coefficients n) :
    fromCoinduced n e (toCoinduced n e F) = F := by
  funext r
  change integralAction n e (representative r)⁻¹
    (integralAction n e (representative r) (F (nonzeroRow (representative r)))) = F r
  rw [representative_row, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

 theorem toCoinduced_fromCoinduced (n : ℕ) (e : ℤ) (f : Coinduced n e) :
    toCoinduced n e (fromCoinduced n e f) = f := by
  apply Subtype.ext
  funext g
  have hr : row (representative (nonzeroRow g)) = row g :=
    congrArg Subtype.val (representative_row (nonzeroRow g))
  obtain ⟨k,hk⟩ := (row_eq_iff _ _).mp hr
  change integralAction n e g (integralAction n e (representative (nonzeroRow g))⁻¹
    (f.val (representative (nonzeroRow g)))) = f.val g
  rw [← Module.End.mul_apply, ← map_mul]
  have hm : g * (representative (nonzeroRow g))⁻¹ = k.val := by
    conv_lhs => lhs; rw [← hk]
    simp [mul_assoc]
  rw [hm]
  exact (f.property k (representative (nonzeroRow g))).symm.trans (congrArg f.val hk)

/-- An exact linear equivalence with actual subgroup coinduction, not an assumed coefficient model. -/
def coinducedEquiv (n : ℕ) (e : ℤ) : Coefficients n ≃ₗ[ℚ] Coinduced n e :=
  LinearEquiv.ofLinearMap (toCoinduced n e) (fromCoinduced n e)
    (by apply LinearMap.ext; intro f; exact toCoinduced_fromCoinduced n e f)
    (by apply LinearMap.ext; intro F; exact fromCoinduced_toCoinduced n e F)

 theorem toCoinduced_equivariant (n : ℕ) (e : ℤ) (g : IntegralGL) (F : Coefficients n) :
    toCoinduced n e (coefficientAction n e g F) =
      Representation.coind K.subtype ((integralAction n e).comp K.subtype) g
        (toCoinduced n e F) := by
  apply Subtype.ext
  funext h
  have hr : rowMove g (nonzeroRow h) = nonzeroRow (h*g) :=
    Subtype.ext (row_mul h g).symm
  change integralAction n e h (integralAction n e g (F (rowMove g (nonzeroRow h)))) =
    integralAction n e (h*g) (F (nonzeroRow (h*g)))
  rw [hr, map_mul, Module.End.mul_apply]

/-- Evaluation at the identity of the actual coinduced function is exactly the support-three fiber. -/
theorem toCoinduced_one (n : ℕ) (e : ℤ) (F : Coefficients n) :
    (toCoinduced n e F).val 1 = evaluation n F := by
  change integralAction n e 1 (F (nonzeroRow 1)) = _
  rw [map_one]
  rfl

end TernaryPoly.OrdinaryBoundaryCommonRoot
