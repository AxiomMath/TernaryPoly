module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Action
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

open MvPolynomial Matrix
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePole
open PolynomialGLAction
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
attribute [local instance] Classical.propDecidable

/-- A surjective linear map with invariant kernel transports the genuine quotient representation. -/
def surjectiveQuotientAction {A B G : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℚ A] [Module ℚ B] [Monoid G]
    (f : A →ₗ[ℚ] B) (hf : Function.Surjective f) (ρ : Representation ℚ G A)
    (h : ∀ g, f.ker ≤ f.ker.comap (ρ g)) : Representation ℚ G B :=
  (f.quotKerEquivOfSurjective hf).conjRingEquiv.toMonoidHom.comp (ρ.quotient f.ker h)

theorem surjectiveQuotientAction_apply {A B G : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℚ A] [Module ℚ B] [Monoid G]
    (f : A →ₗ[ℚ] B) (hf : Function.Surjective f) (ρ : Representation ℚ G A)
    (h : ∀ g, f.ker ≤ f.ker.comap (ρ g)) (g : G) (x : A) :
    surjectiveQuotientAction f hf ρ h g (f x) = f (ρ g x) := by
  change f.quotKerEquivOfSurjective hf
    (Submodule.mapQ _ _ (ρ g) (h g) ((f.quotKerEquivOfSurjective hf).symm (f x))) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk f hf (ρ g x)

/-- The proved polynomial kernel is invariant under actual inverse substitution. -/
theorem residue_kernel_invariant (n : ℕ) (e : ℤ) (g : GL3) :
    (residue n).ker ≤ (residue n).ker.comap (singlePoleAction n e g) := by
  intro x hx
  rw [residue_exact] at hx
  obtain ⟨p,rfl⟩ := hx
  change residue n (singlePoleAction n e g (polynomialInclusion n p)) = 0
  rw [polynomialInclusion_equivariant,residue_polynomial]

/-- Principal parts inherit the actual coefficient action through the proved exact residue map. -/
def residueAction (n : ℕ) (e : ℤ) : Representation ℚ GL3 (Residues n) :=
  surjectiveQuotientAction (residue n) (residue_surjective n) (singlePoleAction n e)
    (residue_kernel_invariant n e)

/-- Equivariance is a theorem about the constructed rational-function and principal-part actions. -/
theorem residue_equivariant (n : ℕ) (e : ℤ) (g : GL3) (x : singlePole n) :
    residueAction n e g (residue n x) = residue n (singlePoleAction n e g x) :=
  surjectiveQuotientAction_apply (residue n) (residue_surjective n) (singlePoleAction n e)
    (residue_kernel_invariant n e) g x

/-- The transported numerator includes the determinant character and inverse denominator scalar. -/
def transformedNumerator (n : ℕ) (e : ℤ) (g : GL3) (c : ℚ) (p : V (n+1)) : V (n+1) :=
  determinantCharacter e g • c⁻¹ •
    (⟨substitute (g⁻¹ : GL3) p.val,substitute_homogeneous _ p.property⟩ : V (n+1))

/-- Literal transformation of a single fraction after choosing its new normal denominator. -/
theorem singlePoleAction_simplePole (n : ℕ) (e : ℤ) (g : GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : GL3) (denominator H) = C c * denominator J) (p : V (n+1)) :
    singlePoleAction n e g (simplePole n H p) =
      simplePole n J (transformedNumerator n e g c p) := by
  apply Subtype.ext
  simp only [singlePoleAction_val,simplePole_val,fractionMap_apply]
  change determinantCharacter e g • fractionEquiv g
    (embed p.val / embed (denominator H)) = _
  rw [map_div₀,fractionEquiv_embed,fractionEquiv_embed,hc,divide_scaled_form]
  rw [← smul_div_assoc]
  congr 1
  exact (IsScalarTower.toAlgHom ℚ Poly Frac).toLinearMap.map_smul _ _ |>.symm

/-- Explicit principal-part transformation: normal transport and inverse scaling are literal. -/
theorem residueAction_lof (n : ℕ) (e : ℤ) (g : GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : GL3) (denominator H) = C c * denominator J) (p : V (n+1)) :
    residueAction n e g
      (DirectSum.lof ℚ Normal (ResidueFiber n) H ((numeratorRelations n H).mkQ p)) =
    DirectSum.lof ℚ Normal (ResidueFiber n) J
      ((numeratorRelations n J).mkQ (transformedNumerator n e g c p)) := by
  rw [← residue_simplePole,residue_equivariant,singlePoleAction_simplePole n e g H J c hc,
    residue_simplePole]

/-- Every transformed normal has the required representative and a nonzero denominator scalar. -/
theorem transformed_denominator_exists (g : GL3) (H : Normal) :
    ∃ J : Normal, ∃ c : ℚ, c ≠ 0 ∧
      substitute (g⁻¹ : GL3) (denominator H) = C c * denominator J := by
  let v := vecMul (rationalVector (primitiveGenerator H))
    (↑(g⁻¹) : Matrix (Fin 3) (Fin 3) ℚ)
  have hv : v ≠ 0 := vecMul_inv_ne_zero g _ (primitiveGenerator_ne_zero H)
  obtain ⟨c,hc,he⟩ := form_scalar_denominator v hv
  refine ⟨vectorLine v hv,c,hc,?_⟩
  change substitute (g⁻¹ : GL3) (form _) = _
  rw [substitute_form]
  exact he

/-- The exact sequence with both endpoint properties and both actual equivariance identities. -/
theorem equivariant_residue_short_exact (n : ℕ) (e : ℤ) :
    Function.Injective (polynomialInclusion n) ∧
    (residue n).ker = (polynomialInclusion n).range ∧
    Function.Surjective (residue n) ∧
    (∀ g p, singlePoleAction n e g (polynomialInclusion n p) =
      polynomialInclusion n (homogeneousAction n e g p)) ∧
    (∀ g x, residueAction n e g (residue n x) = residue n (singlePoleAction n e g x)) :=
  ⟨polynomialInclusion_injective n,residue_exact n,residue_surjective n,
    polynomialInclusion_equivariant n e,residue_equivariant n e⟩

end TernaryPoly.SinglePole
