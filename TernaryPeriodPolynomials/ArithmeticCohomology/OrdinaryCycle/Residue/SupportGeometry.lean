module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportNormals

@[expose] public section

open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryResidueSupport
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness PrimitiveLineHeight

/-- Casting a literal integral row product commutes with rational matrix extension. -/
lemma rationalVector_vecMul (v : IntegralVector) (g : IntegralGL) :
    rationalVector (Matrix.vecMul v g.val)=
      Matrix.vecMul (rationalVector v) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g).val := by
  funext i
  simp [rationalVector,Matrix.vecMul,dotProduct,Matrix.GeneralLinearGroup.map_apply]

/-- The actual kernel of the transformed row is the inverse image of the original hyperplane. -/
lemma mem_hyperplane_rowAction (g : IntegralGL) (L : Normal) (x : Space) :
    x∈hyperplane (rowAction g L) ↔ rationalRepresentation g x∈hyperplane L := by
  obtain ⟨v,hv,rfl⟩ := exists_primitive_row L
  rw [rowAction_normalOfRow,mem_hyperplane_normalOfRow,mem_hyperplane_normalOfRow,
    rationalVector_vecMul,rationalRepresentation_apply,Matrix.dotProduct_mulVec]

lemma hyperplane_rowAction (g : IntegralGL) (L : Normal) :
    hyperplane (rowAction g L)=(hyperplane L).comap (rationalRepresentation g).toLinearMap := by
  ext x
  exact mem_hyperplane_rowAction g L x

/-- Primitive Bézout supplies a rational point where the normal functional is exactly one. -/
lemma exists_normalFunctional_eq_one (L : Normal) : ∃ x : Space, normalFunctional L x=1 := by
  obtain ⟨b,hb⟩ := primitive_bezout (primitiveGenerator_primitive L)
  refine ⟨rationalVector b,?_⟩
  change dotProduct (rationalVector (primitiveGenerator L)) (rationalVector b)=1
  rw [dotProduct_comm]
  change (∑ i, (b i : ℚ)*(primitiveGenerator L i : ℚ))=1
  exact_mod_cast hb

lemma normalFunctional_ne_zero (L : Normal) : normalFunctional L≠0 := by
  obtain ⟨x,hx⟩ := exists_normalFunctional_eq_one L
  intro h
  simp [h] at hx

/-- Normal-line indices are faithful: no two distinct indices define the same hyperplane. -/
theorem hyperplane_injective : Function.Injective hyperplane := by
  intro L K h
  obtain ⟨b,hb⟩ := exists_normalFunctional_eq_one L
  let q : ℚ := normalFunctional K b
  have he (x : Space) : normalFunctional K x=q*normalFunctional L x := by
    have hx : x-(normalFunctional L x) • b∈hyperplane L := by
      change normalFunctional L (x-(normalFunctional L x) • b)=0
      simp [map_sub,map_smul,hb]
    rw [h] at hx
    change normalFunctional K (x-(normalFunctional L x) • b)=0 at hx
    simpa [map_sub,map_smul,sub_eq_zero,mul_comm,q] using hx
  have hrow : rationalVector (primitiveGenerator K)=q • rationalVector (primitiveGenerator L) := by
    funext i
    have hi := he (Pi.single i 1)
    simpa [normalFunctional,dotProduct_single,rationalVector,mul_comm] using hi
  have hq : q≠0 := by
    intro hz
    apply primitiveGenerator_ne_zero K
    simpa [hz] using hrow
  apply Subtype.ext
  rw [← primitiveGenerator_span L,← primitiveGenerator_span K,hrow,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hq)]

end TernaryPoly.OrdinaryResidueSupport
