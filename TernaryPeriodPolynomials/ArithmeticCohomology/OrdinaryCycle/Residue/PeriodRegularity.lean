module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalLift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePole SinglePoleCoordinate SinglePoleSupport OrdinaryResidueGeneral
attribute [local instance] Classical.propDecidable

/-- Vanishing of actual principal parts is equivalent to being a polynomial, with no degree assumed on the witness. -/
theorem residue_zero_iff_polynomial (n : ℕ) (x : singlePole n) :
    residue n x = 0 ↔ ∃ p : SinglePole.Poly, SinglePole.embed p = x.val := by
  constructor
  · intro hx
    have hm : x ∈ (residue n).ker := hx
    rw [residue_exact] at hm
    obtain ⟨p,rfl⟩ := hm
    exact ⟨p.val,(polynomialInclusion_val n p).symm⟩
  · rintro ⟨q,hq⟩
    let p := SinglePole.representative n x
    have hp : presentationMap n p = SinglePole.embed q := (representative_spec n x).trans hq.symm
    change presentationResidues n p = 0
    apply DFinsupp.ext
    intro H
    change (numeratorRelations n H).mkQ (p.2 H) = 0
    by_cases hH : H ∈ p.2.support
    · apply (residueFiber_eq_zero_iff n H (p.2 H)).mpr
      apply normal_denominator_cancellation p.2.support (fun J => (p.2 J).val)
        (q-p.1.val) _ H hH
      rw [map_sub]
      rw [presentationMap_apply,polynomialMap_apply,poleSum_apply] at hp
      exact eq_sub_of_add_eq' hp
    · have hpH : p.2 H = 0 := by simpa only [DFinsupp.mem_support_iff,not_not] using hH
      rw [hpH,map_zero]

/-- The actual inverse-determinant order-three norm in the genuine single-pole module. -/
def norm (n : ℕ) (x : singlePole n) : singlePole n :=
  x + integralSinglePoleAction n (-1) ReferenceCoefficientMatrices.a x +
    integralSinglePoleAction n (-1) (ReferenceCoefficientMatrices.a^2) x

@[simp] theorem norm_val (n : ℕ) (x : singlePole n) :
    (norm n x).val = fractionNorm (-1) x.val := rfl

theorem residue_norm (n : ℕ) (x : singlePole n) :
    residue n (norm n x) = residue n x +
      integralResidueAction n (-1) ReferenceCoefficientMatrices.a (residue n x) +
      integralResidueAction n (-1) (ReferenceCoefficientMatrices.a^2) (residue n x) := by
  simp only [norm,map_add,←residue_integral_equivariant]

/-- The full binary norm follows from residue norm zero alone; a rational norm-zero lift is unnecessary. -/
theorem canonical_residue_norm_iff (n : ℕ) (q : BinaryV (n+1))
    (hq : OrdinaryResidueGeneral.SymmetricOdd q.val) :
    residue n (norm n (canonicalRepresentative n q)) = 0 ↔ SymmetricBinaryPeriodRelations q.val := by
  rw [residue_zero_iff_polynomial]
  simp only [norm_val,canonicalRepresentative_literal,fractionNorm_representative]
  exact representativeNorm_polynomial_iff q.val hq

end TernaryPoly.OrdinaryResiduePeriod
