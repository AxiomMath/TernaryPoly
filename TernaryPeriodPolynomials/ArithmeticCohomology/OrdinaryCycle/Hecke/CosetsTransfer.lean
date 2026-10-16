module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsPrime

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeCosets
open CategoryTheory PolynomialGLAction OrdinaryHeckeArithmetic OrdinaryHeckeTransfer
open RationalCohomologyDescent

/-- Equality of the actual right cosets is exactly the conjugated-integrality relation. -/
theorem rightCoset_eq_iff {G : Type} [Group G] (Γ : Subgroup G) (g : G) (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) a)=
      Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) b ↔
        g⁻¹*b.val*a.val⁻¹*g ∈ Γ := by
  rw [Quotient.eq,QuotientGroup.rightRel_apply,mem_intersection]
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc]

/-- Same right transfer coset means equality of ambient prime representatives up to a right integral factor. -/
theorem rightCoset_eq_iff_factor {G : Type} [Group G] (Γ : Subgroup G) (g : G) (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) a)=
      Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) b ↔
        ∃ d : Γ, a.val⁻¹*g=b.val⁻¹*g*d.val := by
  rw [rightCoset_eq_iff]
  constructor
  · intro hd
    exact ⟨⟨g⁻¹*b.val*a.val⁻¹*g,hd⟩,by dsimp; group⟩
  · rintro ⟨d,hd⟩
    have he : g⁻¹*b.val*a.val⁻¹*g=d.val := by
      calc
        _ = (b.val⁻¹*g)⁻¹*(a.val⁻¹*g) := by group
        _ = (b.val⁻¹*g)⁻¹*((b.val⁻¹*g)*d.val) := by rw [hd]
        _ = d.val := by group
    rw [he]
    exact d.property

/-- Each Hecke summand is independent of the representative of the actual right coset. -/
theorem rightCoset_summand_eq {G : Type} [Group G] (Γ : Subgroup G) (g : G)
    (A : Rep ℚ G) (v : (Rep.res Γ.subtype A).ρ.invariants) (a b : Γ)
    (he : (Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) a)=
      Quotient.mk (QuotientGroup.rightRel (intersection Γ g)) b) :
    A.ρ (a.val⁻¹*g) v.val=A.ρ (b.val⁻¹*g) v.val := by
  have hd := (rightCoset_eq_iff Γ g a b).mp he
  have hv := (Representation.mem_invariants _ _).mp v.property ⟨_,hd⟩
  change A.ρ (g⁻¹*b.val*a.val⁻¹*g) v.val=v.val at hv
  have hg : a.val⁻¹*g=(b.val⁻¹*g)*(g⁻¹*b.val*a.val⁻¹*g) := by group
  rw [hg,map_mul,Module.End.mul_apply,hv]

instance primeIntersection_finiteIndex (p : ℕ) [Fact p.Prime] :
    (intersection Gamma (primeDiagonal p)).FiniteIndex := intersection_finiteIndex _

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The generic left-coefficient Hecke operator has this literal lower-triangular sum.
This is only the exact transfer convention; no right-homology or binary-Hecke normalization is asserted. -/
theorem hecke_prime_apply (p : ℕ) [Fact p.Prime] (A : Rep ℚ GL3)
    (v : (Rep.res Gamma.subtype A).ρ.invariants) :
    (hecke Gamma (primeDiagonal p) A v).val=
      ∑ i : PrimeIndex p, A.ρ (primeRepresentative p i) v.val := by
  rw [hecke_apply,←(prime_coset_equiv p).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hq : (Quotient.mk (QuotientGroup.rightRel (intersection Gamma (primeDiagonal p)))
      (primeCoset p i).out)=Quotient.mk _ (integralEquiv (chartLift i)) := Quotient.out_eq _
  have he := rightCoset_summand_eq Gamma (primeDiagonal p) A v
    (primeCoset p i).out (integralEquiv (chartLift i)) hq
  change A.ρ ((primeCoset p i).out.val⁻¹*primeDiagonal p) v.val=_
  rw [he,inverse_coset_normalization,map_mul,Module.End.mul_apply]
  have hv := (Representation.mem_invariants _ _).mp v.property
    ((integralEquiv (chartPermutation i))⁻¹)
  exact congrArg (A.ρ (primeRepresentative p i)) hv

end TernaryPoly.OrdinaryHeckeCosets
