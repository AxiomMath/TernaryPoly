module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Cancellation
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section


open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePole
attribute [local instance] Classical.propDecidable

/-- Homogeneous polynomials inside their actual fraction field. -/
def polynomialMap (n : ℕ) : V n →ₗ[ℚ] Frac :=
  (IsScalarTower.toAlgHom ℚ Poly Frac).toLinearMap.comp (V n).subtype

@[simp] theorem polynomialMap_apply (n : ℕ) (p : V n) : polynomialMap n p = embed p.val := rfl

/-- One genuine simple-pole summand, with a chosen denominator representing its hyperplane. -/
def fractionMap (n : ℕ) (H : Normal) : V (n+1) →ₗ[ℚ] Frac where
  toFun p := polynomialMap (n+1) p / embed (denominator H)
  map_add' p q := by rw [map_add,add_div]
  map_smul' r p := by simp only [map_smul,smul_div_assoc,RingHom.id_apply]

@[simp] theorem fractionMap_apply (n : ℕ) (H : Normal) (p : V (n+1)) :
    fractionMap n H p = embed p.val / embed (denominator H) := rfl

/-- Numerator presentations have genuinely finite hyperplane support. -/
abbrev PoleTerms (n : ℕ) := ⨁ _H : Normal, V (n+1)
instance poleTermsAddCommGroup (n : ℕ) : AddCommGroup (PoleTerms n) :=
  inferInstanceAs (AddCommGroup (⨁ _H : Normal, V (n+1)))

instance poleTermsAddCommMonoid (n : ℕ) : AddCommMonoid (PoleTerms n) :=
  (poleTermsAddCommGroup n).toAddCommMonoid

instance poleTermsModule (n : ℕ) : Module ℚ (PoleTerms n) :=
  inferInstanceAs (Module ℚ (⨁ _H : Normal, V (n+1)))

abbrev Presentation (n : ℕ) := V n × PoleTerms n

def poleSum (n : ℕ) : PoleTerms n →ₗ[ℚ] Frac :=
  DirectSum.toModule ℚ Normal Frac (fractionMap n)

theorem poleSum_apply (n : ℕ) (p : PoleTerms n) :
    poleSum n p = ∑ H ∈ p.support, embed (p H).val / embed (denominator H) := by
  change DFinsupp.sumAddHom (fun H => (fractionMap n H).toAddMonoidHom) p = _
  rw [DFinsupp.sumAddHom_apply]
  rfl

/-- Evaluation is in the fraction field, not in a formal presentation quotient. -/
def presentationMap (n : ℕ) : Presentation n →ₗ[ℚ] Frac :=
  (polynomialMap n).coprod (poleSum n)

@[simp] theorem presentationMap_apply (n : ℕ) (p : Presentation n) :
    presentationMap n p = polynomialMap n p.1 + poleSum n p.2 := rfl

/-- The genuine single-pole coefficient module as a subspace of Q(x₀,x₁,x₂). -/
abbrev singlePole (n : ℕ) : Submodule ℚ Frac := (presentationMap n).range

/-- Every coefficient is a finite sum, by the literal image definition. -/
theorem mem_singlePole_iff (n : ℕ) (x : Frac) : x ∈ singlePole n ↔
    ∃ p : V n, ∃ t : PoleTerms n,
      x = embed p.val + ∑ H ∈ t.support, embed (t H).val / embed (denominator H) := by
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩
    refine ⟨p,t,?_⟩
    rw [presentationMap_apply,polynomialMap_apply,poleSum_apply]
  · rintro ⟨p,t,rfl⟩
    refine ⟨(p,t),?_⟩
    rw [presentationMap_apply,polynomialMap_apply,poleSum_apply]

def polynomialInclusion (n : ℕ) : V n →ₗ[ℚ] singlePole n :=
  (presentationMap n).rangeRestrict.comp (LinearMap.inl ℚ (V n) (PoleTerms n))

@[simp] theorem polynomialInclusion_val (n : ℕ) (p : V n) :
    (polynomialInclusion n p).val = embed p.val := by
  change polynomialMap n p + poleSum n 0 = embed p.val
  rw [map_zero,add_zero,polynomialMap_apply]

theorem polynomialInclusion_injective (n : ℕ) : Function.Injective (polynomialInclusion n) := by
  intro p q h
  apply Subtype.ext
  apply embed_injective
  simpa only [polynomialInclusion_val] using congrArg Subtype.val h

/-- Multiples of the actual normal form are precisely the regular numerator relations. -/
def multiplyDenominator (n : ℕ) (H : Normal) : V n →ₗ[ℚ] V (n+1) where
  toFun p := ⟨denominator H * p.val, by
    change (denominator H * p.val).IsHomogeneous (n+1)
    simpa only [Nat.add_comm 1 n] using (denominator_homogeneous H).mul p.property⟩
  map_add' p q := Subtype.ext (mul_add _ _ _)
  map_smul' r p := Subtype.ext (mul_smul_comm _ _ _)

def numeratorRelations (n : ℕ) (H : Normal) : Submodule ℚ (V (n+1)) :=
  (multiplyDenominator n H).range

/-- Principal-part fiber in the chosen normal-line trivialization. -/
abbrev ResidueFiber (n : ℕ) (H : Normal) := (V (n+1)) ⧸ numeratorRelations n H

instance residueFiberAddCommGroup (n : ℕ) (H : Normal) : AddCommGroup (ResidueFiber n H) :=
  Submodule.Quotient.addCommGroup (numeratorRelations n H)

/-- The finite-support hyperplane principal parts. -/
abbrev Residues (n : ℕ) := ⨁ H : Normal, ResidueFiber n H

instance residuesAddCommGroup (n : ℕ) : AddCommGroup (Residues n) :=
  inferInstanceAs (AddCommGroup (⨁ H : Normal, ResidueFiber n H))

instance residuesAddCommMonoid (n : ℕ) : AddCommMonoid (Residues n) :=
  (residuesAddCommGroup n).toAddCommMonoid

instance residuesModule (n : ℕ) : Module ℚ (Residues n) :=
  inferInstanceAs (Module ℚ (⨁ H : Normal, ResidueFiber n H))

def numeratorResidues (n : ℕ) : PoleTerms n →ₗ[ℚ] Residues n :=
  DirectSum.lmap (fun H => (numeratorRelations n H).mkQ)

@[simp] theorem numeratorResidues_apply (n : ℕ) (p : PoleTerms n) (H : Normal) :
    numeratorResidues n p H = (numeratorRelations n H).mkQ (p H) := rfl

def presentationResidues (n : ℕ) : Presentation n →ₗ[ℚ] Residues n :=
  (numeratorResidues n).comp (LinearMap.snd ℚ (V n) (PoleTerms n))

/-- Fiber vanishing means the denominator cancels in the exact homogeneous degree. -/
theorem residueFiber_eq_zero_iff (n : ℕ) (H : Normal) (p : V (n+1)) :
    (numeratorRelations n H).mkQ p = 0 ↔ denominator H ∣ p.val := by
  change Submodule.Quotient.mk p = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.val,rfl⟩
  · intro hd
    obtain ⟨q,hq⟩ := homogeneous_divisor (denominator_homogeneous H) p.property hd
    exact ⟨q,Subtype.ext hq⟩

/-- The finite direct sum maps onto the finite direct sum of quotient fibers. -/
theorem numeratorResidues_surjective (n : ℕ) : Function.Surjective (numeratorResidues n) :=
  (DirectSum.lmap_surjective _).mpr fun H => (numeratorRelations n H).mkQ_surjective

end TernaryPoly.SinglePole
