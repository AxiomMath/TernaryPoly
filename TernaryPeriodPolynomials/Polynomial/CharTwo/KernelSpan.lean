module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.ProjectorImages
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymmetricCoordinates
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm
open CharTwoProjectorImages (standardMonomial generatorImage)

/-- All invariant-polynomial multiples of the eight explicit norm generators. -/
def generatorSpan : Submodule (ZMod 2) Poly :=
  Submodule.span (ZMod 2) {v | ∃ p : Poly, ∃ i : Fin 8, v = invariantEval p*generator i}

theorem invariant_mul_generator_mem (p : Poly) (i : Fin 8) :
    invariantEval p*generator i ∈ generatorSpan :=
  Submodule.subset_span ⟨p,i,rfl⟩

theorem generator_mem (i : Fin 8) : generator i ∈ generatorSpan := by
  simpa only [map_one, one_mul] using invariant_mul_generator_mem 1 i

/-- The displayed span is closed under multiplication by any invariant polynomial. -/
theorem invariant_mul_mem {f : Poly} (hf : f ∈ generatorSpan) (p : Poly) :
    invariantEval p*f ∈ generatorSpan := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨q,i,rfl⟩ := h
    simpa only [map_mul, mul_assoc] using invariant_mul_generator_mem (p*q) i
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [mul_add] using generatorSpan.add_mem ihf ihg
  | smul r f hf ih => simpa only [mul_smul_comm] using generatorSpan.smul_mem r ih

/-- Every one of the 28 computed projector images lies in the invariant generator span. -/
theorem generatorImage_mem (i : Fin 28) : generatorImage i ∈ generatorSpan := by
  have hi0 : d4*generator 4 ∈ generatorSpan := by
    simpa only [invariantEval, bind₁_X_right, invariant, Matrix.cons_val_zero] using
      invariant_mul_generator_mem (X 0) 4
  have hi1 : d6*generator 1 ∈ generatorSpan := by
    simpa only [invariantEval, bind₁_X_right, invariant, Matrix.cons_val_one, Matrix.cons_val_zero] using
      invariant_mul_generator_mem (X 1) 1
  have hi2 : d7*generator 0 ∈ generatorSpan := by
    simpa only [invariantEval, bind₁_X_right, invariant, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons] using
      invariant_mul_generator_mem (X 2) 0
  fin_cases i
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generator_mem 0
  · exact generatorSpan.zero_mem
  · exact generator_mem 1
  · exact generator_mem 1
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generator_mem 2
  · exact generatorSpan.zero_mem
  · exact generatorSpan.zero_mem
  · exact generator_mem 3
  · exact generator_mem 4
  · exact generatorSpan.add_mem (generator_mem 3) (generator_mem 4)
  · exact generator_mem 5
  · exact generatorSpan.zero_mem
  · exact generator_mem 5
  · exact generator_mem 6
  · exact generatorSpan.zero_mem
  · exact generator_mem 7
  · exact generatorSpan.add_mem (generatorSpan.add_mem hi2 hi1) hi0

/-- The explicit projector respects addition. -/
theorem projector_add (f g : Poly) :
    CharTwoProjector.projector (f+g) = CharTwoProjector.projector f+CharTwoProjector.projector g := by
  simp only [CharTwoProjector.projector, CharTwoProjector.atom, CharTwoProjector.sub, map_add]
  ring

@[simp] theorem projector_zero : CharTwoProjector.projector 0 = 0 := by
  simp [CharTwoProjector.projector, CharTwoProjector.atom, CharTwoProjector.sub]

/-- The explicit projector respects arbitrary finite sums. -/
theorem projector_sum {ι : Type*} (s : Finset ι) (f : ι → Poly) :
    CharTwoProjector.projector (∑ i ∈ s, f i) = ∑ i ∈ s, CharTwoProjector.projector (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, projector_add, ih]

/-- Complete standard-monomial spanning yields complete norm-kernel spanning. -/
theorem norm_kernel_mem_of_standard_expansion {f : Poly}
    (hs : CharTwoProjector.Symmetric f) (hn : norm f = 0)
    (coeffs : Fin 28 → Poly)
    (hexp : f = ∑ i, invariantEval (coeffs i)*standardMonomial i) : f ∈ generatorSpan := by
  rw [← CharTwoProjector.projector_eq_of_norm hs hn, hexp, projector_sum]
  apply generatorSpan.sum_mem
  intro i _
  rw [CharTwoProjectorImages.projector_invariantEval_mul,
    CharTwoProjectorImages.projector_standardMonomial]
  exact invariant_mul_mem (generatorImage_mem i) (coeffs i)

/-- Eight polynomial coefficients assemble a member of the norm kernel. -/
def generatorCoefficientMap : (Fin 8 → Poly) →ₗ[ZMod 2] Poly where
  toFun q := ∑ i, invariantEval (q i)*generator i
  map_add' p q := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r q := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

private theorem span_le_range_single (v : Fin 8 → Poly) (w : Poly →ₗ[ZMod 2] Poly)
    (L : (Fin 8 → Poly) →ₗ[ZMod 2] Poly)
    (hL : ∀ p i, L (Pi.single i p) = w p * v i) :
    Submodule.span (ZMod 2) {f | ∃ p i, f = w p * v i} ≤ LinearMap.range L := by
  apply Submodule.span_le.mpr
  rintro f ⟨p,i,rfl⟩
  exact ⟨Pi.single i p, hL p i⟩

private theorem generatorCoefficientMap_single (p : Poly) (i : Fin 8) :
    generatorCoefficientMap (Pi.single i p) = invariantEval p * generator i := by
  dsimp only [generatorCoefficientMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
  · simp

theorem generatorSpan_le_coefficient_range : generatorSpan ≤ LinearMap.range generatorCoefficientMap :=
  span_le_range_single generator invariantEval.toLinearMap generatorCoefficientMap
    generatorCoefficientMap_single

/-- Membership has the literal eight-coefficient polynomial form. -/
theorem mem_generatorSpan_iff (f : Poly) :
    f ∈ generatorSpan ↔ ∃ q : Fin 8 → Poly, f = ∑ i, invariantEval (q i)*generator i := by
  constructor
  · intro hf
    obtain ⟨q,hq⟩ := generatorSpan_le_coefficient_range hf
    exact ⟨q,hq.symm⟩
  · rintro ⟨q,rfl⟩
    exact generatorSpan.sum_mem (fun i _ => invariant_mul_generator_mem (q i) i)

end TernaryPoly.CharTwoNorm
