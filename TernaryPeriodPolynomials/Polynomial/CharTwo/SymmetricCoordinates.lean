module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Projector
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Data.Finsupp.Notation
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.RingTheory.MvPolynomial.Tower

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

namespace CharTwoProjector

private theorem rename_eq_sub (φ : Fin 3 → Fin 3) (f : Poly) :
    rename φ f = sub f (X (φ 0)) (X (φ 1)) (X (φ 2)) := by
  have h : (rename φ : Poly →ₐ[ZMod 2] Poly) = bind₁ ![X (φ 0), X (φ 1), X (φ 2)] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun h f

private theorem sub_identity (f : Poly) : sub f (X 0) (X 1) (X 2) = f := by
  have hv : (![X 0, X 1, X 2] : Fin 3 → Poly) = X := by
    funext i
    fin_cases i <;> rfl
  simp only [sub, hv, bind₁_X_left, AlgHom.id_apply]

/-- The two generating symmetries give invariance under every permutation. -/
theorem Symmetric.isSymmetric {f : Poly} (hs : Symmetric f) : f.IsSymmetric := by
  intro σ
  rw [rename_eq_sub]
  obtain ⟨h10, h120, h201, h021, h210⟩ := sub_permutations hs (X 0) (X 1) (X 2)
  have hi := sub_identity f
  rw [hi] at h10 h120 h201 h021 h210
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  generalize h0 : σ 0 = i0 at *
  generalize h1 : σ 1 = i1 at *
  generalize h2 : σ 2 = i2 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all

/-- Mathlib symmetry implies both literal generating substitutions. -/
theorem symmetric_of_isSymmetric {f : Poly} (hs : f.IsSymmetric) : Symmetric f := by
  constructor
  · let σ : Equiv.Perm (Fin 3) :=
      Equiv.ofBijective (![1,2,0] : Fin 3 → Fin 3) (by decide)
    have h := hs σ
    rw [rename_eq_sub] at h
    exact h
  · let σ : Equiv.Perm (Fin 3) :=
      Equiv.ofBijective (![1,0,2] : Fin 3 → Fin 3) (by decide)
    have h := hs σ
    rw [rename_eq_sub] at h
    exact h

/-- The literal and permutation-invariant notions of symmetry coincide. -/
theorem symmetric_iff_isSymmetric (f : Poly) : Symmetric f ↔ f.IsSymmetric :=
  ⟨Symmetric.isSymmetric, symmetric_of_isSymmetric⟩

end CharTwoProjector

namespace CharTwoNorm

/-- Evaluate formal symmetric coordinates in the three actual elementary symmetric polynomials. -/
def elementaryEval : Poly →ₐ[ZMod 2] Poly := bind₁ (![a,b,c] : Fin 3 → Poly)

/-- The first elementary symmetric polynomial is the coordinate sum. -/
theorem esymm_one_eq_a : esymm (Fin 3) (ZMod 2) 1 = a := by
  simp only [esymm_one, Fin.sum_univ_three, a]

/-- The second elementary symmetric polynomial is the sum of the three pair products. -/
theorem esymm_two_eq_b : esymm (Fin 3) (ZMod 2) 2 = b := by
  have h : (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0,1},{0,2},{1,2}} := by decide
  rw [esymm, h]
  have h01 : ({0,1} : Finset (Fin 3)) ∉ ({{0,2},{1,2}} : Finset (Finset (Fin 3))) := by decide
  have h02 : ({0,2} : Finset (Fin 3)) ∉ ({{1,2}} : Finset (Finset (Fin 3))) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h02, Finset.sum_singleton]
  simp [b]
  ring

/-- The third elementary symmetric polynomial is the product of all three variables. -/
theorem esymm_three_eq_c : esymm (Fin 3) (ZMod 2) 3 = c := by
  have h : (Finset.univ : Finset (Fin 3)).powersetCard 3 = {{0,1,2}} := by decide
  rw [esymm, h]
  simp [c, mul_assoc]

/-- The literal elementary-coordinate map is the underlying map in the fundamental theorem. -/
theorem esymmAlgHom_eq_elementaryEval (p : Poly) :
    ((esymmAlgHom (Fin 3) (ZMod 2) 3 p : symmetricSubalgebra (Fin 3) (ZMod 2)) : Poly) =
      elementaryEval p := by
  rw [esymmAlgHom_apply, aeval_eq_bind₁]
  unfold elementaryEval
  congr 2
  funext i
  fin_cases i
  · exact esymm_one_eq_a
  · exact esymm_two_eq_b
  · exact esymm_three_eq_c

/-- Algebraic independence of elementary symmetric coordinates gives injectivity. -/
theorem elementaryEval_injective : Function.Injective elementaryEval := by
  intro p q hpq
  apply (esymmAlgHom_fin_bijective (ZMod 2) 3).1
  apply Subtype.ext
  simpa only [esymmAlgHom_eq_elementaryEval] using hpq

/-- Every elementary-coordinate expression satisfies the two literal symmetry equations. -/
theorem symmetric_elementaryEval (p : Poly) : CharTwoProjector.Symmetric (elementaryEval p) := by
  apply CharTwoProjector.symmetric_of_isSymmetric
  rw [← esymmAlgHom_eq_elementaryEval]
  exact (esymmAlgHom (Fin 3) (ZMod 2) 3 p).property

/-- Every actual symmetric polynomial has an expression in the elementary coordinates. -/
theorem exists_elementaryEval {f : Poly} (hs : CharTwoProjector.Symmetric f) :
    ∃ p : Poly, elementaryEval p = f := by
  obtain ⟨p, hp⟩ := (esymmAlgHom_fin_bijective (ZMod 2) 3).2 ⟨f, hs.isSymmetric⟩
  refine ⟨p, ?_⟩
  have h := congrArg (fun g : symmetricSubalgebra (Fin 3) (ZMod 2) => (g : Poly)) hp
  simpa only [esymmAlgHom_eq_elementaryEval] using h

/-- The range of elementary-coordinate evaluation is exactly the actual symmetric polynomials. -/
theorem symmetric_iff_exists_elementaryEval (f : Poly) :
    CharTwoProjector.Symmetric f ↔ ∃ p : Poly, elementaryEval p = f := by
  refine ⟨exists_elementaryEval, ?_⟩
  rintro ⟨p, rfl⟩
  exact symmetric_elementaryEval p

/-- Both characteristic-two developments use the same literal norm. -/
theorem norm_eq_projector_norm (f : Poly) : norm f = CharTwoProjector.norm f := rfl

end CharTwoNorm
end TernaryPoly
