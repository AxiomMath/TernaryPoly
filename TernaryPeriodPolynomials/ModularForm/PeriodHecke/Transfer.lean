module

public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Primitive
public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Matrices

@[expose] public section

noncomputable section
open Complex Matrix
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryCuspHeckeEndomorphism BinaryRationalHeckePrime

/-- The actual coefficient-and-point action on the normalized primitive, including det(g)⁻¹. -/
def primitiveAction {d : ℕ} (f : Forms d) (g : GL2) (v : Coordinates) (z : ℂ) : ℂ :=
  (g.det.val : ℂ)⁻¹ * eichlerIntegral f
    ((((complexify g)⁻¹).val.mulVec v) 0) ((((complexify g)⁻¹).val.mulVec v) 1)
    (rationalMobius g⁻¹ z)

theorem primitiveAction_finite {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (b : ZMod p) (v : Coordinates) {z : ℂ} (hz : 0 < z.im) :
    primitiveAction f (adjugateRepresentative p (.inl b)) v z =
      (1/(p : ℂ))*heckePrimitiveFinite f p ⟨b.val,ZMod.val_lt b⟩ (v 0) (v 1) z := by
  rw [primitiveAction, adjugate_det, adjugate_inv_coordinates_finite,
    adjugate_inv_mobius_finite p b hz]
  simp only [Rat.cast_natCast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_div, heckePrimitiveFinite]

theorem primitiveAction_infinity {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (v : Coordinates) {z : ℂ} (hz : 0 < z.im) :
    primitiveAction f (adjugateRepresentative p (.inr ())) v z =
      (1/(p : ℂ))*heckePrimitiveInfinity f p (v 0) (v 1) z := by
  rw [primitiveAction, adjugate_det, adjugate_inv_coordinates_infinity,
    adjugate_inv_mobius_infinity p hz]
  simp only [Rat.cast_natCast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_div, heckePrimitiveInfinity]

/-- Literal finite reindexing connects ZMod transfer indices with the standard cusp formula. -/
theorem primitiveAction_sum {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (v : Coordinates) {z : ℂ} (hz : 0 < z.im) :
    (∑ i : PrimeIndex p, primitiveAction f (adjugateRepresentative p i) v z) =
      (1/(p : ℂ))*(heckePrimitiveInfinity f p (v 0) (v 1) z +
        ∑ b : Fin p, heckePrimitiveFinite f p b (v 0) (v 1) z) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  simp_rw [primitiveAction_finite f p _ v hz, primitiveAction_infinity f p v hz]
  rw [←Finset.mul_sum]
  have hs : (∑ b : ZMod p, heckePrimitiveFinite f p ⟨b.val,ZMod.val_lt b⟩ (v 0) (v 1) z) =
      ∑ b : Fin p, heckePrimitiveFinite f p b (v 0) (v 1) z := by
    rw [←(ZMod.finEquiv p).toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply Fin.ext
    exact val_finEquiv p b
  rw [hs]
  ring

/-- Exact scalar audit: standard cusp Hecke is p^(d+1) times the actual determinant-inverse
primitive transfer. This equality uses the literal actual representative matrices. -/
theorem eichlerIntegral_hecke_transfer {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (v : Coordinates) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral (T d p f) (v 0) (v 1) z = (p : ℂ)^(d+1) *
      ∑ i : PrimeIndex p, primitiveAction f (adjugateRepresentative p i) v z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [eichlerIntegral_hecke f p (v 0) (v 1) hz, heckePrimitive, primitiveAction_sum f p v hz, pow_succ]
  field_simp

end TernaryPoly.BinaryCuspSymbol
