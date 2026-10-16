module

public import Mathlib

@[expose] public section


/-!
# A free `Q`-set is `Q × I`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor


/-- A free `Q`-set is `Q × I` for a set `I` of orbit representatives. -/
theorem exists_free_decomp (Q : Type) [Group Q] (X : Type) [MulAction Q X] (free : ∀ (q : Q) (x : X), q • x = x → q = 1) :
    ∃ (I : Type) (e : X ≃ Q × I), ∀ (q : Q) (x : X), e (q • x) = (q * (e x).1, (e x).2) := by
  classical
  let I := MulAction.orbitRel.Quotient Q X
  let rep : I → X := fun i => Quotient.out i
  have hrep : ∀ x : X, ∃ q : Q, q • rep (Quotient.mk _ x) = x := by
    intro x
    have h : (Quotient.mk (MulAction.orbitRel Q X) x) = Quotient.mk _ (rep (Quotient.mk _ x)) := by
      simp only [rep, Quotient.out_eq]
    have := Quotient.exact h
    -- orbitRel: x ~ rep  iff  x ∈ orbit rep
    obtain ⟨q, hq⟩ := (MulAction.orbitRel_apply.mp this)
    exact ⟨q, hq⟩
  have uniq : ∀ (q q' : Q) (y : X), q • y = q' • y → q = q' := by
    intro q q' y h
    have : (q'⁻¹ * q) • y = y := by rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 := free _ _ this
    exact (inv_mul_eq_one.mp h1).symm
  let qOf : X → Q := fun x => Classical.choose (hrep x)
  have hq : ∀ x, qOf x • rep (Quotient.mk _ x) = x := fun x => Classical.choose_spec (hrep x)
  refine ⟨I, ⟨fun x => (qOf x, Quotient.mk _ x), fun p => p.1 • rep p.2, ?_, ?_⟩, ?_⟩
  · intro x
    exact hq x
  · rintro ⟨q, i⟩
    have hi : (Quotient.mk (MulAction.orbitRel Q X) (q • rep i)) = i := by
      have : Quotient.mk (MulAction.orbitRel Q X) (q • rep i) = Quotient.mk _ (rep i) :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit _ _))
      rw [this]
      simp only [rep, Quotient.out_eq]
    have h2 : qOf (q • rep i) • rep i = q • rep i := by
      have := hq (q • rep i)
      rw [hi] at this
      exact this
    have h3 : qOf (q • rep i) = q := uniq _ _ _ h2
    exact Prod.ext h3 hi
  · intro q x
    have h1 : (Quotient.mk (MulAction.orbitRel Q X) (q • x)) = Quotient.mk _ x :=
      Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit _ _))
    have h2 : qOf (q • x) = q * qOf x := by
      apply uniq _ _ (rep (Quotient.mk _ x))
      have := hq (q • x)
      rw [h1] at this
      rw [this, mul_smul, hq x]
    exact Prod.ext h2 h1


end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
