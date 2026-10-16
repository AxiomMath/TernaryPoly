module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Transfer

@[expose] public section


/-!
# Reindexing lemma for the double coset sums of the Hecke bridge (L5)

Formalized by Claude Sonnet 5.5.

For a finite-index subgroup `S ≤ Γ` and an injective `f : S →* Γ` with `Γ/f(S)` finite, a function `T : Γ → Γ → V` with
`T (y f(s)) (s⁻¹ x) = T y x` and finite supports in each variable satisfies
`∑_{X ∈ S\Γ} ∑ᶠ_y T y X.out = ∑ᶠ_{Y ∈ Γ/f(S)} ∑ᶠ_x T Y.out x` (`sum_reindex`), via the bijections `Γ ≃ (Γ/f(S)) × S`,
`Γ ≃ (S\Γ) × S` (`leftDecomp`, `rightDecomp`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

section Reindex

open TernaryPeriodPolynomials.Argument.HeckeHomology
open scoped Classical

variable {Γ : Type} [Group Γ] (S : Subgroup Γ) (f : S →* Γ)

/-- `(Y, σ) ↦ Y.out · f(σ)` is a bijection `(Γ/f(S)) × S ≃ Γ`. -/
def leftDecomp (hf : Function.Injective f) : (Γ ⧸ f.range) × S ≃ Γ :=
  Equiv.ofBijective (fun q => Quotient.out q.1 * f q.2) (by
    constructor
    · rintro ⟨Y, σ⟩ ⟨Y', σ'⟩ h
      have h1 : (QuotientGroup.mk (Quotient.out Y * f σ) : Γ ⧸ f.range) = Y := by
        rw [QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)]
        exact QuotientGroup.out_eq' Y
      have h2 : (QuotientGroup.mk (Quotient.out Y' * f σ') : Γ ⧸ f.range) = Y' := by
        rw [QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨σ', rfl⟩)]
        exact QuotientGroup.out_eq' Y'
      have hY : Y = Y' := by
        rw [← h1, ← h2]
        exact congrArg QuotientGroup.mk h
      subst hY
      have : f σ = f σ' := mul_left_cancel h
      exact Prod.ext rfl (hf this)
    · intro y
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul f.range y
      obtain ⟨σ, hσ⟩ := (f.range.inv_mem h.2)
      refine ⟨(QuotientGroup.mk y, σ), ?_⟩
      show Quotient.out (QuotientGroup.mk y : Γ ⧸ f.range) * f σ = y
      rw [hh, hσ]
      simp)

variable [S.FiniteIndex]

/-- `(X, σ) ↦ σ · X.out` is a bijection `(S\Γ) × S ≃ Γ`. -/
def rightDecomp : RC S × S ≃ Γ :=
  Equiv.ofBijective (fun q => (q.2 : Γ) * Quotient.out q.1) (by
    constructor
    · rintro ⟨X, σ⟩ ⟨X', σ'⟩ h
      have key : ∀ (X : RC S) (σ : S),
          (Quotient.mk (QuotientGroup.rightRel S) ((σ : Γ) * Quotient.out X) : RC S) = X := by
        intro X σ
        have hX : (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out X) : RC S) = X := Quotient.out_eq X
        rw [← hX]
        rw [rc_eq_iff]
        simp
      have hXX : X = X' := by
        rw [← key X σ, ← key X' σ']
        exact congrArg _ h
      subst hXX
      have : (σ : Γ) = σ' := mul_right_cancel h
      exact Prod.ext rfl (Subtype.ext this)
    · intro y
      have hX : (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out
          (Quotient.mk (QuotientGroup.rightRel S) y : RC S)) : RC S) = Quotient.mk (QuotientGroup.rightRel S) y :=
        Quotient.out_eq _
      rw [rc_eq_iff] at hX
      refine ⟨(Quotient.mk (QuotientGroup.rightRel S) y, ⟨y * (Quotient.out
        (Quotient.mk (QuotientGroup.rightRel S) y : RC S))⁻¹, hX⟩), ?_⟩
      show y * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) y : RC S))⁻¹ *
        Quotient.out (Quotient.mk (QuotientGroup.rightRel S) y : RC S) = y
      simp)

theorem sum_reindex {V : Type*} [AddCommGroup V] (hf : Function.Injective f) [Finite (Γ ⧸ f.range)]
    (T : Γ → Γ → V) (hT : ∀ (s : S) (y x : Γ), T (y * f s) ((s : Γ)⁻¹ * x) = T y x)
    (hy : ∀ x, (Function.support fun y => T y x).Finite)
    (hx : ∀ y, (Function.support fun x => T y x).Finite) :
    ∑ X : RC S, ∑ᶠ y : Γ, T y (Quotient.out X) =
      ∑ᶠ Y : Γ ⧸ f.range, ∑ᶠ x : Γ, T (Quotient.out Y) x := by
  have : Fintype (Γ ⧸ f.range) := Fintype.ofFinite _
  have step1 : ∀ X : RC S, ∑ᶠ y : Γ, T y (Quotient.out X) =
      ∑ Y : Γ ⧸ f.range, ∑ᶠ σ : S, T (Quotient.out Y) ((σ : Γ) * Quotient.out X) := by
    intro X
    rw [← finsum_comp_equiv (leftDecomp S f hf)]
    have hsupp : (Function.support fun q : (Γ ⧸ f.range) × S =>
        T (leftDecomp S f hf q) (Quotient.out X)).Finite :=
      (hy (Quotient.out X)).preimage ((leftDecomp S f hf).injective.injOn)
    rw [finsum_curry _ hsupp, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun Y _ => finsum_congr fun σ => ?_
    have := hT σ (Quotient.out Y) ((σ : Γ) * Quotient.out X)
    rw [inv_mul_cancel_left] at this
    exact this
  have step2 : ∀ Y : Γ ⧸ f.range, ∑ᶠ x : Γ, T (Quotient.out Y) x =
      ∑ X : RC S, ∑ᶠ σ : S, T (Quotient.out Y) ((σ : Γ) * Quotient.out X) := by
    intro Y
    rw [← finsum_comp_equiv (rightDecomp S)]
    have hsupp : (Function.support fun q : RC S × S =>
        T (Quotient.out Y) (rightDecomp S q)).Finite :=
      (hx (Quotient.out Y)).preimage ((rightDecomp S).injective.injOn)
    rw [finsum_curry _ hsupp, finsum_eq_sum_of_fintype]
    rfl
  simp only [step1, step2]
  rw [finsum_eq_sum_of_fintype, Finset.sum_comm]

end Reindex

end TernaryPeriodPolynomials.Argument.HeckeNormalization
