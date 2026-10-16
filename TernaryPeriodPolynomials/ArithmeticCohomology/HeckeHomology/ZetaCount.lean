module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ZetaMap

@[expose] public section


/-!
# Splitting the coset sum `S\P` along `U`

Formalized by Claude Sonnet 5.5.

For `U ⊲ P` and a finite-index subgroup `S ≤ P`, the right cosets `S\P` are in bijection with pairs
`((S ∩ U)\U, Γ₀\(P/U))` through `(i, γ) ↦ S · (i.out · γ.out.out)` (`splitMap_bijective`); consequently a sum over `S\P` of a
left-`S`-invariant function is the iterated sum (`sum_rc_split`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section Count

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex]

/-- A representative in `P` of the quotient element `γ.out` of `P/U`. -/
def tRep (γ : RC (G0 U S)) : P := (γ.out : P ⧸ U).out

omit [S.FiniteIndex] in
theorem mk_tRep (γ : RC (G0 U S)) : (QuotientGroup.mk (tRep U S γ) : P ⧸ U) = γ.out :=
  QuotientGroup.out_eq' _

/-- The map `(i, γ) ↦ S · i.out · γ.out.out`. -/
def splitMap (p : RC (U1 U S) × RC (G0 U S)) : RC S :=
  Quotient.mk _ (((p.1.out : U) : P) * tRep U S p.2)

omit [S.FiniteIndex] in
theorem splitMap_injective : Function.Injective (splitMap U S) := by
  rintro ⟨i, γ⟩ ⟨i', γ'⟩ h
  change (Quotient.mk (QuotientGroup.rightRel S) (((i.out : U) : P) * tRep U S γ) : RC S) =
    Quotient.mk _ (((i'.out : U) : P) * tRep U S γ') at h
  rw [rc_eq_iff] at h
  set s₀ : P := (((i'.out : U) : P) * tRep U S γ') * (((i.out : U) : P) * tRep U S γ)⁻¹ with hs₀
  -- reduce modulo `U`
  have hmk : (QuotientGroup.mk s₀ : P ⧸ U) = γ'.out * γ.out⁻¹ := by
    have h1 : (QuotientGroup.mk (((i'.out : U) : P)) : P ⧸ U) = 1 := (QuotientGroup.eq_one_iff _).2 (i'.out).2
    have h2 : (QuotientGroup.mk (((i.out : U) : P)) : P ⧸ U) = 1 := (QuotientGroup.eq_one_iff _).2 (i.out).2
    rw [hs₀]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_tRep, h1, h2, one_mul, mul_inv_rev, inv_one, mul_one]
  have hG : γ'.out * γ.out⁻¹ ∈ G0 U S := by
    rw [← hmk]
    exact ⟨s₀, h, rfl⟩
  have hγ : γ = γ' := by
    have : (Quotient.mk (QuotientGroup.rightRel (G0 U S)) γ.out : RC (G0 U S)) = Quotient.mk _ γ'.out :=
      (rc_eq_iff _ _ _).2 hG
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this
  subst hγ
  have hU : (((i'.out : U) : P) * ((i.out : U) : P)⁻¹) ∈ S := by
    have : s₀ = ((i'.out : U) : P) * ((i.out : U) : P)⁻¹ := by
      rw [hs₀]; group
    rw [← this]; exact h
  have hi : i = i' := by
    have : (Quotient.mk (QuotientGroup.rightRel (U1 U S)) i.out : RC (U1 U S)) = Quotient.mk _ i'.out := by
      rw [rc_eq_iff]
      exact hU
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this
  rw [hi]

omit [S.FiniteIndex] in
theorem splitMap_surjective : Function.Surjective (splitMap U S) := by
  intro x
  set w : P := x.out with hw
  set γ : RC (G0 U S) := Quotient.mk _ (QuotientGroup.mk w) with hγ
  have h1 : (Quotient.mk (QuotientGroup.rightRel (G0 U S)) (QuotientGroup.mk w : P ⧸ U) : RC (G0 U S)) =
      Quotient.mk _ γ.out := by
    rw [Quotient.out_eq]
  rw [rc_eq_iff] at h1
  obtain ⟨s₀, hs₀S, hs₀⟩ := h1
  -- `mk s₀ = γ.out * (mk w)⁻¹ = mk (tRep γ * w⁻¹)`
  have h2 : (QuotientGroup.mk s₀ : P ⧸ U) = QuotientGroup.mk (tRep U S γ * w⁻¹) := by
    have hs₀' : (QuotientGroup.mk s₀ : P ⧸ U) = γ.out * (QuotientGroup.mk w)⁻¹ := hs₀
    rw [hs₀']
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_tRep]
  rw [QuotientGroup.eq] at h2
  -- `v = s₀⁻¹ * (tRep * w⁻¹) ∈ U`
  set v : P := s₀⁻¹ * (tRep U S γ * w⁻¹) with hv
  have hvU : v ∈ U := h2
  have hw' : w = v⁻¹ * (s₀⁻¹ * tRep U S γ) := by rw [hv]; group
  set u'' : P := s₀ * v⁻¹ * s₀⁻¹ with hu''
  have hu''U : u'' ∈ U := by
    have := (inferInstance : U.Normal).conj_mem v⁻¹ (U.inv_mem hvU) s₀
    exact this
  set i : RC (U1 U S) := Quotient.mk _ (⟨u'', hu''U⟩ : U) with hi
  have h3 : (Quotient.mk (QuotientGroup.rightRel (U1 U S)) (⟨u'', hu''U⟩ : U) : RC (U1 U S)) = Quotient.mk _ i.out := by
    rw [Quotient.out_eq]
  rw [rc_eq_iff] at h3
  -- `n = i.out * u''⁻¹ ∈ S`
  have hnS : ((i.out : U) : P) * u''⁻¹ ∈ S := h3
  refine ⟨(i, γ), ?_⟩
  change (Quotient.mk (QuotientGroup.rightRel S) (((i.out : U) : P) * tRep U S γ) : RC S) = x
  rw [← Quotient.out_eq x]
  change _ = Quotient.mk _ w
  rw [rc_eq_iff]
  -- `w * (i.out * t)⁻¹ = s₀⁻¹ * n⁻¹`
  have : w * (((i.out : U) : P) * tRep U S γ)⁻¹ = s₀⁻¹ * (((i.out : U) : P) * u''⁻¹)⁻¹ := by
    rw [hw', hu'']
    group
  rw [this]
  exact S.mul_mem (S.inv_mem hs₀S) (S.inv_mem hnS)

omit [S.FiniteIndex] in
theorem splitMap_bijective : Function.Bijective (splitMap U S) :=
  ⟨splitMap_injective U S, splitMap_surjective U S⟩

/-- A sum over `S\P` of a left-`S`-invariant function is the iterated sum over `Γ₀\(P/U)` and `(S ∩ U)\U`. -/
theorem sum_rc_split {M : Type*} [AddCommMonoid M] (φ : P → M) (hφ : ∀ s : S, ∀ w, φ (s * w) = φ w) :
    ∑ x : RC S, φ x.out =
      ∑ γ : RC (G0 U S), ∑ i : RC (U1 U S), φ (((i.out : U) : P) * tRep U S γ) := by
  have key : ∀ p : RC (U1 U S) × RC (G0 U S),
      φ (splitMap U S p).out = φ (((p.1.out : U) : P) * tRep U S p.2) := by
    intro p
    have h : (Quotient.mk (QuotientGroup.rightRel S) (((p.1.out : U) : P) * tRep U S p.2) : RC S) =
        Quotient.mk _ (splitMap U S p).out := by
      rw [Quotient.out_eq]; rfl
    rw [rc_eq_iff] at h
    have h3 : (splitMap U S p).out = ((splitMap U S p).out * (((p.1.out : U) : P) * tRep U S p.2)⁻¹) *
        (((p.1.out : U) : P) * tRep U S p.2) := by group
    rw [h3, hφ ⟨_, h⟩]
  calc ∑ x : RC S, φ x.out = ∑ p : RC (U1 U S) × RC (G0 U S), φ (splitMap U S p).out :=
        (Fintype.sum_bijective (splitMap U S) (splitMap_bijective U S) _ _ (fun p => rfl)).symm
    _ = ∑ p : RC (U1 U S) × RC (G0 U S), φ (((p.1.out : U) : P) * tRep U S p.2) :=
        Finset.sum_congr rfl fun p _ => key p
    _ = _ := by
        rw [Fintype.sum_prod_type_right]

end Count

end TernaryPeriodPolynomials.Argument.HeckeHomology
