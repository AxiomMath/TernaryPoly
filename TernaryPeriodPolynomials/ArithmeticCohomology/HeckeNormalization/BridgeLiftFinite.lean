module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.FiniteIndex

@[expose] public section


/-!
# `Γ/f(S)` is finite for the binary Hecke datum

Formalized by Claude Sonnet 5.5.

`f_range_eq_comap`: the image of the correspondence map `f` of `binDatum p` is the pull-back, along `integralEquiv`, of the library's actual
intersection subgroup `Γ ∩ C₁ Γ C₁⁻¹`; hence (`intersection_finiteIndex`) `finite_quot_f_range : Finite (IntegralGL ⧸ f.range)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryRationalHeckeArithmetic
open TernaryPoly.BinaryModularSymbol TernaryPoly.OrdinaryHeckeTransfer
open TernaryPeriodPolynomials.Argument.HeckeHomology

variable (p : ℕ) [Fact p.Prime]

theorem f_range_eq_comap : (binDatum p).f.range =
    Subgroup.comap integralEquiv.toMonoidHom (intersection Gamma (C1 p)) := by
  ext k
  rw [Subgroup.mem_comap, mem_intersection]
  constructor
  · rintro ⟨s, rfl⟩
    have hf := (binDatum p).hf s
    change (C1 p)⁻¹ * (binIota ((binDatum p).f s)) * C1 p ∈ Gamma
    rw [hf]
    refine ⟨s.1, ?_⟩
    change binIota s.1 = _
    group
  · intro h
    obtain ⟨δ, hδ⟩ := h
    have hδ' : binIota δ = (C1 p)⁻¹ * binIota k * C1 p := hδ
    have hS : δ ∈ commSubgroup binIota (C1 p) := by
      refine mem_commSubgroup.mpr ⟨k, ?_⟩
      rw [hδ']
      group
    refine ⟨⟨δ, hS⟩, ?_⟩
    apply binIota_injective
    rw [(binDatum p).hf]
    change C1 p * binIota δ * (C1 p)⁻¹ = binIota k
    rw [hδ']
    group

theorem finite_quot_f_range : Finite (IntegralGL ⧸ (binDatum p).f.range) := by
  have hfi : (intersection Gamma (C1 p)).FiniteIndex := intersection_finiteIndex (C1 p)
  have hsurj : Function.Surjective integralEquiv.toMonoidHom := integralEquiv.surjective
  have h1 := Subgroup.index_comap_of_surjective (intersection Gamma (C1 p)) hsurj
  rw [← f_range_eq_comap] at h1
  have : (binDatum p).f.range.FiniteIndex := ⟨by rw [h1]; exact hfi.index_ne_zero⟩
  exact Subgroup.finite_quotient_of_finiteIndex

end TernaryPeriodPolynomials.Argument.HeckeNormalization
