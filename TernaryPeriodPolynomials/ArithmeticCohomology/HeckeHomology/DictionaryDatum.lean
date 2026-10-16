module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryTernary
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryBinary

@[expose] public section


/-!
# `primeDatum p` is the right correspondence of the paper's `diag(p,1,1)`; the printed `diag(1,1,p)`; which parabolic

Formalized by Claude Sonnet 5.5.

**Convention check.**  For a right module `m·h` with left representation `ρ(h) m = m·h⁻¹`, a right correspondence indexed
by `t` has `f(h) = t⁻¹ h t` and transport `μ(m) = m·t = ρ(t⁻¹) m` with `μ(m·h) = μ(m)·f(h)`.

* `datum_right_conj`, `corrMap_eq_rightAct`, `corr_right_equivariant`: for ANY `D : HeckeDatum ι t⁻¹` the datum is exactly this right correspondence (the
  subgroup `S`, `f(s) = t⁻¹ ι(s) t`, `μ = (· · t)` with equivariance); the name `gInv` / the inverse in the datum is a presentation of `t`, not an inverse operator.
* `primeDatum_t`: `primeDatum p` is the datum of `g = t⁻¹` with `t = diag(p,1,1)`, which is the paper's representative `h_∞` (`primeRepresentative_matrix`).
* `printedDiag`, `printed_perm`: the printed `diag(1,1,p)` is `w diag(p,1,1) w⁻¹` for the integral permutation `w` swapping the first and last coordinates, so both
  generate the same double coset; `printed_double_coset`: each of the `p²+p+1` printed representatives lies in `Γ diag(1,1,p) Γ`.
* The parabolic: every printed representative preserves `H = {a = 0}` (`primeRepresentative_firstRow`, first row `(λ,0,0)`), i.e. lies in the rational
  stabilizer `(λ 0; u C)` of `P_H`; `levi_block_ternary_rep` identifies the Levi blocks: the families `(b,c,p)` and `(a,p,0)` have `λ = 1` and blocks
  `C_c = (1 0; c p)`, `C_∞ = diag(p,1)` (the binary representatives `primeRepresentative` of the binary library), and `diag(p,1,1)` has `λ = p`, `C = I`.
* Binary: `binDatum_t`, `binDatum_right_conj`, `binDatum_corrMap` (datum of `t = diag(p,1) = C_∞`), `printed_perm_bin`, `printed_double_coset_bin` (the `p+1` binary
  representatives lie in `Γ diag(1,p) Γ`).
* `chartLift_mem_Sp_iff`, `chartLift_inf_mem_Sp`: the coset representative `x_i` lies in `S_p · 1 · P_H` exactly for the printed `diag(p,1,1)` (`i = ∞`),
  and in `S_p · σ · P_H` for the other `p²+p` (`chartLift_mem_sigma_coset`): the identity-term `p²` of `eq:Hecke-formula` comes from `diag(p,1,1)` and the `p T₂`
  term from the `λ = 1` families.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly CategoryTheory Representation Representation.Coinvariants

section Generic

variable {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} (t : Ĝ) (D : HeckeDatum ι t⁻¹) (M : Rep.{0} ℚ Ĝ)

theorem datum_right_conj (s : D.S) : ι (D.f s) = t⁻¹ * ι s * t := by
  simpa using D.hf s

theorem corrMap_eq_rightAct (m : Rep.res D.S.subtype (Rep.res ι M)) :
    (corrMap D M).hom m = rightAct M m t := rfl

/-- `μ(m · h) = μ(m) · f(h)` for the right correspondence of `t`. -/
theorem corr_right_equivariant (s : D.S) (m : M) :
    rightAct M (rightAct M m (ι s)) t = rightAct M (rightAct M m t) (ι (D.f s)) := by
  rw [← rightAct_mul, ← rightAct_mul, datum_right_conj t D s]
  congr 1
  group

end Generic

section Ternary

open scoped Classical

open TernaryPoly.ModThreeGoodAction
open TernaryPeriodPolynomials.Argument.AppendixBResidue (PH)
open TernaryPoly.OrdinaryHeckeCosets (PrimeIndex chartLift chartPermutation primeRepresentative)

variable (p : ℕ) [Fact p.Prime]

/-- `primeDatum p` is the datum of `g = t⁻¹` for `t = diag(p,1,1)`. -/
theorem primeDatum_t : gInv p = (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p)⁻¹ := rfl

theorem primeDiagonal_val :
    (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p).val = !![(p : ℚ), 0, 0; 0, 1, 0; 0, 0, 1] := rfl

/-- The right correspondence of `t = diag(p,1,1)` is `primeDatum p`: conjugation `s ↦ t⁻¹ s t` and transport `m ↦ m·t`. -/
theorem primeDatum_right_conj (s : (primeDatum p).S) :
    OrdinaryFullAction.integral ((primeDatum p).f s) =
      (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p)⁻¹ * OrdinaryFullAction.integral (s : IntegralGL) *
        TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p :=
  datum_right_conj (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p) (primeDatum p) s

theorem primeDatum_corrMap (M : Rep.{0} ℚ OrdinaryFullAction.GL3) (m : Rep.res (primeDatum p).S.subtype (Rep.res OrdinaryFullAction.integral M)) :
    (corrMap (primeDatum p) M).hom m = rightAct M m (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p) :=
  corrMap_eq_rightAct (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p) (primeDatum p) M m

/-- The printed matrix `diag(1,1,p)`. -/
def printedDiag : OrdinaryFullAction.GL3 :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, (p : ℚ)], !![1, 0, 0; 0, 1, 0; 0, 0, (p : ℚ)⁻¹],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hp],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hp]⟩

/-- The integral permutation swapping the first and last coordinates. -/
def wSwap13 : IntegralGL :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- `diag(1,1,p) = w · diag(p,1,1) · w⁻¹` with `w ∈ GL₃(ℤ)`: the printed and the used matrix generate the same double coset. -/
theorem printed_perm :
    OrdinaryFullAction.integral wSwap13 * TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p *
        (OrdinaryFullAction.integral wSwap13)⁻¹ = printedDiag p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  have hw : ((OrdinaryFullAction.integral wSwap13)⁻¹).val = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext a b; fin_cases a <;> fin_cases b <;> rfl
  have hI : (OrdinaryFullAction.integral wSwap13).val = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [wSwap13]; all_goals rfl
  rw [hw, hI]
  fin_cases i <;> fin_cases j <;>
    simp [printedDiag, TernaryPoly.OrdinaryHeckeCosets.primeDiagonal, Matrix.mul_apply, Fin.sum_univ_three]

/-- Each of the `p²+p+1` printed representatives lies in the double coset `Γ diag(1,1,p) Γ`. -/
theorem printed_double_coset (i : PrimeIndex p) :
    ∃ a b : IntegralGL, primeRepresentative p i =
      OrdinaryFullAction.integral a * printedDiag p * OrdinaryFullAction.integral b := by
  refine ⟨(wSwap13 * chartLift i)⁻¹, wSwap13 * chartPermutation i, ?_⟩
  have h := printed_perm p
  have hD : TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p =
      (OrdinaryFullAction.integral wSwap13)⁻¹ * printedDiag p * OrdinaryFullAction.integral wSwap13 := by
    rw [← h]; group
  change (OrdinaryFullAction.integral (chartLift i))⁻¹ * TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p *
      OrdinaryFullAction.integral (chartPermutation i) = _
  rw [hD]
  simp only [map_mul, map_inv]
  group

section Levi

open TernaryPoly.OrdinaryResidueParabolic (lowerBlock)

theorem levi_block_AB (b c : ZMod p) :
    (primeRepresentative p (Sum.inl (b, c))).val 0 0 = 1 ∧
    lowerBlock (primeRepresentative p (Sum.inl (b, c))).val =
      (TernaryPoly.BinaryRationalHeckePrime.primeRepresentative p (Sum.inl c)).val := by
  rw [TernaryPoly.OrdinaryHeckeCosets.primeRepresentative_matrix,
    TernaryPoly.BinaryRationalHeckePrime.primeRepresentative_matrix]
  refine ⟨rfl, ?_⟩
  ext a e
  fin_cases a <;> fin_cases e <;> rfl

theorem levi_block_B (a : ZMod p) :
    (primeRepresentative p (Sum.inr (Sum.inl a))).val 0 0 = 1 ∧
    lowerBlock (primeRepresentative p (Sum.inr (Sum.inl a))).val =
      (TernaryPoly.BinaryRationalHeckePrime.primeRepresentative p (Sum.inr ())).val := by
  rw [TernaryPoly.OrdinaryHeckeCosets.primeRepresentative_matrix,
    TernaryPoly.BinaryRationalHeckePrime.primeRepresentative_matrix]
  refine ⟨rfl, ?_⟩
  ext c e
  fin_cases c <;> fin_cases e <;> rfl

theorem levi_block_D (u : Unit) :
    (primeRepresentative p (Sum.inr (Sum.inr u))).val 0 0 = (p : ℚ) ∧
    lowerBlock (primeRepresentative p (Sum.inr (Sum.inr u))).val = 1 := by
  rw [TernaryPoly.OrdinaryHeckeCosets.primeRepresentative_matrix]
  refine ⟨rfl, ?_⟩
  ext c e
  fin_cases c <;> fin_cases e <;> rfl

end Levi

section Cosets

theorem chartLift_mem_Sp_iff (i : PrimeIndex p) :
    chartLift i ∈ (primeDatum p).S ↔ i = Sum.inr (Sum.inr ()) := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    have h2 := (Fact.out : p.Prime).two_le
    omega
  change chartLift i ∈ Sp p ↔ _
  rw [mem_Sp]
  rcases i with ⟨b, c⟩ | a | u
  · constructor
    · rintro ⟨-, h⟩
      exact absurd h (by simpa [chartLift, TernaryPoly.OrdinaryHeckeCosets.chartMatrix] using hp1)
    · intro h; cases h
  · constructor
    · rintro ⟨h, -⟩
      exact absurd h (by simpa [chartLift, TernaryPoly.OrdinaryHeckeCosets.chartMatrix] using hp1)
    · intro h; cases h
  · constructor
    · intro _; rfl
    · intro _
      simp [chartLift, TernaryPoly.OrdinaryHeckeCosets.chartMatrix]

theorem chartLift_mem_sigma_coset (i : PrimeIndex p) (hi : i ≠ Sum.inr (Sum.inr ())) :
    ∃ s ∈ (primeDatum p).S, ∃ h ∈ PH, chartLift i = s * sigma * h := by
  obtain ⟨x, hx, s, hs, h, hh, hy⟩ := (doubleCosetReps p).cover (chartLift i)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exfalso
    apply hi
    rw [← chartLift_mem_Sp_iff, hy]
    simpa using (primeDatum p).S.mul_mem hs (PH_le_Sp p hh)
  · exact ⟨s, hs, h, hh, hy⟩

end Cosets

end Ternary

section Binary

open TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.BinaryRationalHeckePrime (PrimeIndex chartLift chartPermutation primeRepresentative)

variable (p : ℕ) [Fact p.Prime]

/-- `binDatum p` is the datum of `g = t⁻¹` for `t = diag(p,1) = C_∞`. -/
theorem binDatum_t : C1 p = (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)⁻¹ := C1_eq_inv p

theorem binDatum_right_conj (s : (binDatum p).S) :
    binIota ((binDatum p).f s) =
      (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)⁻¹ * binIota (s : IntegralGL) *
        TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p := by
  have key : ∀ x : BinaryModularSymbol.GL2, C1 p * x * (C1 p)⁻¹ =
      (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)⁻¹ * x *
        TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p := by
    intro x
    rw [binDatum_t, inv_inv]
  rw [(binDatum p).hf s]
  exact key _

theorem binDatum_corrMap (M : Rep.{0} ℚ BinaryModularSymbol.GL2)
    (m : Rep.res (binDatum p).S.subtype (Rep.res binIota M)) :
    (corrMap (binDatum p) M).hom m = rightAct M m (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p) := by
  change M.ρ (C1 p) m = M.ρ (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)⁻¹ m
  rw [binDatum_t]

/-- The integral swap of the two coordinates. -/
def wSwap2 : IntegralGL :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- `diag(1,p) = w · diag(p,1) · w⁻¹`. -/
theorem printed_perm_bin :
    binIota wSwap2 * TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p * (binIota wSwap2)⁻¹ = Cp p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  have hw : ((binIota wSwap2)⁻¹).val = !![0, 1; 1, 0] := by
    ext a b; fin_cases a <;> fin_cases b <;> rfl
  have hI : (binIota wSwap2).val = !![0, 1; 1, 0] := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [wSwap2, binIota, TernaryPoly.BinaryModularSymbol.integral]
  rw [hw, hI]
  fin_cases i <;> fin_cases j <;>
    simp [Cp, TernaryPoly.BinaryRationalHeckePrime.primeDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Each of the `p+1` binary representatives lies in the double coset `Γ diag(1,p) Γ`. -/
theorem printed_double_coset_bin (i : PrimeIndex p) :
    ∃ a b : IntegralGL, primeRepresentative p i = binIota a * Cp p * binIota b := by
  refine ⟨(wSwap2 * chartLift i)⁻¹, wSwap2 * chartPermutation i, ?_⟩
  have h := printed_perm_bin p
  have hD : TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p =
      (binIota wSwap2)⁻¹ * Cp p * binIota wSwap2 := by
    rw [← h]; group
  change (binIota (chartLift i))⁻¹ * TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p *
      binIota (chartPermutation i) = _
  rw [hD]
  simp only [map_mul, map_inv]
  group

end Binary

end TernaryPeriodPolynomials.Argument.HeckeHomology
