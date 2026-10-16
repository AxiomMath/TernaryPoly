module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneIwasawaRational
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.IntegralReduction
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ClassicalSection

@[expose] public section


/-!
# (B), step 1: `P(ℚ) ∩ K(N)` is `Γ_P`

Formalized by Claude Sonnet 5.5.

* `rat_mem_int`: a rational number integral at every place is an integer.
* `ratGL_integral`: if the finite image of `ρ ∈ GL₃(ℚ)` lies in the image of `GL₃(Ẑ)`, its entries are integers.
* `gammaN_of_rat_levelKernel`: if moreover the element of `GL₃(Ẑ)` lies in `K(N)` and `det ρ = 1`, then `ρ` is the image of an element of `Γ(N) ⊂ SL₃(ℤ)`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem rat_mem_int (r : ℚ) (h : ∀ v : FinitePlace, algebraMap ℚ (v.adicCompletion ℚ) r ∈ OS v) :
    ∃ z : ℤ, (z : ℚ) = r := by
  obtain ⟨z, hz⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (K := ℚ) r (fun v => by
    have := h v
    change algebraMap ℚ (v.adicCompletion ℚ) r ∈ v.adicCompletionIntegers ℚ at this
    have key : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r) = v.valuation ℚ r :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := ℤ) (v := v) (K := ℚ) r
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, key] at this
    exact this)
  exact ⟨z, hz⟩

theorem ratGL_integral (ρ : GL3 ℚ) (k : GL3 IntegralAdeles)
    (h : rationalFinite ρ = GeneralLinearGroup.map integralEmbedding k) (i j : Fin 3) :
    algebraMap ℚ FiniteAdeles (ρ.val i j) = integralEmbedding (k.val i j) := by
  have := congrArg (fun g : FiniteGL => g.val i j) h
  exact this

theorem rat_entry_int (ρ : GL3 ℚ) (k : GL3 IntegralAdeles)
    (h : rationalFinite ρ = GeneralLinearGroup.map integralEmbedding k) (i j : Fin 3) :
    ∃ z : ℤ, (z : ℚ) = ρ.val i j := by
  refine rat_mem_int _ fun v => ?_
  have := congrArg (finiteEvaluation v) (ratGL_integral ρ k h i j)
  rw [finiteEvaluation_rational] at this
  rw [this]
  exact (k.val i j v).2


variable (N : ℕ) [NeZero N]

/-- **`P(ℚ) ∩ K(N)`**: a determinant-one rational matrix whose finite image is an element of `K(N)` is an element of `Γ(N)`. -/
theorem gammaN_of_rat_levelKernel (ρ : GL3 ℚ) (hdet : ρ.val.det = 1) (k : GL3 IntegralAdeles)
    (hk : k ∈ IntegralReduction.levelKernel N 3) (h : rationalFinite ρ = GeneralLinearGroup.map integralEmbedding k) :
    ∃ w : SL(3, ℤ), w ∈ gammaN N ∧ ∀ i j, (((w : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ℚ) = ρ.val i j := by
  choose z hz using rat_entry_int ρ k h
  let W : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of z
  have hW : W.map (Int.cast : ℤ → ℚ) = ρ.val := by
    ext i j; exact hz i j
  have hdetW : W.det = 1 := by
    have : ((W.det : ℤ) : ℚ) = 1 := by
      rw [← hdet, ← hW]
      exact (RingHom.map_det (Int.castRingHom ℚ) W)
    exact_mod_cast this
  obtain ⟨w, hw⟩ : ∃ w : SL(3, ℤ), (w : Matrix (Fin 3) (Fin 3) ℤ) = W := ⟨⟨W, hdetW⟩, rfl⟩
  refine ⟨w, ?_, fun i j => by rw [hw]; exact hz i j⟩
  rw [mem_gammaN, hw]
  intro i j
  have hk' := (IntegralReduction.mem_levelKernel_iff N k).1 hk i j
  have hkz : k.val i j = ((z i j : ℤ) : IntegralAdeles) := by
    apply integralEmbedding_injective
    rw [← ratGL_integral ρ k h i j, integralEmbedding_int, ← hz i j]
    simp
  rw [hkz, IntegralReduction.integralReductionN_int] at hk'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
  show ((z i j : ℤ) : ZMod N) - (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) = 0
  rw [hk']
  simp [Matrix.one_apply]

end TernaryPeriodPolynomials.Argument.FormClassK
