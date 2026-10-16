module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Pieces

@[expose] public section


/-!
# (C), step 6: the support of the finite part is the union of the congruence cells

Formalized by Claude Sonnet 5.5.

`exists_orbit_of_decomp`: if `w₀⁻¹ u(σ) = π κ` with `π ∈ P(ℚ)`, `det π = 1`, `κ ∈ K(N)` (the support of the induced
section), then `σ` lies in the cell of a free orbit `o` of the line radical lattice (strong approximation
`𝔸_f = ℚ + N Ẑ`, then `exists_elt_of_decomp` and `ptC_latQ`).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N]

theorem algebraMap_Nint_mem_lat (q : ℤ) : algebraMap ℚ FiniteAdeles ((N : ℚ) * q) ∈ latSet N := by
  have := latSet_natCast_mul N q
  convert this using 1
  rw [map_mul]
  push_cast
  simp

/-- **The support of the finite part lies in the congruence cells.** -/
theorem exists_orbit_of_decomp (σ : FiniteAdeles × FiniteAdeles)
    (h : ∃ π κ, IsDecomp N (gFin σ) π κ) : ∃ o : FreeOrb N, σ ∈ pieceFin N o := by
  obtain ⟨r0, hr0⟩ := exists_rat_sub_mem_lat N σ.1
  obtain ⟨r1, hr1⟩ := exists_rat_sub_mem_lat N σ.2
  set a : FiniteAdeles × FiniteAdeles := (algebraMap ℚ FiniteAdeles r0, algebraMap ℚ FiniteAdeles r1) with ha
  have hsub : σ - a = (σ.1 - algebraMap ℚ FiniteAdeles r0, σ.2 - algebraMap ℚ FiniteAdeles r1) := rfl
  obtain ⟨κ, hκ, he⟩ := gFin_add_lat N a (σ - a) hr0 hr1
  rw [add_sub_cancel] at he
  have h' : ∃ π κ, IsDecomp N (gFin a) π κ := by
    rw [he] at h
    exact (exists_decomp_mul_ker N (g := gFin a) (κ' := κ) hκ).1 h
  obtain ⟨b, hbN, hb0, hbr⟩ := exists_elt_of_decomp N (r0, r1) h'
  set c : Ck N 1 := Quotient.mk _ (⟨b, hbN⟩ : ↥(gammaN N)) with hc
  have hrow : ∀ j, cuspRow (gammaN N) (CuspData.ofSL 1).r c j = (b : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
    intro j
    rw [hc, cuspRow_mk_eq N 1 ⟨b, hbN⟩ j, one_mul]
  have hptc : ptC N c = (r0, r1) := by
    rw [← hbr]
    unfold ptC slRowPt rowPt
    rw [hrow, hrow, hrow]
  have hfree : (qActK N 1).r0Q (Quotient.mk (qActK N 1).orbSetoid c) ≠ 0 := by
    show cuspRow (gammaN N) (CuspData.ofSL 1).r c 0 ≠ 0
    rw [hrow]; exact hb0
  set o : FreeOrb N := ⟨Quotient.mk _ c, hfree⟩ with ho
  refine ⟨o, ?_⟩
  have hrel : (qActK N 1).OrbRel (orbCoset N o) c := by
    have : Quotient.mk (qActK N 1).orbSetoid (orbCoset N o) = Quotient.mk (qActK N 1).orbSetoid c :=
      Quotient.out_eq o.1
    exact Quotient.exact this
  obtain ⟨ℓ, hℓ⟩ := hrel
  have hpt := ptC_latQ N ℓ (orbCoset N o) (orbCoset_r0 N o)
  change cmulR N 1 (latQ N ℓ) (orbCoset N o) = c at hℓ
  rw [hℓ, hptc] at hpt
  have h1 : r0 = (orbPt N o).1 - N * ℓ 1 := by
    have := congrArg Prod.fst hpt
    simpa [orbPt] using this
  have h2 : r1 = (orbPt N o).2 - N * ℓ 0 := by
    have := congrArg Prod.snd hpt
    simpa [orbPt] using this
  refine ⟨(mem_latCoset N).2 ?_, (mem_latCoset N).2 ?_⟩
  · have := latSet_add N hr0 (algebraMap_Nint_mem_lat N (-(ℓ 1)))
    convert this using 1
    rw [h1]
    push_cast
    ring
  · have := latSet_add N hr1 (algebraMap_Nint_mem_lat N (-(ℓ 0)))
    convert this using 1
    rw [h2]
    push_cast
    ring

end TernaryPeriodPolynomials.Argument.FormClassK
