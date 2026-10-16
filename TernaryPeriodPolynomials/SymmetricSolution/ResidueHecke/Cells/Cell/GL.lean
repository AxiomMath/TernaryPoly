module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellRep

@[expose] public section


/-!
# Lemma B.1, boundary route: the well-rounded complex is `GL₃(ℤ)`-stable

The cells of the well-rounded complex (spanning simplices of lines) and the boundary neighbours are stable
under the whole of `GL₃(ℤ)` (the library proves this for the principal congruence subgroup `Γ(3)` only, because
there the label signs are also preserved).  This file extends the sign-free statements: `spans`, `IsSimplex`,
`IsCell`, `nbrs` and the cardinality are stable under `g ∈ GL₃(ℤ)`; `glCell g` is the action on `Cell`, which on
`Γ(6)` is the action of `cellRep`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing
  GeneralEisenstein TernaryPeriodPolynomials.Argument.Lemma33.Retract

theorem spans_smul_gl (g : IntegralGL3) {T : Finset Line} (h : Spans T) : Spans (g • T) := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
  exact ⟨g • a, Finset.smul_mem_smul_finset ha, g • b, Finset.smul_mem_smul_finset hb,
    g • c, Finset.smul_mem_smul_finset hc, (Line.indep_smul g a b c).mpr habc⟩

theorem spans_smul_gl_iff (g : IntegralGL3) (T : Finset Line) : Spans (g • T) ↔ Spans T := by
  refine ⟨fun h => ?_, spans_smul_gl g⟩
  have := spans_smul_gl g⁻¹ h
  rwa [inv_smul_smul g T] at this

theorem isSimplex_smul_gl (g : IntegralGL3) {T : Finset Line} (h : IsSimplex T) : IsSimplex (g • T) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨Vtx.translate g v, ?_⟩
  rw [Vtx.translate_M]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_smul_finset.mp hx
  exact Finset.mem_image.mpr ⟨t, hv ht, rfl⟩

theorem isSimplex_smul_gl_iff (g : IntegralGL3) (T : Finset Line) : IsSimplex (g • T) ↔ IsSimplex T := by
  refine ⟨fun h => ?_, isSimplex_smul_gl g⟩
  have := isSimplex_smul_gl g⁻¹ h
  rwa [inv_smul_smul g T] at this

theorem isCell_smul_gl (g : IntegralGL3) (T : Finset Line) : IsCell (g • T) ↔ IsCell T := by
  rw [IsCell, IsCell, spans_smul_gl_iff, isSimplex_smul_gl_iff]

theorem card_smul_gl (g : IntegralGL3) (T : Finset Line) : (g • T).card = T.card := by
  rw [Finset.smul_finset_def, Finset.card_image_of_injective _ (MulAction.injective g)]

theorem nbrs_smul_gl (g : IntegralGL3) (T : Finset Line) : nbrs (g • T) = g • nbrs T := by
  by_cases hT : Spans T
  · have hT' : Spans (g • T) := (spans_smul_gl_iff g T).mpr hT
    ext w
    rw [mem_nbrs hT', ← smul_inv_smul g w, Finset.smul_mem_smul_finset_iff,
      Finset.smul_mem_smul_finset_iff, mem_nbrs hT, ← Finset.smul_finset_insert, isSimplex_smul_gl_iff]
  · rw [nbrs_of_not_spans hT, nbrs_of_not_spans (fun h => hT ((spans_smul_gl_iff g T).mp h)),
      Finset.smul_finset_empty]

/-- The action of `GL₃(ℤ)` on cells. -/
def glCell (g : IntegralGL3) (C : Cell) : Cell := ⟨g • C.val, (isCell_smul_gl g C.val).mpr C.isCell⟩

@[simp] theorem glCell_val (g : IntegralGL3) (C : Cell) : (glCell g C).val = g • C.val := rfl

theorem glCell_one (C : Cell) : glCell 1 C = C := Cell.ext (one_smul _ _)

theorem glCell_mul (g h : IntegralGL3) (C : Cell) : glCell (g * h) C = glCell g (glCell h C) :=
  Cell.ext (mul_smul g h C.val)

theorem glCell_injective (g : IntegralGL3) : Function.Injective (glCell g) := by
  intro C D h
  apply Cell.ext
  exact MulAction.injective g (congrArg Cell.val h)

theorem grade_glCell (g : IntegralGL3) (C : Cell) : (glCell g C).grade = C.grade := by
  rw [Cell.grade, Cell.grade, glCell_val, card_smul_gl]

/-- On `Γ(6)` the action is the one of the cellular representation. -/
theorem glCell_six (g : TernaryPoly.IntegralGL3Congruence.principalSix) (C : Cell) :
    glCell g.1 C = g • C := by
  apply Cell.ext
  change g.1 • C.val = (levelOfSix g • C).val
  rw [Cell.smul_val, Finset.smul_finset_def, Finset.smul_finset_def]
  congr 1
  funext ℓ
  rw [level_smul, levelLift_levelOfSix]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
