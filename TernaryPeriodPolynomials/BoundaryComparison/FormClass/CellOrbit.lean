module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KClass
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KConj
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NConstantTerms

@[expose] public section


/-!
# Orbit combinatorics of the cell of the series at a cusp

Formalized by Claude Sonnet 5.5.
* `cell_exists_iff`: the series at the cusp `h'`, seen from the face `h`, has a cell (`IsCellK`) iff `h` and `h'` are in one `Γ(N)`-orbit of planes (`planeFaceSetoid`).
* `no_cell_of_ne`: for different faces `x ≠ i` there is no cell: the `faceClass_none` applies.
* `cuspSlash_of_mem`, `cell_self`: from the same cusp the cell is the identity coset, with bottom entry `1`, and the slash of `f` by its Levi block is `f`.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ)

/-- **A cell of the series at the cusp `h'`, seen from the face `h`, exists iff the two cusps are in one `Γ(N)`-orbit of planes**
(`k = h' h⁻¹`; the face relation `h' = q h γ` of `PlaneFaces N`). -/
theorem cell_exists_iff (h h' : SL(3, ℤ)) :
    (∃ c : Ck N (h' * h⁻¹), IsCellK N (h' * h⁻¹) c) ↔ (planeFaceSetoid N).r h h' := by
  constructor
  · rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with | _ a => ?_
    obtain ⟨h0, h1⟩ := hc
    rw [cuspRow_mk_eq] at h0 h1
    refine ⟨h' * h⁻¹ * a.1, ⟨h0, h1⟩, h⁻¹ * a.1⁻¹ * h, ?_, by group⟩
    have := (gammaN_normal N).conj_mem a.1⁻¹ ((gammaN N).inv_mem a.2) h⁻¹
    simpa [mul_assoc] using this
  · rintro ⟨q, hq, γ, hγ, rfl⟩
    have ha : h * γ⁻¹ * h⁻¹ ∈ gammaN N := by
      have := (gammaN_normal N).conj_mem γ⁻¹ ((gammaN N).inv_mem hγ) h
      simpa [mul_assoc] using this
    refine ⟨Quotient.mk _ ⟨h * γ⁻¹ * h⁻¹, ha⟩, ?_⟩
    have e : (q * h * γ) * h⁻¹ * (h * γ⁻¹ * h⁻¹) = q := by group
    unfold IsCellK
    rw [cuspRow_mk_eq, cuspRow_mk_eq]
    simp only
    rw [e]
    exact ⟨hq.1, hq.2⟩

/-- **Different faces: no cell** (the series at the cusp `planeFaceRepr x` restricted to the face `planeFaceRepr i`, `x ≠ i`). -/
theorem no_cell_of_ne {i x : PlaneFaces N} (hix : x ≠ i) :
    ∀ c : Ck N (planeFaceRepr x * (planeFaceRepr i)⁻¹), ¬ IsCellK N (planeFaceRepr x * (planeFaceRepr i)⁻¹) c := by
  intro c hc
  have h := (cell_exists_iff N (planeFaceRepr i) (planeFaceRepr x)).1 ⟨c, hc⟩
  apply hix
  have e1 : (Quotient.mk (planeFaceSetoid N) (planeFaceRepr i) : PlaneFaces N) = i := Quotient.out_eq i
  have e2 : (Quotient.mk (planeFaceSetoid N) (planeFaceRepr x) : PlaneFaces N) = x := Quotient.out_eq x
  rw [← e1, ← e2]
  exact (Quotient.sound h).symm

open UpperHalfPlane ModularForm in
/-- The slash by a Levi block that lies in the level group fixes the cusp form. -/
theorem cuspSlash_of_mem {n : ℕ} (A : SL(2, ℤ)) (hA : (Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ) ∈ leviGroup N)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) : cuspSlash N n A f = f := by
  apply DFunLike.ext
  intro z
  rw [coe_cuspSlash]
  have h := SlashInvariantFormClass.slash_action_eq f _ hA
  exact congrFun h z

/-- **The cell of the series at a cusp, seen from the same cusp, is the identity coset**: `k = h h⁻¹`; its matrix lies in `Γ(N) ∩ P(ℤ)`, has bottom entry `1`,
and the slash of `f` by its Levi block is `f`. -/
theorem cell_self (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) :
    ∃ (c₀ : Ck N (h * h⁻¹)) (hc : IsCellK N (h * h⁻¹) c₀)
      (h22 : ((cellMat N (h * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1),
      cuspSlash N n (leviBlock (cellMat N (h * h⁻¹) c₀) (cellMat_mem_planeStab N (h * h⁻¹) hc h22)) f = f := by
  obtain ⟨c₀, hc⟩ := (cell_exists_iff N h h).2 ⟨1, planeBorel.one_mem, 1, (gammaN N).one_mem, by simp⟩
  have hM : cellMat N (h * h⁻¹) c₀ = (Quotient.out c₀).1 := by
    unfold cellMat
    exact (congrArg (fun m => m * (Quotient.out c₀).1) (mul_inv_cancel h)).trans (one_mul _)
  have hΓ : cellMat N (h * h⁻¹) c₀ ∈ gammaN N := by rw [hM]; exact (Quotient.out c₀).2
  have hst0 : ((cellMat N (h * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := by
    have := hc.1; rw [cuspRow_out] at this; exact this
  have hst1 : ((cellMat N (h * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
    have := hc.2; rw [cuspRow_out] at this; exact this
  have hst : cellMat N (h * h⁻¹) c₀ ∈ planeStab := mem_planeStab_of_gammaN hN hΓ hst0 hst1
  have h22 : ((cellMat N (h * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := hst.2.2
  refine ⟨c₀, hc, h22, ?_⟩
  obtain ⟨g, hg, hge⟩ := leviIn_gammaN N _ hΓ hst
  refine cuspSlash_of_mem N _ ?_ f
  have : (Matrix.SpecialLinearGroup.mapGL ℝ (leviBlock (cellMat N (h * h⁻¹) c₀)
      (cellMat_mem_planeStab N (h * h⁻¹) hc h22)) : GL (Fin 2) ℝ) = g := by
    apply Units.ext
    rw [coe_mapGL_leviBlock, hge]
  rw [this]
  exact hg

end TernaryPeriodPolynomials.Argument.FormClassK
