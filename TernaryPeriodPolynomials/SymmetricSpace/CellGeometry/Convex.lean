module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Stabilizer
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Reduction
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section


/-!
# Appendix B cell calculation: the standard ternary cell is convex, hence contractible

Formalized by Claude Sonnet 5.5.  Paper: "Both this core and `W₃` are contractible."

What the library builds (all literal, in Gram coordinates):
* `Tcell_convex`, `Tcell_contractible`: the standard ternary top cell `{A pos. def., A_ii = 1, vᵗAv ≥ 1 on ℤ³∖0}` is the intersection of the (convex) cone of positive definite forms with
  an affine subspace and with the half-spaces `vᵗAv ≥ 1`, hence convex; it is nonempty, hence contractible.
* `voronoi_convex`, `voronoi_contractible`: the Voronoi cell of `0` for `C(t)` is a convex polygon.
* `BinWR_eq_union_edges`: the binary well-rounded locus `W₂ = {C : BinWR C}` is the union of the `GL₂(ℤ)`-translates `Dᵗ C(t) D`, `|t| ≤ 1/2`, of the standard edge.
* `Tparam`: the cell is parametrized by `(t, w)` (a bijection from the Voronoi fibration over the standard edge), the chart `(w, t) ↦ (Cw, t)` having positive Jacobian.

What is NOT built (recorded precisely): the cellular structure of `W₂` as a tree (vertices: the hexagonal forms; edges: the translates of the standard edge) and its
contractibility, hence the contractibility of `ℝ² × W₂`; the ternary retract `W₃` as a cell complex (its contractibility is Ash's theorem, a statement about the whole
well-rounded retract, not about the standard cell); the equivariant subdivision and the cellular chain complexes.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix

theorem posDefQ_convex {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : PosDefQ A) (hB : PosDefQ B) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : PosDefQ (a • A + b • B) := by
  refine ⟨by rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hA.1, hB.1], fun v hv => ?_⟩
  have h1 := hA.2 v hv
  have h2 := hB.2 v hv
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with h | h
  · have : b = 1 := by linarith
    subst this
    rw [← h]
    nlinarith
  · nlinarith [mul_nonneg hb h2.le]

/-- **The standard ternary top cell is convex.** -/
theorem Tcell_convex : Convex ℝ Tcell := by
  intro A hA B hB a b ha hb hab
  obtain ⟨hAp, hA0, hA1, hA2, hAm⟩ := hA
  obtain ⟨hBp, hB0, hB1, hB2, hBm⟩ := hB
  refine ⟨posDefQ_convex hAp hBp ha hb hab, ?_, ?_, ?_, ?_⟩
  · simp [hA0, hB0, hab]
  · simp [hA1, hB1, hab]
  · simp [hA2, hB2, hab]
  · intro v hv
    have h1 := hAm v hv
    have h2 := hBm v hv
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **The standard ternary top cell is contractible.** -/
theorem Tcell_contractible : ContractibleSpace Tcell :=
  Tcell_convex.contractibleSpace ⟨1, one_mem_Tcell⟩

/-- The Voronoi cell of `0` for `C(t)` is convex (an intersection of half-planes). -/
theorem voronoi_convex {t : ℝ} (ht : |t| ≤ 1 / 2) : Convex ℝ (Voronoi (Ct t)) := by
  intro w1 h1 w2 h2 a b ha hb hab
  rw [mem_Voronoi_iff ht] at h1 h2 ⊢
  intro z
  have e1 := h1 z
  have e2 := h2 z
  simp only [quad_Ct, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

theorem voronoi_contractible {t : ℝ} (ht : |t| ≤ 1 / 2) : ContractibleSpace (Voronoi (Ct t)) :=
  (voronoi_convex ht).contractibleSpace ⟨0, by
    refine (mem_Voronoi_iff ht 0).mpr (fun z => ?_)
    have h0 : quad (Ct t) 0 = 0 := by simp [quad]
    have := quad_Ct_nonneg (t := t) (by linarith [abs_nonneg t]) (0 - intVec z)
    linarith⟩

/-- **The binary well-rounded locus is the union of the `GL₂(ℤ)`-translates of the standard edge** (`W₂ = ⋃_D Dᵗ {C(t)} D`). -/
theorem BinWR_eq_union_edges : {C : Mat2 | BinWR C} =
    {C | ∃ (t : ℝ) (D D' : IMat2), |t| ≤ 1 / 2 ∧ D * D' = 1 ∧ D' * D = 1 ∧ C = (castMat D)ᵀ * Ct t * castMat D} := by
  ext C
  constructor
  · intro hC
    obtain ⟨t, ht, D, D', h1, h2, rfl⟩ := BinWR_reduce hC
    exact ⟨t, D, D', ht, h1, h2, rfl⟩
  · rintro ⟨t, D, D', ht, h1, h2, rfl⟩
    exact BinWR_conj ht D D' h1 h2

/-- The parameter space of the standard cell: the Voronoi fibration over the standard edge. -/
def Tfib : Set (ℝ × Vec2) := {p | |p.1| ≤ 1 / 2 ∧ p.2 ∈ Voronoi (Ct p.1)}

/-- **The standard cell is parametrized by `(t, w)`**: `(t, w) ↦ G(w, C(t))` is a bijection of the Voronoi fibration over the standard edge onto the cell. -/
def Tparam : Tfib ≃ Tcell :=
  Equiv.ofBijective (fun p => ⟨Gmat p.1.2 (Ct p.1.1), Gmat_mem_Tcell p.2.1 p.2.2⟩) (by
    constructor
    · rintro ⟨⟨t, w⟩, ht, hw⟩ ⟨⟨t', w'⟩, ht', hw'⟩ h
      have h' : Gmat w (Ct t) = Gmat w' (Ct t') := congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := Gmat_Ct_injective ht h'
      subst e1; subst e2
      rfl
    · rintro ⟨A, hA⟩
      obtain ⟨t, ht, w, hw, rfl⟩ := Tcell_eq_Gmat hA
      exact ⟨⟨(t, w), ht, hw⟩, rfl⟩)

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
