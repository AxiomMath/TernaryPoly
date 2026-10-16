module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.PropC5Assembly
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LineEdgeAlign

@[expose] public section


/-!
# The alignment `QDi ≃ QDiLit` and Proposition C.5 from Stokes alone

Formalized by Claude Sonnet 5.5.

`qdiLitEquiv N n i : QDi N n i ≃ₗ QDiLit N n i` is the composite of the restriction of the bijection `toLiteral` (`H²(·, E^∨) ≅ H²(·, E*)`) to the cuspidal groups
`𝒞_Q(E^∨) → 𝒞_Q(E*)` (`Submodule.equivMapOfInjective`; `dualCuspidalQLiteral` is by definition the image of `dualCuspidalQ`) with the Hochschild-Serre edge equivalence
`dualCuspidalLiteralEquiv`.  `qdiLitEquiv_val` / `qdiLitEquiv_dualRQ`: its `H¹(N_{Q'}, E*)`-coordinate is the edge `edgeL` of `toLiteral` of the class, in particular of the line
restriction `r_Q c'` of a dual Eisenstein class `c'`; this is the compatibility with `dualRQ`.  `qdiAlignmentInst` is the resulting `QDiAlignment`, so
`C5LevelInputs` reduces to `StokesAtLevel` for this alignment (`propC5_gammaN_of_stokes`).

Comparison with the `QDiLitEquiv : QDiLit ≃ QDiDual`: `QDiDual N n i` is the cuspidal group of the contragredient of the Levi module `H¹(N_{Q'_i}, E_n)`, a group of
`H¹(Γ₂(N), ·)`-classes, whereas the `QDi N n i = 𝒞_Q(E^∨)` is a subspace of `H²(Γ(N) ∩ h⁻¹Qh, E^∨)`.  They are different objects, so `QDiDual` is NOT `QDi`; `qdiLitEquiv`
and `QDiLitEquiv` have different sources, and `qdiLitEquiv` followed by `QDiLitEquiv` is a (non-canonical-scalar) iso `QDi ≃ QDiDual` that is not needed for the assembly.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual

section Align

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The alignment `𝒞_Q(E^∨) ≃ QDiLit`**: `toLiteral` on the cuspidal groups, then the Hochschild-Serre edge. -/
def qdiLitEquiv (i : LineFaces N) : QDi N n i ≃ₗ[ℂ] QDiLit N n i :=
  (Submodule.equivMapOfInjective (toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n)
      (toLiteral_bijective (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n).1 (dualCuspidalQ N n i.rep)).trans
    (dualCuspidalLiteralEquiv N n i.rep)

/-- The `H¹(N_{Q'}, E*)`-coordinate of the alignment is the edge of `toLiteral` of the class. -/
theorem qdiLitEquiv_val (i : LineFaces N) (x : QDi N n i) :
    ((qdiLitEquiv N n i x : QDiLit N n i) : groupCohomology.H1 (lineFaceRadH1Lit N n i.rep)) =
      edgeL N n i.rep (cuspToKer N n i.rep
        ⟨toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n x.1, Submodule.mem_map_of_mem x.2⟩) := rfl

variable {N n}

theorem dualRQ_apply_val (hN : 3 ≤ N) (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) (i : LineFaces N) :
    ((dualRQ hN hn c) i).1 = resLine i c.1 := by
  have e : (dualRQ hN hn c) i = (∑ j : LineFaces N, DirectSum.lof ℂ (LineFaces N) (fun i => QDi N n i) j
      ⟨resLine j c.1, resLine_mem hN hn j c⟩) i := rfl
  rw [e, DFinsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [DirectSum.lof_apply]
  · intro j _ hj
    rw [DirectSum.lof_eq_of, DirectSum.of_apply, dite_eq_right hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem edge_toLiteral_congr (i : LineFaces N)
    {x y : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N i.rep))))} (hxy : x = y)
    (hx : toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n x ∈ dualCuspidalQLiteral N n i.rep)
    (hy : toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n y ∈ dualCuspidalQLiteral N n i.rep) :
    edgeL N n i.rep (cuspToKer N n i.rep ⟨toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n x, hx⟩) =
      edgeL N n i.rep (cuspToKer N n i.rep ⟨toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n y, hy⟩) := by
  subst hxy; rfl

/-- **Compatibility with `dualRQ`**: the line coordinate of a dual Eisenstein class goes to the edge of `toLiteral (r_Q c')`. -/
theorem qdiLitEquiv_dualRQ (hN : 3 ≤ N) (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) (i : LineFaces N)
    (hmem : toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n (resLine i c.1) ∈ dualCuspidalQLiteral N n i.rep) :
    ((qdiLitEquiv N n i ((dualRQ hN hn c) i) : QDiLit N n i) : groupCohomology.H1 (lineFaceRadH1Lit N n i.rep)) =
      edgeL N n i.rep (cuspToKer N n i.rep
        ⟨toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n (resLine i c.1), hmem⟩) := by
  rw [qdiLitEquiv_val]
  exact edge_toLiteral_congr i (dualRQ_apply_val hN hn c i) _ _

end Align

variable {M n : ℕ} [NeZero M]

/-- **The canonical alignment instance** `QDiAlignment M n`. -/
def qdiAlignmentInst : QDiAlignment M n where
  eQ := qdiLitEquiv M n

/-- Proposition C.5 inputs reduce to Stokes alone. -/
def C5LevelInputs.ofStokes (hM : 3 ≤ M) (hn : 4 ≤ n) (hS : StokesAtLevel hM hn (qdiAlignmentInst (M := M) (n := n))) :
    C5LevelInputs hM hn where
  align := qdiAlignmentInst
  stokes := hS

/-- **Proposition C.5 for `Γ(N)` from Stokes alone**: the alignment is instantiated; the only input is `StokesAtLevel` at the common level `M`. -/
theorem propC5_gammaN_of_stokes {N : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) (hNM : N ∣ M) (hM : 3 ≤ M)
    (hS : StokesAtLevel hM hn (qdiAlignmentInst (M := M) (n := n))) : PropC5GammaN N n :=
  propC5_gammaN_assembled hN hn hNM hM (C5LevelInputs.ofStokes hM hn hS)

/-- The same at the common level `lcm(N, 6)`. -/
theorem propC5_gammaN_of_stokes_lcm {N : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n)
    (hS : StokesAtLevel (three_le_lcm hN) hn (qdiAlignmentInst (M := Nat.lcm N 6) (n := n))) : PropC5GammaN N n :=
  propC5_gammaN_of_stokes hN hn (Nat.dvd_lcm_left N 6) (three_le_lcm hN) hS

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
