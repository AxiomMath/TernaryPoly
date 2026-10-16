module

public import TernaryPeriodPolynomials.BoundaryComparison.AlternatingEven
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.Cohomology
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.RelativeVertexCohomology

@[expose] public section


/-!
# the extension obstruction in alternating even degree, and the explicit stabilizers

Formalized by Claude Sonnet 5.5.

* `stabilizers_explicit`: `H_P, H_L, H_BB, H_BG` with the displayed matrices written out entrywise (`!![ ... ]`), for the stabilizers `HP, HL, HBB, HBG` of the coordinate bad plane, bad line and the two flags in `K†` (the stabilizer of `e₃*` modulo three).
* `ext_Q0_vanishing` ("the four vanishings make `Ext¹_{K†}(Q₀,E) = 0`"): for even `n`, `Ext¹_K(Q₀, E_n) = 0`, `Q₀ = St/St↑`, from the four stabilizer vanishings `H¹(H_BB), H¹(H_BG), H²(H_L), H²(H_P)` (all four proved for the actual stabilizers).
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerMatrices RelativeStabilizerParameters

/-- **The explicit stabilizers, entry by entry.**  With `η, η₁, η₂ = ±1`:
`H_P = {[[A, u], [0, 1]]}` (`A ∈ GL₂(ℤ)`, `u ∈ ℤ²`), `H_L = {[[η, u], [0, D]]}` (`u` a row, `D ∈ GL₂(ℤ)` with `(0,1) D ≡ (0,1) mod 3`),
`H_BB = {[[η₁, a, b], [0, η₂, c], [0, 0, 1]]}`, `H_BG = {[[η₁, a, b], [0, η₂, 0], [0, 3k, 1]]}`, all entries integral. -/
theorem stabilizers_explicit :
    (∀ g : IntegralGL, HP g ↔ ∃ (A : Mat2) (u : Fin 2 → ℤ), IsUnit A.det ∧
      g.val = !![A 0 0, A 0 1, u 0; A 1 0, A 1 1, u 1; 0, 0, 1]) ∧
    (∀ g : IntegralGL, HL g ↔ ∃ (η : ℤ) (u : Fin 2 → ℤ) (D : Mat2), IsSign η ∧ IsUnit D.det ∧
      (D 1 0 : ZMod 3) = 0 ∧ (D 1 1 : ZMod 3) = 1 ∧
      g.val = !![η, u 0, u 1; 0, D 0 0, D 0 1; 0, D 1 0, D 1 1]) ∧
    (∀ g : IntegralGL, HBB g ↔ ∃ η₁ η₂ a b c : ℤ, IsSign η₁ ∧ IsSign η₂ ∧
      g.val = !![η₁, a, b; 0, η₂, c; 0, 0, 1]) ∧
    (∀ g : IntegralGL, HBG g ↔ ∃ η₁ η₂ a b k : ℤ, IsSign η₁ ∧ IsSign η₂ ∧
      g.val = !![η₁, a, b; 0, η₂, 0; 0, 3 * k, 1]) := by
  obtain ⟨hP, hL, hBB, hBG⟩ := TernaryPeriodPolynomials.Argument.Statements.AlternatingEven.stabilizer_forms
  have sgn : ∀ ε : ℤˣ, IsSign (ε : ℤ) := fun ε => Int.isUnit_iff.mp ε.isUnit
  have unit_of_sign : ∀ z : ℤ, IsSign z → ∃ ε : ℤˣ, (ε : ℤ) = z := by
    rintro z (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩
  refine ⟨fun g => (hP g).trans ?_, fun g => (hL g).trans ?_, fun g => (hBB g).trans ?_, fun g => (hBG g).trans ?_⟩
  · constructor
    · rintro ⟨A, u, rfl⟩
      exact ⟨A.val, u, (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit, by rw [planeElement_val]; rfl⟩
    · rintro ⟨A, u, hA, hg⟩
      refine ⟨Matrix.GeneralLinearGroup.mk'' A hA, u, Units.ext (hg.trans ?_)⟩
      rw [planeElement_val, Matrix.GeneralLinearGroup.val_mk'']; rfl
  · constructor
    · rintro ⟨ε, u, D, hD, rfl⟩
      exact ⟨ε, u, D.val, sgn ε, (Matrix.isUnit_iff_isUnit_det _).mp D.isUnit, hD.1, hD.2, by rw [lineElement_val]; rfl⟩
    · rintro ⟨η, u, D, hη, hD, h1, h2, hg⟩
      obtain ⟨ε, hε⟩ := unit_of_sign η hη
      refine ⟨ε, u, Matrix.GeneralLinearGroup.mk'' D hD, ⟨?_, ?_⟩, Units.ext (hg.trans ?_)⟩
      · rw [Matrix.GeneralLinearGroup.val_mk'']; exact h1
      · rw [Matrix.GeneralLinearGroup.val_mk'']; exact h2
      · rw [lineElement_val, Matrix.GeneralLinearGroup.val_mk'', hε]; rfl
  · constructor
    · rintro ⟨ε₀, ε₁, a, b, c, rfl⟩
      exact ⟨ε₀, ε₁, a, b, c, sgn ε₀, sgn ε₁, by rw [bbElement_val]; rfl⟩
    · rintro ⟨η₁, η₂, a, b, c, h1, h2, hg⟩
      obtain ⟨ε₀, hε₀⟩ := unit_of_sign η₁ h1
      obtain ⟨ε₁, hε₁⟩ := unit_of_sign η₂ h2
      exact ⟨ε₀, ε₁, a, b, c, Units.ext (hg.trans (by rw [bbElement_val, hε₀, hε₁]; rfl))⟩
  · constructor
    · rintro ⟨ε₀, ε₁, a, b, k, rfl⟩
      exact ⟨ε₀, ε₁, a, b, k, sgn ε₀, sgn ε₁, by rw [bgElement_val]; rfl⟩
    · rintro ⟨η₁, η₂, a, b, k, h1, h2, hg⟩
      obtain ⟨ε₀, hε₀⟩ := unit_of_sign η₁ h1
      obtain ⟨ε₁, hε₁⟩ := unit_of_sign η₂ h2
      exact ⟨ε₀, ε₁, a, b, k, Units.ext (hg.trans (by rw [bgElement_val, hε₀, hε₁]; rfl))⟩

open CategoryTheory RelativeExtObstructionSequences in
/-- **The four vanishings make `Ext¹_K(Q₀, E) = 0`** for `E = Sym^n((ℚ³)*)` (determinant exponent `0`) and `n` even, `Q₀ = St/St↑`
the quotient of the cycle modules of the full and restricted graphs (in the original coordinates `K ≅ K†`). -/
theorem ext_Q0_vanishing (n : ℕ) (hn : Even n) :
    Subsingleton (Abelian.Ext.{1} QuotientCyclesRep (RelativeExtObstruction.coefficientRep n) 1) :=
  RelativeExtObstruction.quotientExt_one_subsingleton _
    (RelativeShapiro.relativeEdges_ext _ (RelativeEdgeCohomology.hbb_H1_zero n hn)
      (RelativeEdgeCohomology.hbg_H1_zero n hn))
    (RelativeShapiro.relativeVertices_ext _ (RelativeVertexCohomology.hl_H2_zero n)
      (RelativeVertexCohomology.hp_H2_zero n hn))

end TernaryPeriodPolynomials.Argument.Identities
