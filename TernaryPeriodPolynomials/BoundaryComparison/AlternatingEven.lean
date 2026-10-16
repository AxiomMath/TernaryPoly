module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Transitivity3
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Parameters
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.RelativeVertexCohomology
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBB
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBG
public import TernaryPeriodPolynomials.GroupCohomology.Relative.LeviCohomology
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstructionSequences
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyPlane
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyLine

@[expose] public section


/-!
# Proposition 5.1 (`prop:alternating-even`): the internal claims of its proof

Formalized by Claude Sonnet 5.5.

Every alternating
even-degree solution belongs to `U_n`.  The proof works in `K† = B₃ K B₃⁻¹`, the stabilizer of the
covector `e₃*` modulo three (`ModThreeGoodAction.K3`), with `E = Sym^n((ℚ³)*)` (determinant exponent `0`)
and the following steps, each of which is stated below with the library theorem proving it (the library
builds the same argument; `TernaryPoly.RelativeVertexCohomology.homogeneous_extension` is the assembled
conclusion):

* `relative_graph_orbits`: the bad vertices and edges form the orbits of `K†` of the
  coordinate bad line `ℚe₁`, the coordinate bad plane `ℚe₁+ℚe₂`, and the two edge types (bad line in bad plane,
  bad line in good plane `ℚe₁+ℚe₃`); a bad plane contains only bad lines, so the list is exhaustive.
* `stabilizer_forms`: the explicit matrices of `H_P, H_L, H_BB, H_BG`.
* `plane_radical_H2`, `line_radical_H2` (`H²` column of `tab:radical-cohomology`, with the
  top-cohomology formula `H²(N,E) = E_N ⊗ ∧²(N⊗ℚ)*`): `H²(N_P,E) ≅ det(A)^{-1} Sym^n(x,y)*`, and
  `H²(N_L,E) = ℚ` with the diagonal sign `(ε₁,ε₂)` acting by `ε₁^{-n-2} ε₂`.
* `plane_H1_central_sign`, `line_H1_sign`: the central `-I₂` acts by `-1` on `H¹(N_P,E)`
  and the independent line sign by `-1` on `H¹(N_L,E)`, for `n` even (plane).
* `plane_H2_fixed_zero`, `line_H2_fixed_zero` ("positive binary degree kills the `H²` invariants").
* `vertex_stabilizer_H2_vanishing`: `H²(H_P,E) = H²(H_L,E) = 0`.
* `edge_stabilizer_H1_vanishing`: `H¹(H_BB,E) = H¹(H_BG,E) = 0` for `n` even.
* `relative_graph_sequences`: the exact sequences of `K†`-modules
  `0 → St↑ → St → Q₀ → 0` and `0 → Q₀ → ℚ[edges] → ℚ[vertices] → 0` of the relative graph.
* `extension_to_full_graph`: `Hom_K(St,E) → Hom_K(St↑,E)` is surjective.

**What is not stated here.**  The weights of `tab:edge-weights` and the `H¹` column of
`tab:radical-cohomology` (the identification `H¹(N_P,E) ≅ Sym^{n+1}(x,y)*` as a Levi module) are the
*method* of the paper for the vanishing statements; the library proves the vanishings directly
(`bb_H1_zero`, `bg_H1_zero`, `planeCross_H1_zero`) without stating the weights.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AlternatingEven

open ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerConjugacy
open RelativeStabilizerMatrices RelativeStabilizerParameters

theorem good3_mono {L P : RationalSubspace} (h : L ≤ P) (hL : Good3 L) : Good3 P :=
  let ⟨v, hv, hn⟩ := hL
  ⟨v, h hv, hn⟩

/-- **The relative graph `𝒯† \ 𝒯`.** `K†` acts transitively on the bad lines (orbit of
`L0 = ℚe₁`), on the bad planes (orbit of `P0 = ℚe₁+ℚe₂`), on the flags of a bad line in a bad plane (orbit of
`(L0,P0)`) and on the flags of a bad line in a good plane (orbit of `(L0,P1)`, `P1 = ℚe₁+ℚe₃`); a bad plane
contains only bad lines, so a flag with a bad end is of one of these two types. -/
theorem relative_graph_orbits :
    (∀ L : RationalSubspace, Module.finrank ℚ L = 1 → ¬Good3 L → ∃ k : K3, act3 k L0 = L) ∧
    (∀ P : RationalSubspace, Module.finrank ℚ P = 2 → ¬Good3 P → ∃ k : K3, act3 k P0 = P) ∧
    (∀ L P : RationalSubspace, Module.finrank ℚ L = 1 → Module.finrank ℚ P = 2 → L ≤ P → ¬Good3 P →
      ∃ k : K3, act3 k L0 = L ∧ act3 k P0 = P) ∧
    (∀ L P : RationalSubspace, Module.finrank ℚ L = 1 → Module.finrank ℚ P = 2 → L ≤ P → ¬Good3 L →
      Good3 P → ∃ k : K3, act3 k L0 = L ∧ act3 k P1 = P) ∧
    (∀ L P : RationalSubspace, L ≤ P → ¬Good3 P → ¬Good3 L) ∧
    (∀ L P : RationalSubspace, L ≤ P → ¬(Good3 L ∧ Good3 P) →
      ¬Good3 P ∨ (¬Good3 L ∧ Good3 P)) := by
  refine ⟨RelativeOrbitTransitivity3.bad_line, RelativeOrbitTransitivity3.bad_plane,
    RelativeOrbitTransitivity3.bad_bad, RelativeOrbitTransitivity3.bad_good,
    fun L P hle hP hL => hP (good3_mono hle hL), ?_⟩
  intro L P _ h
  by_cases hP : Good3 P
  · exact Or.inr ⟨fun hL => h ⟨hL, hP⟩, hP⟩
  · exact Or.inl hP

/-- **The explicit stabilizers.** In `K†`: `H_P = {((A,u),(0,1))}` (the stabilizer of the bad
plane), `H_L = {(η,u;0,D)}` with `η = ±1` and `D ∈ GL₂(ℤ)` with `(0,1)D ≡ (0,1) mod 3`, `H_BB =
{(η₁ a b; 0 η₂ c; 0 0 1)}` and `H_BG = {(η₁ a b; 0 η₂ 0; 0 3k 1)}` with independent signs `η_i = ±1`
(`planeElement`, `lineElement`, `bbElement`, `bgElement` are these matrices; `HP, HL, HBB, HBG` the stabilizers
in `K†` of `P0`, `L0`, `(L0,P0)`, `(L0,P1)`). -/
theorem stabilizer_forms :
    (∀ g : IntegralGL, HP g ↔ ∃ (A : GL2) (u : Fin 2 → ℤ), g = planeElement A u) ∧
    (∀ g : IntegralGL, HL g ↔ ∃ (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2),
      GammaEntries D.val ∧ g = lineElement ε u D) ∧
    (∀ g : IntegralGL, HBB g ↔ ∃ (ε₀ ε₁ : ℤˣ) (a b c : ℤ), g = bbElement ε₀ ε₁ a b c) ∧
    (∀ g : IntegralGL, HBG g ↔ ∃ (ε₀ ε₁ : ℤˣ) (a b k : ℤ), g = bgElement ε₀ ε₁ a b k) :=
  ⟨hp_iff_parameter, hl_iff_parameter, hbb_iff_parameter, hbg_iff_parameter⟩


open RadicalTopCohomology RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice

/-- **`H²` column of `tab:radical-cohomology`, plane radical.**
`H²(N_P,E) ≅ det(A)^{-1} Sym^n(x,y)*`: an identification of the second cohomology of the plane radical
`N_P = ⟨U₁₃,U₂₃⟩ ≅ ℤ²` with binary forms of degree `n` (coinvariants `E_{N_P} = ℚ[x,y]_n`), under
which the Levi element `A ∈ GL₂(ℤ)` acts by the inverse substitution `A⁻¹` twisted by `det(A)^{-1}`. -/
theorem plane_radical_H2 (n : ℕ) :
    ∃ e : groupCohomology (planeRep n) 2 ≃ₗ[ℚ] BinaryH n,
      ∀ (A : GL2) (v : groupCohomology (planeRep n) 2),
        (e (planeH2Action n A v) : MvPolynomial (Fin 2) ℚ) =
          ((A.val.det : ℚ)⁻¹) •
            binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
              (e v : MvPolynomial (Fin 2) ℚ) := by
  refine ⟨(planeH2Iso n).toLinearEquiv.trans (actualPlaneQuotientEquiv n), fun A v => ?_⟩
  have h := planeH2Iso_action n A v
  change (actualPlaneQuotientEquiv n ((planeH2Iso n).hom (planeH2Action n A v)) :
    MvPolynomial (Fin 2) ℚ) = _
  rw [h, map_smul, Submodule.coe_smul, planeQuotientLevi_intertwine]
  rfl

/-- **`H²` column of `tab:radical-cohomology`, line radical.**
`H²(N_L,E)` is the line `ℚ` (coinvariants `E_{N_L} = ℚx^n`), on which the diagonal sign `(ε₁,ε₂)` of the Levi
`(η,D)` acts by `ε₁^{-n-2} ε₂` (the character `η^{-n-2} det(D)` of the table, `D = diag(ε₂,1)`). -/
theorem line_radical_H2 (n : ℕ) :
    ∃ e : groupCohomology (lineRep n) 2 ≃ₗ[ℚ] ℚ,
      ∀ (ε : ℤˣ × ℤˣ) (v : groupCohomology (lineRep n) 2),
        e (lineH2Action n ε v) = (unitScalar ε.1⁻¹ ^ (n + 2) * unitScalar ε.2) * e v := by
  refine ⟨(lineH2Iso n).toLinearEquiv.trans (actualLineScalarEquiv n), fun ε v => ?_⟩
  have h := lineH2Iso_action n ε v
  change actualLineScalarEquiv n ((lineH2Iso n).hom (lineH2Action n ε v)) = _
  rw [h, map_smul, lineQuotientDiagonal_intertwine, lineRootDual_formula]
  rw [smul_eq_mul, ← mul_assoc]
  congr 1
  ring

/-- Every vector of `H²(N_P,E)` fixed by the whole Levi action is zero ("positive binary degree kills the
`H²` invariants"). -/
theorem plane_H2_fixed_zero (n : ℕ) (v : groupCohomology (planeRep n) 2)
    (hv : ∀ M : GL2, planeH2Action n M v = v) : v = 0 :=
  planeH2_fixed_zero n v hv

/-- The same for the line radical and its diagonal signs. -/
theorem line_H2_fixed_zero (n : ℕ) (v : groupCohomology (lineRep n) 2)
    (hv : ∀ ε : ℤˣ × ℤˣ, lineH2Action n ε v = v) : v = 0 :=
  lineH2_fixed_zero n v hv

/-- **Central sign on `H¹` of the plane radical:** for even `n`, the central element `-I₂`
of the Levi `GL₂(ℤ)` acts by `-1` on `H¹(N_P,E)`. -/
alias plane_H1_central_sign := RelativeVertexCohomology.planeCross_sign

/-- **Line sign on `H¹` of the line radical:** the independent line sign `η = -1` acts by
`-1` on `H¹(N_L,E)`. -/
alias line_H1_sign := RelativeVertexCohomology.lineCross_sign

/-- **`H²(H_P,E) = H²(H_L,E) = 0`.**  Hochschild-Serre for the radical extension, using that
the Levi groups `GL₂(ℤ)` and `{±1} × Γ₂` are virtually free (`H² = 0`), the central sign on `H¹`, and the
vanishing of the Levi invariants of `H²(N,E)`; `E = Sym^n((ℚ³)*)` with the left inverse-substitution action. -/
theorem vertex_stabilizer_H2_vanishing (n : ℕ) :
    (Even n → CategoryTheory.Limits.IsZero
      (groupCohomology (RelativeVertexCohomology.planeMatrixPolynomial n) 2)) ∧
    CategoryTheory.Limits.IsZero
      (groupCohomology (RelativeVertexCohomology.lineMatrixPolynomial n) 2) :=
  ⟨fun hn => RelativeVertexCohomology.planeMatrix_H2_zero n hn
      RelativeLeviCohomology.plane_H2_zero,
    RelativeVertexCohomology.lineMatrix_H2_zero n RelativeLeviCohomology.line_H2_zero⟩

/-- **`H¹(H_BB,E) = H¹(H_BG,E) = 0` for even `n`.**  (The paper derives this from the
weights of `tab:edge-weights` through the five-term sequence; the library eliminates the root values of a
normalized cocycle directly.) -/
theorem edge_stabilizer_H1_vanishing (n : ℕ) (hn : Even n) :
    CategoryTheory.Limits.IsZero (groupCohomology (RelativeEdgeCohomologyActions.bbRep n) 1) ∧
    CategoryTheory.Limits.IsZero (groupCohomology (RelativeEdgeCohomologyActions.bgRep n) 1) :=
  ⟨RelativeEdgeCohomologyBB.bb_H1_zero n hn, RelativeEdgeCohomologyBG.bg_H1_zero n hn⟩

/-- **The exact sequences of the relative graph**, as `K`-modules (`K ≅ K†` by conjugation):
`0 → St↑ → St → Q₀ → 0` and `0 → Q₀ → ℚ[relative edges] → ℚ[relative vertices] → 0`. -/
theorem relative_graph_sequences :
    RelativeExtObstructionSequences.cycleSequence.ShortExact ∧
      RelativeExtObstructionSequences.relativeSequence.ShortExact :=
  ⟨RelativeExtObstructionSequences.cycleSequence_shortExact,
    RelativeExtObstructionSequences.relativeSequence_shortExact⟩

/-- **Extension to the full graph:** for even `n`, every `K`-equivariant polynomial-valued
functional on `St↑` extends to a `K`-equivariant functional on `St` (surjectivity of
`Hom_K(St,E) → Hom_K(St↑,E)`). -/
alias extension_to_full_graph := RelativeVertexCohomology.homogeneous_extension

end TernaryPeriodPolynomials.Argument.Statements.AlternatingEven
