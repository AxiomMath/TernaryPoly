module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.OrientationSentence
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Stabilizer
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Stab

@[expose] public section


/-!
# The full stabilizer of the standard top cell: the 48 signed permutations

Formalized by Claude Sonnet 5.5.

`stabT0_eq`: `{g ∈ GL₃(ℤ) | g · T₀ = T₀}` is the set of signed permutation matrices `AppendixBResidue.Geometry.SignedPerms`, so
`stabT0_ncard : #stabilizer = 48` (the count `signedPerms_card` is reused).  `avgGenT0_stabilizer`: the orientation-character-weighted average of
the translates of the generator `[T₀]` over this full stabilizer is `[T₀]`, i.e. the "averaged standard top-cell generator" of the paper
for the actual stabilizer.
-/

open CategoryTheory Finsupp Matrix
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry
open TernaryPeriodPolynomials.FreeResolution

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical Pointwise

theorem line_colVec_mem (k : Fin 6) : Line.mk (colVec k) ∈ T0set := by
  fin_cases k
  · simp [T0set, colVec, e0]
  · refine Finset.mem_insert.mpr (Or.inl (Line.mk_eq_mk.mpr (Or.inr ?_)))
    funext i; fin_cases i <;> simp [colVec, e0]
  · simp [T0set, colVec, e1]
  · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Line.mk_eq_mk.mpr (Or.inr ?_)))))
    funext i; fin_cases i <;> simp [colVec, e1]
  · simp [T0set, colVec, e2]
  · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Line.mk_eq_mk.mpr (Or.inr ?_))))))
    funext i; fin_cases i <;> simp [colVec, e2]

theorem mv_basis (g : GeneralEisenstein.IntegralGL3) (i : Fin 3) (r : Fin 3) :
    (mv g (Pi.single i 1 : Vec)) r = (g : IMat3) r i := by
  simp [mv, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem e_eq_single : (e0 : Vec) = Pi.single 0 1 ∧ (e1 : Vec) = Pi.single 1 1 ∧ (e2 : Vec) = Pi.single 2 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [e0, e1, e2]

/-- A signed permutation matrix maps the standard top cell to itself. -/
theorem smul_T0set_of_signedPerm (g : GeneralEisenstein.IntegralGL3) (hg : (g : IMat3) ∈ SignedPerms) :
    g • T0set = T0set := by
  unfold SignedPerms at hg
  obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hg
  have hcol : ∀ (i : Fin 3), mv g (Pi.single i 1 : Vec) = colVec (c i) := by
    intro i; funext r
    rw [mv_basis, ← hc]; rfl
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hy
    simp only [T0set, Finset.mem_insert, Finset.mem_singleton] at hx
    have : ∀ i : Fin 3, x = Line.mk (Pi.single i 1 : Vec) → g • x ∈ T0set := by
      intro i hxi
      rw [hxi, smul_mk, hcol]
      exact line_colVec_mem _
    obtain ⟨h0, h1, h2⟩ := e_eq_single
    rcases hx with rfl | rfl | rfl
    · exact this 0 (by rw [← h0])
    · exact this 1 (by rw [← h1])
    · exact this 2 (by rw [← h2])
  · rw [card_smul_gl]

/-- An element mapping the standard top cell to itself is a signed permutation matrix. -/
theorem signedPerm_of_smul_T0set (g : GeneralEisenstein.IntegralGL3) (h : g • T0set = T0set) :
    (g : IMat3) ∈ SignedPerms := by
  have hcol : ∀ i : Fin 3, ∃ k : Fin 6, (fun r => (g : IMat3) r i) = colVec k := by
    intro i
    have hmem : g • Line.mk (Pi.single i 1 : Vec) ∈ T0set := by
      rw [← h]
      refine Finset.smul_mem_smul_finset ?_
      obtain ⟨h0, h1, h2⟩ := e_eq_single
      fin_cases i
      · show Line.mk (Pi.single 0 1 : Vec) ∈ T0set
        rw [← h0]; simp [T0set]
      · show Line.mk (Pi.single 1 1 : Vec) ∈ T0set
        rw [← h1]; simp [T0set]
      · show Line.mk (Pi.single 2 1 : Vec) ∈ T0set
        rw [← h2]; simp [T0set]
    rw [smul_mk] at hmem
    simp only [T0set, Finset.mem_insert, Finset.mem_singleton] at hmem
    have key : ∀ (j : Fin 3), Line.mk (mv g (Pi.single i 1 : Vec)) = Line.mk (Pi.single j 1 : Vec) →
        ∃ k : Fin 6, (fun r => (g : IMat3) r i) = colVec k := by
      intro j hj
      rcases Line.mk_eq_mk.mp hj with hj | hj
      · have hj' : mv g (Pi.single i 1 : Vec) = Pi.single j 1 := hj.symm
        fin_cases j
        · exact ⟨0, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
        · exact ⟨2, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
        · exact ⟨4, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
      · have hj' : mv g (Pi.single i 1 : Vec) = -(Pi.single j 1) := neg_eq_iff_eq_neg.mp hj.symm
        fin_cases j
        · exact ⟨1, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
        · exact ⟨3, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
        · exact ⟨5, by funext r; rw [← mv_basis, hj']; fin_cases r <;> simp [colVec]⟩
    obtain ⟨h0, h1, h2⟩ := e_eq_single
    rcases hmem with hm | hm | hm
    · exact key 0 (by rw [hm, ← h0])
    · exact key 1 (by rw [hm, ← h1])
    · exact key 2 (by rw [hm, ← h2])
  choose c hc using hcol
  have hmat : (g : IMat3) = matOfCols c := by
    funext r i
    exact congrFun (hc i) r
  have hdet : (matOfCols c).det = 1 ∨ (matOfCols c).det = -1 := by
    rw [← hmat]
    have : IsUnit (g : IMat3).det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    exact Int.isUnit_iff.mp this
  rw [hmat]
  unfold SignedPerms
  exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdet⟩, rfl⟩

theorem glGraded_T0g_iff_smul (g : GeneralEisenstein.IntegralGL3) : glGraded 3 g T0g = T0g ↔ g • T0set = T0set := by
  constructor
  · intro h
    exact congrArg (fun C : Graded 3 => C.1.val) h
  · intro h
    exact Subtype.ext (Cell.ext h)

/-- The stabilizer of the standard top cell `T₀` in `GL₃(ℤ)`. -/
def stabT0 : Set GeneralEisenstein.IntegralGL3 := {g | glGraded 3 g T0g = T0g}

/-- **The stabilizer of `T₀` in `GL₃(ℤ)` is the group of signed permutation matrices** (`AppendixBResidue.Geometry.SignedPerms`). -/
theorem stabT0_eq : stabT0 = (fun g : GeneralEisenstein.IntegralGL3 => (g : IMat3)) ⁻¹' (SignedPerms : Set IMat3) := by
  ext g
  show glGraded 3 g T0g = T0g ↔ (g : IMat3) ∈ SignedPerms
  rw [glGraded_T0g_iff_smul]
  exact ⟨signedPerm_of_smul_T0set g, smul_T0set_of_signedPerm g⟩

theorem stabT0_finite : stabT0.Finite := by
  rw [stabT0_eq]
  exact (Finset.finite_toSet SignedPerms).preimage (fun a _ b _ h => Units.ext h)

/-- **The stabilizer of the standard top cell in `GL₃(ℤ)` has order 48.** -/
theorem stabT0_ncard : stabT0.ncard = 48 := by
  rw [stabT0_eq, Set.ncard_preimage_of_injective_subset_range (fun a b h => Units.ext h), Set.ncard_coe_finset,
    signedPerms_card]
  intro m hm
  have hm' : m ∈ SignedPerms := hm
  obtain ⟨h1, h2⟩ := signedPerms_transpose m hm'
  have h4 := (signedPerms_transpose mᵀ h1).2
  rw [Matrix.transpose_transpose] at h4
  exact ⟨⟨m, mᵀ, h2, h4⟩, rfl⟩

/-- **The averaged standard top-cell generator, for the full stabilizer.**  The 48 signed permutation matrices, weighted by the orientation
character `cellSign`, average the translates of the generator `[T₀]` of the oriented cell resolution back to `[T₀]`. -/
theorem avgGenT0_stabilizer :
    ∃ S : Finset GeneralEisenstein.IntegralGL3, (∀ g, g ∈ S ↔ glGraded 3 g T0g = T0g) ∧ S.card = 48 ∧
      (48 : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g (single T0g (1 : ℚ)) = single T0g (1 : ℚ) := by
  refine ⟨stabT0_finite.toFinset, fun g => by simp [stabT0], ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ stabT0_finite]; exact stabT0_ncard
  · have hcard : (stabT0_finite.toFinset).card = 48 := by
      rw [← Set.ncard_eq_toFinset_card _ stabT0_finite]; exact stabT0_ncard
    have := avgGenT0_eq stabT0_finite.toFinset (Finset.card_pos.mp (by rw [hcard]; norm_num))
      (fun g hg => by simpa [stabT0] using hg)
    rw [hcard] at this
    exact_mod_cast this

/-- **The paper's orientation sentence with the actual stabilizer**: `paper_orientation_sentence`, where the averaged generator is the
average over the full stabilizer of `T₀` in `GL₃(ℤ)` (the 48 signed permutation matrices). -/
theorem paper_orientation_sentence_stabilizer :
    ((∃ s r : ℚ, (s = 1 ∨ s = -1) ∧ (r = 1 ∨ r = -1) ∧ orientedIntersection s r = 1) ∧
      (∀ s r : ℚ, orientedIntersection s r = 1 ↔ s * r = -1) ∧
      (∀ r : ℚ, orientedIntersection 1 r = 1 ↔ r = -1)) ∧
    stabT0.ncard = 48 ∧
    ∃ S : Finset GeneralEisenstein.IntegralGL3, (∀ g, g ∈ S ↔ glGraded 3 g T0g = T0g) ∧
      (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g (single T0g (1 : ℚ)) = single T0g (1 : ℚ) := by
  obtain ⟨S, hS, hcard, havg⟩ := avgGenT0_stabilizer
  obtain ⟨h1, h2, -, h4, -, -⟩ := paper_orientation_sentence
  refine ⟨⟨h1, h2, h4⟩, stabT0_ncard, S, hS, ?_⟩
  rw [hcard]; exact_mod_cast havg

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
