module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationRanks
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationProjector

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceLineBordification
open SymmetricSpaceBorelCorner

/-- The two literal normalized matrix equations satisfied by every interior chart transition. -/
def Compatible (g : RealGL) (p q : Corner) : Prop :=
  A q=SymmetricSpacePositive.normalize (conjugate g (A p)) ∧
  D q=SymmetricSpacePositive.normalize (conjugate (contragredient g) (D p))

/-- The two independent rank-one tests detect exactly the two root-zero strata. -/
theorem compatible_zero_roots (g : RealGL) {p q : Corner} (h : Compatible g p q) :
    (p.2.1.val=0 ↔ q.2.1.val=0) ∧ (p.2.2.val=0 ↔ q.2.2.val=0) := by
  have hA : (A q).rank=(A p).rank :=
    (congrArg Matrix.rank h.1).trans (rank_normalized_conjugate g (A_psd p) (A_ne_zero p))
  have hD : (D q).rank=(D p).rank :=
    (congrArg Matrix.rank h.2).trans
      (rank_normalized_conjugate (contragredient g) (D_psd p) (D_ne_zero p))
  constructor
  · rw [←A_rank_one_iff p,←A_rank_one_iff q,hA]
  · rw [←D_rank_one_iff p,←D_rank_one_iff q,hD]

theorem compatible_positive_roots (g : RealGL) {p q : Corner} (h : Compatible g p q) :
    (0<p.2.1.val ↔ 0<q.2.1.val) ∧ (0<p.2.2.val ↔ 0<q.2.2.val) := by
  have hz := compatible_zero_roots g h
  constructor
  · constructor
    · intro hp
      have hq : q.2.1.val≠0 := fun hq => (ne_of_gt hp) (hz.1.mpr hq)
      exact lt_of_le_of_ne q.2.1.property (Ne.symm hq)
    · intro hq
      have hp : p.2.1.val≠0 := fun hp => (ne_of_gt hq) (hz.1.mp hp)
      exact lt_of_le_of_ne p.2.1.property (Ne.symm hp)
  · constructor
    · intro hp
      have hq : q.2.2.val≠0 := fun hq => (ne_of_gt hp) (hz.2.mpr hq)
      exact lt_of_le_of_ne q.2.2.property (Ne.symm hq)
    · intro hq
      have hp : p.2.2.val≠0 := fun hp => (ne_of_gt hq) (hz.2.mp hp)
      exact lt_of_le_of_ne p.2.2.property (Ne.symm hp)

/-- A first-root degeneration forces the original real transition matrix to preserve e0. -/
theorem compatible_line_entries (g : RealGL) {p q : Corner} (h : Compatible g p q)
    (hp : p.2.1.val=0) : g.val 1 0=0 ∧ g.val 2 0=0 := by
  have hq := (compatible_zero_roots g h).1.mp hp
  have he := h.1
  rw [A_t1_zero q hq,A_t1_zero p hp] at he
  exact fixed_E00_line g he.symm

/-- A second-root degeneration forces the original real transition matrix to preserve the
actual e0,e1-plane, using the complementary inverse-form detector. -/
theorem compatible_plane_entries (g : RealGL) {p q : Corner} (h : Compatible g p q)
    (hp : p.2.2.val=0) : g.val 2 0=0 ∧ g.val 2 1=0 := by
  have hq := (compatible_zero_roots g h).2.mp hp
  have he := h.2
  rw [D_t2_zero q hq,D_t2_zero p hp] at he
  exact fixed_dual_E22_plane g he.symm

theorem compatible_line_mem (g : RealGL) {p q : Corner} (h : Compatible g p q)
    (hp : p.2.1.val=0) : g∈lineStabilizer :=
  (mem_lineStabilizer_iff g).mpr (compatible_line_entries g h hp)

theorem compatible_plane_mem (g : RealGL) {p q : Corner} (h : Compatible g p q)
    (hp : p.2.2.val=0) : g∈planeStabilizer :=
  (mem_planeStabilizer_iff g).mpr (compatible_plane_entries g h hp)

theorem compatible_borel_mem (g : RealGL) {p q : Corner} (h : Compatible g p q)
    (h1 : p.2.1.val=0) (h2 : p.2.2.val=0) : g∈borelStabilizer :=
  ⟨compatible_plane_mem g h h2,compatible_line_mem g h h1⟩

end TernaryPoly.SymmetricSpaceCornerDegeneration
