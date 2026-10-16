module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportSymmetry
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportGrowth
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryResidueSupport
open ModThreeGoodAction GoodIntegralNormalization ReferenceCoefficientMatrices

/-- A finite signed-symmetric support with genuine order-three norm cancellation is coordinate. -/
theorem finite_support_coordinate (S : Set Normal) (hfinite : S.Finite)
    (hsign : ∀ s L, L∈S → signNormal s L∈S)
    (hperm : ∀ π L, L∈S → permuteNormal π L∈S)
    (hnorm : ∀ L∈S, rowAction a L∈S ∨ rowAction (a^2) L∈S) :
    ∀ L∈S, Coordinate L := by
  classical
  intro L hL
  by_contra hcoord
  let B : Set Normal := {K | K∈S ∧ ¬Coordinate K}
  have hB : B.Finite := hfinite.subset (fun _ h => h.1)
  obtain ⟨K,hK,hmax⟩ := Set.exists_max_image B height hB ⟨L,hL,hcoord⟩
  obtain ⟨s,π,v,hv,he,h0,h1,h2⟩ := positive_representative K hK.2
  have hmem : normalOfRow v hv∈S := by
    rw [he]
    exact hsign s _ (hperm π _ hK.1)
  have hheight : height (normalOfRow v hv)=height K := by
    rw [he,height_signNormal,height_permuteNormal]
  rcases hnorm _ hmem with ha | ha
  · have hbound := hmax _ ⟨ha,row_a_noncoordinate v hv h0 h1⟩
    have hlt := height_lt_row_a v hv h0 h1 h2
    omega
  · have hbound := hmax _ ⟨ha,row_a_sq_noncoordinate v hv h0 h1⟩
    have hlt := height_lt_row_a_sq v hv h0 h1 h2
    omega

/-- The same support statement explicitly lists the three actual coordinate hyperplanes. -/
theorem finite_support_subset_axes (S : Set Normal) (hfinite : S.Finite)
    (hsign : ∀ s L, L∈S → signNormal s L∈S)
    (hperm : ∀ π L, L∈S → permuteNormal π L∈S)
    (hnorm : ∀ L∈S, rowAction a L∈S ∨ rowAction (a^2) L∈S) :
    S ⊆ Set.range axis :=
  fun L hL => by
    obtain ⟨i,hi⟩ := finite_support_coordinate S hfinite hsign hperm hnorm L hL
    exact ⟨i,hi.symm⟩

/-- Genuine fiberwise additive norm cancellation implies support cancellation, with arbitrary fibers. -/
theorem component_norm_support {C : Normal → Type*} [∀ L, AddCommGroup (C L)]
    (c : ∀ L, C L) (hfinite : {L | c L≠0}.Finite)
    (hsign : ∀ s L, c L≠0 → c (signNormal s L)≠0)
    (hperm : ∀ π L, c L≠0 → c (permuteNormal π L)≠0)
    (T : ∀ L, C (rowAction a L) →+ C L)
    (U : ∀ L, C (rowAction (a^2) L) →+ C L)
    (hnorm : ∀ L, c L+T L (c (rowAction a L))+U L (c (rowAction (a^2) L))=0) :
    ∀ L, ¬Coordinate L → c L=0 := by
  classical
  have hs : ∀ L∈{L | c L≠0}, Coordinate L := by
    apply finite_support_coordinate _ hfinite hsign hperm
    intro L hL
    by_contra h
    have ha : c (rowAction a L)=0 := by simpa using (not_or.mp h).1
    have hb : c (rowAction (a^2) L)=0 := by simpa using (not_or.mp h).2
    have he := hnorm L
    simp only [ha,hb,map_zero,add_zero] at he
    exact hL he
  intro L hL
  by_contra h
  exact hL (hs L h)

/-- Actual rational representations and component projections satisfy the residue support lemma.
The transport is the source-component convention: inverse substitution by g at L reads L*g. -/
theorem representation_norm_support
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    {C : Normal → Type*} [∀ L, AddCommGroup (C L)] [∀ L, Module ℚ (C L)]
    (ρ : Representation ℚ ModThreeGoodAction.IntegralGL M) (p : ∀ L, M →ₗ[ℚ] C L) (x : M)
    (hfinite : {L | p L x≠0}.Finite)
    (hsign : ∀ s L, p L x≠0 → p (signNormal s L) x≠0)
    (hperm : ∀ π L, p L x≠0 → p (permuteNormal π L) x≠0)
    (htransport : ∀ g L, p L (ρ g x)=0 ↔ p (rowAction g L) x=0)
    (hnorm : x+ρ a x+ρ (a^2) x=0) :
    ∀ L, ¬Coordinate L → p L x=0 := by
  classical
  have hs : ∀ L∈{L | p L x≠0}, Coordinate L := by
    apply finite_support_coordinate _ hfinite hsign hperm
    intro L hL
    by_contra h
    have ha : p (rowAction a L) x=0 := by simpa using (not_or.mp h).1
    have hb : p (rowAction (a^2) L) x=0 := by simpa using (not_or.mp h).2
    have he := congrArg (p L) hnorm
    simp only [map_add,map_zero,(htransport a L).mpr ha,(htransport (a^2) L).mpr hb,
      add_zero] at he
    exact hL he
  intro L hL
  by_contra h
  exact hL (hs L h)

end TernaryPoly.OrdinaryResidueSupport
