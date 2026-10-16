module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.SpanComparison
public import TernaryPeriodPolynomials.Building.Good.DeterminantDescent
public import TernaryPeriodPolynomials.Topology.Singular.GoodFrame
public import TernaryPeriodPolynomials.Building.Good.ApartmentSpan
public import TernaryPeriodPolynomials.Building.Primitive.LineHeight

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryApartmentGeneration
open ModThreeGoodAction OrdinaryIncidence GoodIncidenceConnected GoodApartmentCycles
open PrimitiveLineHeight

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- The same comparison with the generic apartment cycle aliases explicit. -/
def genericComparison : OrdinaryRelativeChains.RelativeBoundaryTwo →ₗ[ℚ] GoodApartmentCycles.Cycles (fun _ => True) :=
  OrdinaryApartmentSpanComparison.comparison

def NonzeroColumns (M : Mat) : Prop := ∀ j,rationalVector (M.col j)≠0

def vectorLine (v : IntegralVector) (hv : rationalVector v≠0) : OrdinaryIncidence.Line :=
  ⟨Submodule.span ℚ {rationalVector v},finrank_span_singleton hv,trivial⟩

def columnLine (M : Mat) (hM : NonzeroColumns M) (j : Fin 3) : OrdinaryIncidence.Line :=
  vectorLine (M.col j) (hM j)

def frameApartment (M : Mat) (hM : NonzeroColumns M) : GoodApartmentCycles.Cycles (fun _ => True) :=
  apartmentCycle (fun _ => True) (columnLine M hM 0) (columnLine M hM 1) (columnLine M hM 2)

theorem columnLine_le_columnSpan (M : Mat) (hM : NonzeroColumns M) (j : Fin 3) :
    (columnLine M hM j).val≤SingularGoodFrame.columnSpan M := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl
  exact Submodule.subset_span ⟨j,rfl⟩

/-- Singular integral frames give zero ordinary apartments, without residue restrictions. -/
theorem frameApartment_eq_zero_of_det_eq_zero (M : Mat) (hM : NonzeroColumns M) (hd : M.det=0) :
    frameApartment M hM=0 := by
  classical
  by_cases he : columnLine M hM 0=columnLine M hM 1
  · apply Subtype.ext
    change apartmentChain (fun _ => True) (columnLine M hM 0) (columnLine M hM 1) (columnLine M hM 2)=0
    rw [he,apartmentChain,lineChain_self,lineChain_reverse (fun _ => True) (columnLine M hM 1) (columnLine M hM 2)]
    simp
  · let P : OrdinaryIncidence.Plane := spanPlane (fun _ => True) (columnLine M hM 0) (columnLine M hM 1) he
    have hPS : P.val≤SingularGoodFrame.columnSpan M :=
      sup_le (columnLine_le_columnSpan M hM 0) (columnLine_le_columnSpan M hM 1)
    have hPeq : P.val=SingularGoodFrame.columnSpan M := by
      apply Submodule.eq_of_le_of_finrank_le hPS
      rw [P.property.1]
      exact SingularGoodFrame.columnSpan_finrank_le_two M hd
    exact apartmentCycle_collinear (fun _ => True) _ _ _ P
      (line_le_spanPlane_left (fun _ => True) _ _ he) (line_le_spanPlane_right (fun _ => True) _ _ he)
      (by rw [hPeq]; exact columnLine_le_columnSpan M hM 2)

theorem col_updateCol_self (M : Mat) (w : IntegralVector) (j : Fin 3) :
    (M.updateCol j w).col j=w := by
  funext i
  change (M.updateCol j w) i j=w i
  exact Matrix.updateCol_self

theorem col_updateCol_ne (M : Mat) (w : IntegralVector) (j k : Fin 3) (hjk : k≠j) :
    (M.updateCol j w).col k=M.col k := by
  funext i
  change (M.updateCol j w) i k=M i k
  exact Matrix.updateCol_ne hjk

theorem nonzeroColumns_updateCol (M : Mat) (hM : NonzeroColumns M)
    (w : IntegralVector) (hw : rationalVector w≠0) (j : Fin 3) : NonzeroColumns (M.updateCol j w) := by
  intro k
  by_cases hk : k=j
  · subst k
    simpa only [col_updateCol_self] using hw
  · simpa only [col_updateCol_ne M w j k hk] using hM k

theorem columnLine_updateCol_same (M : Mat) (w : IntegralVector) (hw : rationalVector w≠0)
    (j : Fin 3) (hU : NonzeroColumns (M.updateCol j w)) :
    columnLine (M.updateCol j w) hU j=vectorLine w hw := by
  apply Subtype.ext
  simp only [columnLine,vectorLine,col_updateCol_self]

theorem columnLine_updateCol_ne (M : Mat) (hM : NonzeroColumns M)
    (w : IntegralVector) (j k : Fin 3) (hjk : k≠j) (hU : NonzeroColumns (M.updateCol j w)) :
    columnLine (M.updateCol j w) hU k=columnLine M hM k := by
  apply Subtype.ext
  simp only [columnLine,vectorLine,col_updateCol_ne M w j k hjk]

theorem apartmentCycle_subdivision (L M N W : OrdinaryIncidence.Line) :
    apartmentCycle (fun _ => True) L M N=apartmentCycle (fun _ => True) W M N+
      apartmentCycle (fun _ => True) L W N+apartmentCycle (fun _ => True) L M W := by
  have h := sub_eq_zero.mp (apartmentCycle_four (fun _ => True) L M N W)
  have hs : apartmentCycle (fun _ => True) L W N= -apartmentCycle (fun _ => True) L N W :=
    (apartmentCycle_cyclic (fun _ => True) N L W).trans (apartmentCycle_swap (fun _ => True) L N W)
  rw [hs,←apartmentCycle_cyclic (fun _ => True) W M N]
  simpa only [sub_eq_add_neg] using h.symm

theorem frameApartment_subdivision (M : Mat) (hM : NonzeroColumns M)
    (w : IntegralVector) (hw : rationalVector w≠0) (hU : ∀ j,NonzeroColumns (M.updateCol j w)) :
    frameApartment M hM=frameApartment (M.updateCol 0 w) (hU 0)+
      frameApartment (M.updateCol 1 w) (hU 1)+frameApartment (M.updateCol 2 w) (hU 2) := by
  simp only [frameApartment,columnLine_updateCol_same M w hw]
  rw [columnLine_updateCol_ne M hM w 0 1 (by decide),columnLine_updateCol_ne M hM w 0 2 (by decide),
    columnLine_updateCol_ne M hM w 1 0 (by decide),columnLine_updateCol_ne M hM w 1 2 (by decide),
    columnLine_updateCol_ne M hM w 2 0 (by decide),columnLine_updateCol_ne M hM w 2 1 (by decide)]
  exact apartmentCycle_subdivision _ _ _ _

/-- An unrestricted nonzero integral replacement strictly lowers all three determinants. -/
theorem exists_determinant_descent (M : Mat) (hd : M.det≠0) (hlarge : 1<M.det.natAbs) :
    ∃ w : IntegralVector,rationalVector w≠0 ∧ ∀ j,(M.updateCol j w).det.natAbs<M.det.natAbs := by
  obtain ⟨w,a,hw,ha,k,hk⟩ := NonunimodularFractionalPoint.fractional_lattice_point M hd hlarge
  have hw0 : rationalVector w≠0 := by
    intro hz
    have hinj := Matrix.mulVec_injective_iff.mpr (SingularGoodFrame.column_independent_iff_det_ne_zero M |>.mpr hd)
    have ha0 : a=0 := hinj (hw.symm.trans (hz.trans (Matrix.mulVec_zero _).symm))
    simp [ha0] at hk
  exact ⟨w,hw0,GoodDeterminantDescent.det_updateCol_natAbs_lt M hd w a hw
    (fun i => by rw [abs_of_nonneg (ha i).1]; exact (ha i).2)⟩

/-- An actual integral invertible frame represents its displayed ambient triangle. -/
theorem comparison_triangle (g : IntegralGL) :
    genericComparison (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g))=
      apartmentCycle (fun _ => True)
        (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine g 0))
        (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine g 1))
        (OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine g 2)) := by
  apply Subtype.ext
  exact OrdinaryApartmentSpanComparison.edgeMap_triangle_boundary _ _ _

theorem columnLine_unit (g : IntegralGL) (hM : NonzeroColumns g.val) (j : Fin 3) :
    columnLine g.val hM j=OrdinaryApartmentSpanComparison.line (AugmentedFrameComplex.augmentedLine g j.castSucc) := by
  apply Subtype.ext
  exact (IntegralFrameHeightReduction.columnLine_span g j).symm

/-- Every determinant-one-in-absolute-value integral apartment lies in the actual comparison range. -/
theorem frameApartment_mem_range_of_unit (M : Mat) (hM : NonzeroColumns M) (hu : M.det.natAbs=1) :
    frameApartment M hM∈genericComparison.range := by
  let g : IntegralGL := Matrix.nonsingInvUnit M (Int.isUnit_iff_natAbs_eq.mpr hu)
  have hg : NonzeroColumns g.val := hM
  refine ⟨OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g),?_⟩
  rw [comparison_triangle]
  change apartmentCycle (fun _ => True) _ _ _=frameApartment g.val hg
  change apartmentCycle (fun _ => True) _ _ _=apartmentCycle (fun _ => True)
    (columnLine g.val hg 0) (columnLine g.val hg 1) (columnLine g.val hg 2)
  rw [columnLine_unit g hg 0,columnLine_unit g hg 1,columnLine_unit g hg 2]
  rfl

/-- Strict integral determinant descent generates every nonzero-column ordinary apartment. -/
theorem frameApartment_mem_range (M : Mat) (hM : NonzeroColumns M) :
    frameApartment M hM∈genericComparison.range := by
  generalize hn : M.det.natAbs=n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : M.det=0
    · rw [frameApartment_eq_zero_of_det_eq_zero M hM hz]
      exact genericComparison.range.zero_mem
    by_cases h1 : M.det.natAbs=1
    · exact frameApartment_mem_range_of_unit M hM h1
    have h0 : M.det.natAbs≠0 := Int.natAbs_ne_zero.mpr hz
    have hl : 1<M.det.natAbs := by omega
    obtain ⟨w,hw,hu⟩ := exists_determinant_descent M hz hl
    rw [frameApartment_subdivision M hM w hw (nonzeroColumns_updateCol M hM w hw)]
    apply genericComparison.range.add_mem
    · apply genericComparison.range.add_mem
      · exact ih _ (by simpa only [←hn] using hu 0) _ (nonzeroColumns_updateCol M hM w hw 0) rfl
      · exact ih _ (by simpa only [←hn] using hu 1) _ (nonzeroColumns_updateCol M hM w hw 1) rfl
    · exact ih _ (by simpa only [←hn] using hu 2) _ (nonzeroColumns_updateCol M hM w hw 2) rfl

def lineGenerator (L : OrdinaryIncidence.Line) : IntegralVector := primitiveGenerator ⟨L.val,L.property.1⟩

def lineFrame (L : Fin 3 → OrdinaryIncidence.Line) : Mat := fun i j => lineGenerator (L j) i

theorem lineFrame_nonzero (L : Fin 3 → OrdinaryIncidence.Line) : NonzeroColumns (lineFrame L) :=
  fun j => primitiveGenerator_ne_zero ⟨(L j).val,(L j).property.1⟩

theorem columnLine_lineFrame (L : Fin 3 → OrdinaryIncidence.Line) (j : Fin 3) :
    columnLine (lineFrame L) (lineFrame_nonzero L) j=L j := by
  apply Subtype.ext
  exact primitiveGenerator_span ⟨(L j).val,(L j).property.1⟩

/-- All rational ordinary apartments lie in the actual ambient comparison range. -/
theorem apartment_mem_range (L M N : OrdinaryIncidence.Line) :
    apartmentCycle (fun _ => True) L M N∈genericComparison.range := by
  have h := frameApartment_mem_range (lineFrame ![L,M,N]) (lineFrame_nonzero ![L,M,N])
  simpa only [frameApartment,columnLine_lineFrame,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

/-- Unrestricted integral determinant descent and actual graph cycle generation make comparison surjective. -/
theorem comparison_surjective : Function.Surjective OrdinaryApartmentSpanComparison.comparison := by
  have h : apartmentSpan (fun _ => True)≤genericComparison.range := by
    apply Submodule.span_le.mpr
    rintro c ⟨t,rfl⟩
    exact apartment_mem_range t.1 t.2.1 t.2.2
  rw [apartmentSpan_eq_top (fun _ => True) ⟨firstLine,firstLine_finrank,trivial⟩] at h
  intro c
  exact h Submodule.mem_top

end TernaryPoly.OrdinaryApartmentGeneration
