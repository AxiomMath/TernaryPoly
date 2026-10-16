module

public import TernaryPeriodPolynomials.Building.Ambient.HeightFiltration
public import TernaryPeriodPolynomials.Building.Ambient.ZeroHeightCone
public import TernaryPeriodPolynomials.Building.Good.ChainFilling

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientHeightInduction
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open PrimitiveLineHeight AmbientHeightFiltration
local instance : DecidableEq RationalLine := Classical.decEq _

/-- A displayed finite simplex has a finite height bound, including the empty simplex. -/
theorem simplex_height_bound (F : IntegralVector →ₗ[ℤ] ℤ) (l : List RationalLine)
    (hl : Allowed ambient l) :
    Allowed (bounded F (l.toFinset.sup (height F))) l := by
  apply (allowed_bounded_iff F _ l).mpr
  refine ⟨hl,?_⟩
  intro L hL
  exact Finset.le_sup (f := height F) (List.mem_toFinset.mpr hL)

/-- Every actual finite ambient chain belongs to a finite primitive-height subcomplex. -/
theorem exists_height_bound (F : IntegralVector →ₗ[ℤ] ℤ) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains ambient n) :
    ∃ N : ℕ, c ∈ chains (bounded F N) n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    refine ⟨l.toFinset.sup (height F),?_⟩
    simpa only [hlen] using simplex_mem_chains _ l (simplex_height_bound F l hl)
  | zero => exact ⟨0,(chains (bounded F 0) n).zero_mem⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨M,hM⟩ := ihc
    obtain ⟨N,hN⟩ := ihd
    exact ⟨max M N,(chains (bounded F (max M N)) n).add_mem
      (chains_mono (bounded_mono F (le_max_left M N)) n hM)
      (chains_mono (bounded_mono F (le_max_right M N)) n hN)⟩
  | smul q c hc ih =>
    obtain ⟨N,hN⟩ := ih
    exact ⟨N,(chains (bounded F N) n).smul_mem q hN⟩

/-- The coordinate-plane cone and the primitive height use definitionally equal functionals. -/
theorem integralLastCoordinate_eq :
    AmbientZeroHeightCone.integralLastCoordinate = PrimitiveLineHeight.lastCoordinate := rfl

/-- Height zero for the fixed primitive functional is exactly the actual coordinate-plane condition. -/
theorem last_height_zero_iff (L : RationalLine) :
    height PrimitiveLineHeight.lastCoordinate L = 0 ↔ AmbientZeroHeightCone.PlaneLine L := by
  rw [← integralLastCoordinate_eq]
  exact AmbientZeroHeightCone.height_zero_iff L

/-- The zero-height full subcomplex lies in the actual coordinate-plane subcomplex. -/
theorem bounded_zero_le_zeroPlane :
    bounded PrimitiveLineHeight.lastCoordinate 0 ≤ AmbientZeroHeightCone.zeroPlane := by
  intro s hs
  refine ⟨hs.1,?_⟩
  intro L hL
  exact (last_height_zero_iff L).mp (Nat.eq_zero_of_le_zero (hs.2 L hL))

/-- Every zero-height two-cycle has the actual coordinate-plane cone filling. -/
theorem zero_height_filling {c : Chain RationalLine}
    (hc : c ∈ chains (bounded PrimitiveLineHeight.lastCoordinate 0) 3)
    (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains ambient 4 ∧ boundary t = c :=
  AmbientZeroHeightCone.zero_plane_filling (chains_mono bounded_zero_le_zeroPlane 3 hc) hd

/-- The precise remaining positive-height reduction: a bounded two-cycle is homologous,
through an actual ambient tetrahedral chain, to a cycle at the preceding height. -/
def HeightStep (F : IntegralVector →ₗ[ℤ] ℤ) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ c : Chain RationalLine,
    c ∈ chains (bounded F N) 3 → boundary c = 0 →
      ∃ t r : Chain RationalLine, t ∈ chains ambient 4 ∧
        r ∈ chains (bounded F (N-1)) 3 ∧ c = boundary t + r ∧ boundary r = 0

/-- Natural-number induction turns the positive-height step into actual filling at every finite height. -/
theorem bounded_two_filling (hstep : HeightStep PrimitiveLineHeight.lastCoordinate) (N : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains (bounded PrimitiveLineHeight.lastCoordinate N) 3)
    (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains ambient 4 ∧ boundary t = c := by
  induction N generalizing c with
  | zero => exact zero_height_filling hc hd
  | succ N ih =>
    obtain ⟨t,r,ht,hr,he,hdr⟩ := hstep (N+1) (Nat.zero_lt_succ N) c hc hd
    have hr' : r ∈ chains (bounded PrimitiveLineHeight.lastCoordinate N) 3 := by simpa using hr
    obtain ⟨a,ha,hda⟩ := ih hr' hdr
    refine ⟨t+a,(chains ambient 4).add_mem ht ha,?_⟩
    rw [map_add,hda]
    exact he.symm

/-- Finite exhaustion and the proved zero-height cone close ambient two-filling,
conditional only on the displayed positive-height reduction step. -/
theorem ambient_two_filling (hstep : HeightStep PrimitiveLineHeight.lastCoordinate) :
    GoodChainFilling.AmbientTwoFilling := by
  intro c hc hd
  obtain ⟨N,hN⟩ := exists_height_bound PrimitiveLineHeight.lastCoordinate 3 hc
  exact bounded_two_filling hstep N hN hd

/-- The actual Good-complex filling theorem consumes the resulting ambient filling. -/
theorem good_two_filling (hstep : HeightStep PrimitiveLineHeight.lastCoordinate)
    {c : Chain RationalLine} (hc : c ∈ chains good 3) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c :=
  GoodChainFilling.good_two_filling_of_ambient (ambient_two_filling hstep) hc hd

end TernaryPoly.AmbientHeightInduction
