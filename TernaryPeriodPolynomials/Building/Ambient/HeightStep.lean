module

public import TernaryPeriodPolynomials.Building.OrientedChain.IsolatedVertexSurgery
public import TernaryPeriodPolynomials.Building.Ambient.HorizontalReduction
public import TernaryPeriodPolynomials.Building.OrientedChain.ProjectionCalculus

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHeightStep
open ModThreeGoodAction AugmentedFrameComplex GoodIntegralNormalization PrimitiveLineHeight
open OrientedListChains OrientedChainProjection GoodLinkExtraction AmbientHeightFiltration
open OrientedIsolatedVertexSurgery AmbientEdgeRetraction
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The remaining height-local input, with the literal unrestricted-link remainder convention. -/
def LowLinkFilling (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) : Prop :=
  ∀ a : RationalLine, height F a = N → ∀ u : Chain RationalLine,
    u ∈ chains (lowLink F (nonnegativeRepresentative F a) a) 2 → boundary u = 0 →
      ∃ b : Chain RationalLine,
        b ∈ chains (lowLink F (nonnegativeRepresentative F a) a) 3 ∧ boundary b = u

/-- The exact link extracted from a bounded high vertex is precisely the actual lower link. -/
theorem high_link_eq (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (a : RationalLine)
    (ha : height F a = N) :
    goodLink (bounded F N) (fun L => height F L < N) {a} =
      lowLink F (nonnegativeRepresentative F a) a := by
  ext s
  change s ∈ goodLink (bounded F N) (fun L => height F L < N) {a} ↔
    s ∈ goodLink ambient
    (fun L => L ≠ a ∧ (height F L : ℤ) < F (nonnegativeRepresentative F a)) {a}
  rw [mem_goodLink,mem_goodLink,nonnegativeRepresentative_value,ha]
  constructor
  · rintro ⟨hs,hface,hlt⟩
    refine ⟨hs,hface.1,?_⟩
    intro L hL
    refine ⟨?_,by exact_mod_cast hlt L hL⟩
    intro he
    have hh := hlt L hL
    rw [he,ha] at hh
    exact (lt_irrefl N) hh
  · rintro ⟨hs,hface,hlt⟩
    refine ⟨hs,⟨hface,?_⟩,?_⟩
    · intro L hL
      rcases Finset.mem_union.mp hL with hL | hL
      · have he : L = a := Finset.mem_singleton.mp hL
        rw [he,ha]
      · have hh : height F L < N := by exact_mod_cast (hlt L hL).2
        exact Nat.le_of_lt hh
    · intro L hL
      exact_mod_cast (hlt L hL).2

/-- Restricting a bounded complex to strictly lower vertices is the preceding height stage. -/
theorem restriction_eq (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N) :
    restricted (bounded F N) (fun L => height F L < N) = bounded F (N-1) := by
  ext s
  change s ∈ goodLink (bounded F N) (fun L => height F L < N) ∅ ↔ _
  rw [mem_goodLink,Finset.empty_union]
  constructor
  · rintro ⟨_,hface,hlt⟩
    refine ⟨hface.1,?_⟩
    intro L hL
    have hh := hlt L hL
    omega
  · intro hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,⟨hs.1,?_⟩,?_⟩
    · intro L hL
      exact (hs.2 L hL).trans (Nat.sub_le N 1)
    · intro L hL
      have hh := hs.2 L hL
      omega

/-- Actual lower-link filling discharges the generic isolated-vertex input. -/
theorem isolated_input (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (hfill : LowLinkFilling F N) :
    LinkFilling (bounded F N) (fun L => height F L < N) := by
  intro a ha hbad u hu hdu
  have hle : height F a ≤ N := ha.2 a (Finset.mem_singleton_self a)
  have he : height F a = N := by omega
  rw [high_link_eq F N a he] at hu ⊢
  exact hfill a he u hu hdu

/-- One complete finite height step, conditional only on actual lower-link one-cycle filling. -/
theorem lower_height (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    (hfill : LowLinkFilling F N) {c : Chain RationalLine}
    (hc : c ∈ chains (bounded F N) 3) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ chains (bounded F (N-1)) 3 ∧ c = boundary t + r ∧ boundary r = 0 := by
  obtain ⟨t,d,ht,hdmem,hdzero,he,hproj⟩ :=
    AmbientHorizontalReduction.reduce_to_one_high F N hN hc hd
  have hmax : ∀ s : Finset RationalLine, 1 < s.card →
      badFaceProjection (fun L => height F L < N) s d = 0 := by
    intro s hs
    exact OrientedProjectionCalculus.badFace_eq_zero_of_badCount_eq_zero
      (fun L => height F L < N) s s.card rfl d (hproj s.card (by omega))
  obtain ⟨t',r,ht',hr,he',hdr⟩ := eliminate_isolated_vertices (bounded F N)
    (fun L => height F L < N) (isolated_input F N hfill)
    (reducedTriangles_le_chains F N hdmem) hdzero hmax
  rw [restriction_eq F N hN] at hr
  refine ⟨t+t',r,(chains (bounded F N) 4).add_mem ht ht',hr,?_,hdr⟩
  rw [he,he',map_add]
  abel

end TernaryPoly.AmbientHeightStep
