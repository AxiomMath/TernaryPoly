module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Stabilizers
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitCosets
open ModThreeGoodAction RelativePermutationIndices RelativeOrbitTransport RelativeOrbitStabilizers

section General
variable {G X : Type*} [Group G] [MulAction G X]

/-- An exhaustive orbit is literally the whole acted-on type. -/
def fullOrbitEquiv (b : X) (hb : ∀ x, ∃ g : G, g • b = x) : MulAction.orbit G b ≃ X where
  toFun := Subtype.val
  invFun x := ⟨x,MulAction.mem_orbit_iff.mpr (hb x)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A proved exhaustive orbit with a proved stabilizer gives the actual coset equivalence. -/
def cosetEquiv (b : X) (hb : ∀ x, ∃ g : G, g • b = x) (H : Subgroup G)
    (hH : MulAction.stabilizer G b = H) : G ⧸ H ≃ X := by
  subst H
  exact (MulAction.orbitEquivQuotientStabilizer G b).symm.trans (fullOrbitEquiv b hb)

@[simp] theorem cosetEquiv_mk (b : X) (hb : ∀ x, ∃ g : G, g • b = x) (H : Subgroup G)
    (hH : MulAction.stabilizer G b = H) (g : G) :
    cosetEquiv b hb H hH (QuotientGroup.mk g) = g • b := by
  subst H
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply G b g

/-- Coset coordinates intertwine genuine left multiplication with the original action. -/
theorem cosetEquiv_equivariant (b : X) (hb : ∀ x, ∃ g : G, g • b = x) (H : Subgroup G)
    (hH : MulAction.stabilizer G b = H) (g : G) (x : G ⧸ H) :
    cosetEquiv b hb H hH (g • x) = g • cosetEquiv b hb H hH x := by
  refine Quotient.inductionOn' x (fun h => ?_)
  change cosetEquiv b hb H hH (QuotientGroup.mk (g*h)) = g • cosetEquiv b hb H hH (QuotientGroup.mk h)
  rw [cosetEquiv_mk,cosetEquiv_mk,mul_smul]

end General

/-- The four quotient sets use the exact conjugated parameterized stabilizer subgroups. -/
def lineCosets : K ⧸ HL ≃ BadLine := cosetEquiv baseLine badLine_transitive HL stabilizer_line
def planeCosets : K ⧸ HP ≃ BadPlane := cosetEquiv basePlane badPlane_transitive HP stabilizer_plane
def bbCosets : K ⧸ HBB ≃ BB := cosetEquiv baseBB bb_transitive HBB stabilizer_bb
def bgCosets : K ⧸ HBG ≃ BG := cosetEquiv baseBG bg_transitive HBG stabilizer_bg

@[simp] theorem lineCosets_mk (g : K) : lineCosets (QuotientGroup.mk g) = badLineAction g baseLine :=
  cosetEquiv_mk _ _ _ _ g
@[simp] theorem planeCosets_mk (g : K) : planeCosets (QuotientGroup.mk g) = badPlaneAction g basePlane :=
  cosetEquiv_mk _ _ _ _ g
@[simp] theorem bbCosets_mk (g : K) : bbCosets (QuotientGroup.mk g) = bbAction g baseBB :=
  cosetEquiv_mk _ _ _ _ g
@[simp] theorem bgCosets_mk (g : K) : bgCosets (QuotientGroup.mk g) = bgAction g baseBG :=
  cosetEquiv_mk _ _ _ _ g

theorem lineCosets_equivariant (g : K) (x : K ⧸ HL) : lineCosets (g • x) = badLineAction g (lineCosets x) :=
  cosetEquiv_equivariant _ _ _ _ g x
theorem planeCosets_equivariant (g : K) (x : K ⧸ HP) : planeCosets (g • x) = badPlaneAction g (planeCosets x) :=
  cosetEquiv_equivariant _ _ _ _ g x
theorem bbCosets_equivariant (g : K) (x : K ⧸ HBB) : bbCosets (g • x) = bbAction g (bbCosets x) :=
  cosetEquiv_equivariant _ _ _ _ g x
theorem bgCosets_equivariant (g : K) (x : K ⧸ HBG) : bgCosets (g • x) = bgAction g (bgCosets x) :=
  cosetEquiv_equivariant _ _ _ _ g x

/-- Actual finite coset-chain identifications, ready to serve as the permutation-module input. -/
def lineChains : ((K ⧸ HL) →₀ ℚ) ≃ₗ[ℚ] (BadLine →₀ ℚ) := Finsupp.domLCongr lineCosets
def planeChains : ((K ⧸ HP) →₀ ℚ) ≃ₗ[ℚ] (BadPlane →₀ ℚ) := Finsupp.domLCongr planeCosets
def bbChains : ((K ⧸ HBB) →₀ ℚ) ≃ₗ[ℚ] (BB →₀ ℚ) := Finsupp.domLCongr bbCosets
def bgChains : ((K ⧸ HBG) →₀ ℚ) ≃ₗ[ℚ] (BG →₀ ℚ) := Finsupp.domLCongr bgCosets

@[simp] theorem lineChains_single (g : K) (q : ℚ) :
    lineChains (Finsupp.single (QuotientGroup.mk g) q) = Finsupp.single (badLineAction g baseLine) q := by
  change Finsupp.domLCongr lineCosets _ = _
  rw [Finsupp.domLCongr_single,lineCosets_mk]
@[simp] theorem planeChains_single (g : K) (q : ℚ) :
    planeChains (Finsupp.single (QuotientGroup.mk g) q) = Finsupp.single (badPlaneAction g basePlane) q := by
  change Finsupp.domLCongr planeCosets _ = _
  rw [Finsupp.domLCongr_single,planeCosets_mk]
@[simp] theorem bbChains_single (g : K) (q : ℚ) :
    bbChains (Finsupp.single (QuotientGroup.mk g) q) = Finsupp.single (bbAction g baseBB) q := by
  change Finsupp.domLCongr bbCosets _ = _
  rw [Finsupp.domLCongr_single,bbCosets_mk]
@[simp] theorem bgChains_single (g : K) (q : ℚ) :
    bgChains (Finsupp.single (QuotientGroup.mk g) q) = Finsupp.single (bgAction g baseBG) q := by
  change Finsupp.domLCongr bgCosets _ = _
  rw [Finsupp.domLCongr_single,bgCosets_mk]

/-- Left translation on the actual finite coset-chain module. -/
def cosetLinear (H : Subgroup K) (g : K) : ((K ⧸ H) →₀ ℚ) ≃ₗ[ℚ] ((K ⧸ H) →₀ ℚ) :=
  Finsupp.domLCongr (MulAction.toPerm g)

theorem lineChains_equivariant (g : K) (c : (K ⧸ HL) →₀ ℚ) :
    lineChains (cosetLinear HL g c) = Finsupp.domLCongr (R := ℚ) (badLineAction g) (lineChains c) :=
  RelativePermutationQuotient.reindex_natural lineCosets (MulAction.toPerm g) (badLineAction g)
    (lineCosets_equivariant g) c
theorem planeChains_equivariant (g : K) (c : (K ⧸ HP) →₀ ℚ) :
    planeChains (cosetLinear HP g c) = Finsupp.domLCongr (R := ℚ) (badPlaneAction g) (planeChains c) :=
  RelativePermutationQuotient.reindex_natural planeCosets (MulAction.toPerm g) (badPlaneAction g)
    (planeCosets_equivariant g) c
theorem bbChains_equivariant (g : K) (c : (K ⧸ HBB) →₀ ℚ) :
    bbChains (cosetLinear HBB g c) = Finsupp.domLCongr (R := ℚ) (bbAction g) (bbChains c) :=
  RelativePermutationQuotient.reindex_natural bbCosets (MulAction.toPerm g) (bbAction g)
    (bbCosets_equivariant g) c
theorem bgChains_equivariant (g : K) (c : (K ⧸ HBG) →₀ ℚ) :
    bgChains (cosetLinear HBG g c) = Finsupp.domLCongr (R := ℚ) (bgAction g) (bgChains c) :=
  RelativePermutationQuotient.reindex_natural bgCosets (MulAction.toPerm g) (bgAction g)
    (bgCosets_equivariant g) c

/-- No orientation character occurs: each group element sends line-to-plane flags to line-to-plane flags with the same coefficient. -/
theorem bb_no_orientation_character (g : K) (e : BB) (q : ℚ) :
    Finsupp.domLCongr (R := ℚ) (bbAction g) (Finsupp.single e q) = Finsupp.single (bbAction g e) q :=
  Finsupp.domLCongr_single _ _ _
theorem bg_no_orientation_character (g : K) (e : BG) (q : ℚ) :
    Finsupp.domLCongr (R := ℚ) (bgAction g) (Finsupp.single e q) = Finsupp.single (bgAction g e) q :=
  Finsupp.domLCongr_single _ _ _

end TernaryPoly.RelativeOrbitCosets
