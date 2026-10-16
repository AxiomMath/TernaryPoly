module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.DimensionCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitReconstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerTransport

@[expose] public section


/-!
# Separation reduces to four local problems, one per cusp

Each side of the boundary has exactly two cusps (good and bad flags, `CuspOrbits`). The Shapiro
coordinates `cuspRes side good` at the two reference flags jointly detect every maximal-stratum
class, and every away-from-three Hecke operator acts on them DIAGONALLY by the local Hecke operators
`localOp` of the parabolic stabilizers (`HeckeShapiro.fixedPointH2_hecke`). Hence the joint
generalized eigenspace `J` of the pair character maps into the four local joint generalized
eigenspaces `localJoint`, and eigencharacter separation follows from four local statements:
every local generalized eigenclass at a cusp is the Shapiro coordinate of a class of the cuspidal
summand that vanishes at the other cusp of the same side.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SpectralSeparation

namespace TernaryPeriodPolynomials.Spectral.CuspReduction

open CuspOrbits

variable {n : ℕ}

/-- The stabilizer of the reference flag of a cusp. -/
abbrev cuspLevel (side : Side) (good : Bool) : Subgroup RationalGL3 :=
  fixedPointLevel rationalLevel (cuspFlag side good)

/-- The local cohomology `H²(Γ_F, V)` at a cusp. -/
abbrev CuspH2 (n : ℕ) (χ : RankOneCharacter) (side : Side) (good : Bool) :=
  H2 (cuspLevel side good) (rationalCoefficientComponent n χ)

/-- The Shapiro coordinate of a maximal-stratum class at a cusp. -/
def cuspRes (n : ℕ) (χ : RankOneCharacter) (side : Side) (good : Bool) :
    StratumH2 n χ side →ₗ[ℂ] CuspH2 n χ side good :=
  fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) (cuspFlag side good)

/-- The local Hecke operator of an away-from-three correspondence at a cusp. -/
def localOp (n : ℕ) (χ : RankOneCharacter) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (good : Bool) : Module.End ℂ (CuspH2 n χ side good) :=
  LocalHecke.cohomologyAction (rationalCoefficientComponent n χ)
    (HeckeShapiro.localCorrespondence (transports_cuspFlag t ht side good))

/-- **Diagonality.** Shapiro coordinates intertwine every actual away-from-three Hecke operator with
the local Hecke operator, on every class. -/
theorem cuspRes_hecke {χ : RankOneCharacter} (hecke : BoundaryHecke n χ)
    (hhecke : ActualBoundaryHecke n χ hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (good : Bool) (a : StratumH2 n χ side) :
    cuspRes n χ side good (hecke side t a) = localOp n χ t ht side good (cuspRes n χ side good a) :=
  HeckeShapiro.fixedPointH2_hecke (rationalCoefficientComponent n χ) (hecke side) (hhecke side)
    (transports_cuspFlag t ht side good) a

section Generic

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem intertwine_sub_pow (f : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (hcomm : ∀ a, f (A a) = B (f a)) (μ : ℂ) (k : ℕ) (a : M) :
    f (((A - μ • 1) ^ k) a) = ((B - μ • 1) ^ k) (f a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, hcomm]

theorem intertwine_mem_maxGenEigenspace (f : M →ₗ[ℂ] N) (A : Module.End ℂ M)
    (B : Module.End ℂ N) (hcomm : ∀ a, f (A a) = B (f a)) (μ : ℂ) {a : M}
    (ha : a ∈ A.maxGenEigenspace μ) : f a ∈ B.maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at ha ⊢
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, by rw [← intertwine_sub_pow f A B hcomm, hk, map_zero]⟩

theorem prodMap_mem_maxGenEigenspace (A : Module.End ℂ M) (B : Module.End ℂ N) (μ : ℂ)
    {v : M × N} (hv : v ∈ Module.End.maxGenEigenspace (A.prodMap B) μ) :
    v.1 ∈ A.maxGenEigenspace μ ∧ v.2 ∈ B.maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  rw [prodMap_sub_smul_pow_apply] at hk
  exact ⟨(Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, (Prod.mk.inj hk).1⟩,
    (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, (Prod.mk.inj hk).2⟩⟩

theorem map_sub_sub_eq_zero (f : M →ₗ[ℂ] N) {x a b : M} (ha : f a = f x) (hb : f b = 0) :
    f (x - a - b) = 0 := by
  rw [map_sub, map_sub, ha, hb, sub_self, sub_zero]

theorem map_sub_sub_eq_zero' (f : M →ₗ[ℂ] N) {x a b : M} (ha : f a = 0) (hb : f b = f x) :
    f (x - a - b) = 0 := by
  rw [map_sub, map_sub, ha, hb, sub_zero, sub_self]

end Generic

theorem cuspRes_hecke_sub_pow' {χ : RankOneCharacter} (hecke : BoundaryHecke n χ)
    (hhecke : ActualBoundaryHecke n χ hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (good : Bool) (μ : ℂ) (k : ℕ) (a : StratumH2 n χ side) :
    cuspRes n χ side good (((hecke side t - μ • 1) ^ k) a) =
      ((localOp n χ t ht side good - μ • 1) ^ k) (cuspRes n χ side good a) :=
  intertwine_sub_pow _ _ _ (cuspRes_hecke hecke hhecke t ht side good) μ k a

/-- The joint generalized eigenspace of the local operators at a cusp. -/
def localJoint (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) : Submodule ℂ (CuspH2 n χ side good) :=
  ⨅ t : {t : HeckeCorrespondence // AwayThree t},
    (localOp n χ t.1 t.2 side good).maxGenEigenspace (c t.1)

/-- The side component of a boundary vector. -/
def component {χ : RankOneCharacter} : (side : Side) → BoundaryCoordinates n χ → StratumH2 n χ side
  | .plane, b => b.1
  | .line, b => b.2

theorem cuspRes_mem_localJoint (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (c : HeckeCorrespondence → ℂ)
    {w : BoundaryCoordinates n D.chi} (hw : w ∈ jointGenEigenspace D hecke c)
    (side : Side) (good : Bool) :
    cuspRes n D.chi side good (component side w) ∈ localJoint n D.chi c side good := by
  simp only [localJoint, Submodule.mem_iInf, Subtype.forall]
  intro t ht
  simp only [jointGenEigenspace, Submodule.mem_iInf, Subtype.forall] at hw
  have hpair := prodMap_mem_maxGenEigenspace (hecke .plane t) (hecke .line t) (c t) (hw t ht)
  apply intertwine_mem_maxGenEigenspace (cuspRes n D.chi side good) (hecke side t)
    (localOp n D.chi t ht side good) (cuspRes_hecke hecke hhecke t ht side good)
  cases side
  · exact hpair.1
  · exact hpair.2

/-- **Shapiro detection at the two cusps.** A maximal-stratum class vanishes iff both its Shapiro
coordinates at the two reference cusps of its side vanish. -/
theorem eq_zero_iff_cuspRes {χ : RankOneCharacter} (side : Side) (a : StratumH2 n χ side) :
    a = 0 ↔ cuspRes n χ side true a = 0 ∧ cuspRes n χ side false a = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨hgood, hbad⟩
    apply (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) a).mpr
    intro flag
    classical
    obtain ⟨γ, hγ⟩ := cuspFlag_transporter side (decide (GoodFlag side flag)) flag
      (by simp)
    have htransport := stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent n χ) γ (cuspFlag side (decide (GoodFlag side flag))) flag hγ a
    rw [← htransport]
    have hzero : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
        (cuspFlag side (decide (GoodFlag side flag))) a = 0 := by
      cases decide (GoodFlag side flag)
      · exact hbad
      · exact hgood
    rw [hzero, map_zero]

theorem associatePair_mem_iff (D : InducingData n) (b : BoundaryCoordinates n D.chi) :
    b ∈ associatePair D ↔ ∀ side, component side b ∈ boundarySummand D side := by
  constructor
  · rintro ⟨h1, h2⟩ side
    cases side
    · exact h1
    · exact h2
  · intro h
    exact ⟨h .plane, h .line⟩

/-- **Four-cusp reduction of eigencharacter separation.** It suffices that at each of the four
cusps every local joint generalized eigenclass of the pair character is the Shapiro coordinate of a
class of the cuspidal summand of that side vanishing at the other cusp of the side. -/
theorem eigenSeparated_of_cusps (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (cusps : ∀ side good, ∀ y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good,
      ∃ a ∈ boundarySummand D side,
        cuspRes n D.chi side good a = y ∧ cuspRes n D.chi side (!good) a = 0) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  apply eigenSeparated_of_finrank_le D hecke hhecke
  apply Submodule.finrank_mono
  intro w hw
  apply (associatePair_mem_iff D w).mpr
  intro side
  obtain ⟨aGood, haGood, hresGood, hresGood'⟩ := cusps side true _
    (cuspRes_mem_localJoint D hecke hhecke _ hw side true)
  obtain ⟨aBad, haBad, hresBad, hresBad'⟩ := cusps side false _
    (cuspRes_mem_localJoint D hecke hhecke _ hw side false)
  have hdiff : component side w - aGood - aBad = 0 := by
    have hG' : cuspRes n D.chi side false aGood = 0 := hresGood'
    have hB' : cuspRes n D.chi side true aBad = 0 := hresBad'
    exact (eq_zero_iff_cuspRes side _).mpr
      ⟨map_sub_sub_eq_zero _ hresGood hB', map_sub_sub_eq_zero' _ hG' hresBad⟩
  have hw' : component side w = aGood + aBad := by
    rw [← sub_eq_zero, ← sub_sub]
    exact hdiff
  rw [hw']
  exact Submodule.add_mem _ haGood haBad

end TernaryPeriodPolynomials.Spectral.CuspReduction
