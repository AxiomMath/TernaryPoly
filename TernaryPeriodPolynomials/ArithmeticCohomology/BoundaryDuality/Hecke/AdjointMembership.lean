module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineBound

@[expose] public section


/-!
# Summand coordinates lie in the domain of the edge maps

The edge maps of the local cohomology `H²(Γ_F, V)` at the good line and at the bad line are defined
on subspaces: at the good line on the classes `ML` whose transport to the stabilizer of the line
`⟨e₃⟩` has vanishing radical restriction, at the bad line on the classes of zero radical restriction.

The Shapiro coordinate of a class of the cuspidal summand is an eigenvector of every away-from-three
local Hecke operator for the pair character. For the trivial character and `n ≥ 3` the pair
character is within `3/4` of `1` at `T_2`, which separates it from the eigenvalue of `T_2` on the
quotient by the domain, so the local joint generalized eigenspace lies in the domain. Hence the
reference coordinates of summand classes lie in the domains of the edge maps.

The coordinate of a class at any other flag `F` of the same goodness is the transport of the
reference coordinate along an element `γ` of the level with `γ F₀ = F`, and the transport
intertwines the local Hecke operator at the reference flag with the local Hecke operator at `F` on
coordinates (both are the Shapiro–Hecke operator applied to the same global class). The sign-twisted
good-line edge is defined on the whole local cohomology, so only this transport is needed there.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

variable {n : ℕ}

/-- The inducing data with the trivial character. After `obtain ⟨cusp, chi, coh⟩ := D` and
`subst` of `chi = trivialCharacter`, any inducing datum with trivial character has this form. -/
abbrev trivialData (cusp : CuspidalRepresentation) (coh : Cohomological cusp n) :
    InducingData n :=
  ⟨cusp, trivialCharacter, coh⟩

/-! ### The reference cusps -/

/-- **The good-line coordinate of a summand class lies in `ML`.** For the trivial character and
`3 ≤ n`, with a nonzero associate pair. -/
theorem cuspRes_line_true_mem_ML (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
    (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 3 ≤ n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥) {b : StratumH2 n trivialCharacter .line}
    (hb : b ∈ boundarySummand (trivialData cusp coh) .line) :
    cuspRes n trivialCharacter .line true b ∈ LocalUniqueness.ML n := by
  have hc := Separation.pairCharacter_two_sub_one_norm_le_of_trivial
    (trivialData cusp coh) rfl hecke hhecke hn hne
  exact LocalUniqueness.localJoint_le_ML _ hc
    (Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke hhecke .line
      true hb)

/-- **The bad-line coordinate of a summand class lies in the radical kernel**, the domain of
`badLineEdge`. -/
theorem cuspRes_line_false_mem_radicalKernel (cusp : CuspidalRepresentation)
    (coh : Cohomological cusp n) (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 3 ≤ n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥) {b : StratumH2 n trivialCharacter .line}
    (hb : b ∈ boundarySummand (trivialData cusp coh) .line) :
    cuspRes n trivialCharacter .line false b ∈
      LevelThree.BadLineLocal.badLineLocalRadicalKernel n := by
  have hc := Separation.pairCharacter_two_sub_one_norm_le_of_trivial
    (trivialData cusp coh) rfl hecke hhecke hn hne
  exact LevelThree.BadLineBound.localJoint_le_radicalKernel n (by omega) _ hc
    (Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke hhecke .line
      false hb)

/-! ### Other flags of the same orbit -/

/-- **Every away-from-three correspondence transports every flag into its orbit.** -/
theorem transports_flag (t : HeckeCorrespondence) (haway : AwayThree t) (side : Side)
    (F : Flags side) : HeckeShapiro.Transports t F := by
  classical
  intro r hr
  obtain ⟨c, hc⟩ : ∃ c : Bool, c = decide (GoodFlag side F) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ := cuspFlag_transporter side c F (by simp [hc])
  obtain ⟨α, hα⟩ := cuspFlag_transporter side c (r⁻¹ • F)
    (by simp [hc, goodFlag_inv_smul_iff t haway hr side F])
  refine ⟨α * β⁻¹, ?_⟩
  have h1 : β.val⁻¹ • F = cuspFlag side c := by
    rw [← hβ, inv_smul_smul]
  show (α.val * β.val⁻¹) • F = r⁻¹ • F
  rw [mul_smul, h1, hα]

/-- The local Hecke operator of an away-from-three correspondence at an arbitrary flag `F`. -/
def localOpAt (n : ℕ) (χ : RankOneCharacter) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (F : Flags side) :
    Module.End ℂ (H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent n χ)) :=
  LocalHecke.cohomologyAction (rationalCoefficientComponent n χ)
    (HeckeShapiro.localCorrespondence (transports_flag t ht side F))

/-- At a reference flag the local operator at the flag is `localOp`. -/
theorem localOpAt_cuspFlag (n : ℕ) (χ : RankOneCharacter) (t : HeckeCorrespondence)
    (ht : AwayThree t) (side : Side) (good : Bool) :
    localOpAt n χ t ht side (cuspFlag side good) = localOp n χ t ht side good :=
  rfl

/-- **Diagonality at an arbitrary flag.** The Shapiro coordinate at `F` intertwines the actual
Hecke operator with `localOpAt`. -/
theorem fixedPointH2_hecke_flag {χ : RankOneCharacter} (hecke : BoundaryHecke n χ)
    (hhecke : ActualBoundaryHecke n χ hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (F : Flags side) (a : StratumH2 n χ side) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F (hecke side t a) =
      localOpAt n χ t ht side F
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F a) :=
  HeckeShapiro.fixedPointH2_hecke (rationalCoefficientComponent n χ) (hecke side) (hhecke side)
    (transports_flag t ht side F) a

/-- **The coordinate of a summand class at any flag is an eigenclass of `localOpAt`** for the pair
character. -/
theorem localOpAt_fixedPointH2_of_mem (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (F : Flags side) {a : StratumH2 n D.chi side}
    (ha : a ∈ boundarySummand D side) :
    localOpAt n D.chi t ht side F
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) F a) =
      pairCharacter D hecke hhecke t •
        fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) F a := by
  rw [← fixedPointH2_hecke_flag hecke hhecke t ht side F a,
    Separation.hecke_eq_pairCharacter_smul D hecke hhecke t ht side ha]
  exact map_smul _ _ _

/-- **The coordinate at `F` is the transport of the reference coordinate.** -/
theorem fixedPointH2_eq_transport (χ : RankOneCharacter) (side : Side) (good : Bool)
    (F : Flags side) (γ : rationalLevel) (h : γ.val • cuspFlag side good = F)
    (a : StratumH2 n χ side) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F a =
      stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) γ
        (cuspFlag side good) F h (cuspRes n χ side good a) :=
  (stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (cuspFlag side good) F h a).symm

/-- **The transport intertwines `localOp` with `localOpAt` on reference coordinates.** -/
theorem transport_localOp_cuspRes {χ : RankOneCharacter} (hecke : BoundaryHecke n χ)
    (hhecke : ActualBoundaryHecke n χ hecke) (t : HeckeCorrespondence) (ht : AwayThree t)
    (side : Side) (good : Bool) (F : Flags side) (γ : rationalLevel)
    (h : γ.val • cuspFlag side good = F) (a : StratumH2 n χ side) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) γ
        (cuspFlag side good) F h (localOp n χ t ht side good (cuspRes n χ side good a)) =
      localOpAt n χ t ht side F (stabilizerTransportH2 rationalLevel
        (rationalCoefficientComponent n χ) γ (cuspFlag side good) F h
          (cuspRes n χ side good a)) := by
  rw [← cuspRes_hecke hecke hhecke t ht side good a, ← fixedPointH2_eq_transport χ side good F γ h,
    ← fixedPointH2_eq_transport χ side good F γ h, fixedPointH2_hecke_flag hecke hhecke t ht side F]

/-- **The coordinate of a summand class at a good line lies in the transport of `ML`.** If `F` is
`γ`-translate of the reference good line, the Shapiro coordinate of a line summand class at `F` is
the transport of an element of `ML`. -/
theorem fixedPointH2_mem_map_ML (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
    (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 3 ≤ n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥) {b : StratumH2 n trivialCharacter .line}
    (hb : b ∈ boundarySummand (trivialData cusp coh) .line) (F : Flags .line)
    (γ : rationalLevel) (h : γ.val • cuspFlag .line true = F) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F b ∈
      (LocalUniqueness.ML n).map (stabilizerTransportH2 rationalLevel
        (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true) F h) := by
  rw [fixedPointH2_eq_transport trivialCharacter .line true F γ h b]
  exact Submodule.mem_map_of_mem
    (cuspRes_line_true_mem_ML cusp coh hecke hhecke hn hne hb)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership
