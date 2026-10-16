module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.LocalMultiplicity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Sign
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBoundTwo
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# Local upper bounds at the plane cusps for the prime correspondences only

The dimension bounds for the local joint generalized eigenspace at the plane cusps are proved by
embedding it, through the Hochschild–Serre edge, into a joint generalized eigenspace of the classical
Hecke operators `T_p`, using only the edge formulas of the prime correspondences. The same proofs
therefore bound the joint generalized eigenspace `J` of the local operators of the `T_p` alone:

* identity plane, trivial character: for odd `n` the edge maps `J` into the joint generalized
  eigenspace of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` with eigenvalues `p^{n+2}(c(T_p) - 1)`, which has
  dimension at most one when `‖c(T_2) - 1‖ ≤ 3/4`; for even `n` the local cohomology vanishes;
* identity plane, odd character of conductor three: the same with `H¹(GL₂(ℤ), Sym^{n+1})`, the
  eigenvalues `p^{n+1}(c(T_p) - sgn_p)` and `‖c(T_2) + 1‖ ≤ 3/4`;
* good plane, trivial character: the edge maps `J` into the joint generalized eigenspace of the level
  three operators on `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`, which has dimension at most two when
  `‖c(T_2) - 1‖ ≤ 3/4`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators

open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ### The identity plane, trivial character -/

/-- **The identity-plane edge maps the prime eigenspace into the joint generalized eigenspace of
level-one `H¹`.** -/
theorem edgeH2_mem_jointH1_gen (c : HeckeCorrespondence → ℂ) (hn : 0 < n) (hodd : Odd n)
    {x : CuspH2 n trivialCharacter .plane false}
    (hx : x ∈ localJointGen n trivialCharacter c .plane false) :
    IdentityPlaneHecke.edgeH2 n hn hodd x ∈
      jointH1 (n + 1) (-1) (LocalUniqueness.eIdentity n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hxp := (Submodule.mem_iInf _).mp hx ⟨p, hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 2))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  exact LocalUniqueness.map_mem_maxGenEigenspace_of_affine (IdentityPlaneHecke.edgeH2 n hn hodd)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p) _ _ hs
    (IdentityPlaneLocalOp.edgeH2_localOp_tp p n hn hodd hp3) hxp

/-- **Identity-plane cusp, prime correspondences: dimension at most one.** -/
theorem localUpperBoundGen_identityPlane (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalUpperBoundGen n trivialCharacter c .plane false 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · have hbot : localJointGen n trivialCharacter c .plane false = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [Submodule.mem_bot]
      exact IdentityPlaneEven.cuspH2_identityPlane_eq_zero n hn heven x
    unfold LocalUpperBoundGen
    rw [hbot]
    exact ⟨inferInstance, by simp⟩
  · have : FiniteDimensional ℂ (jointH1 (n + 1) (-1) (LocalUniqueness.eIdentity n c)) :=
      LevelOneEisenstein.jointH1_finiteDimensional _ _ _
    refine ⟨LevelOneEisenstein.finiteDimensional_of_injective_map _
      (IdentityPlaneHecke.edgeH2_injective n hn hodd) _
      (jointH1 (n + 1) (-1) (LocalUniqueness.eIdentity n c))
      (fun _ hx => edgeH2_mem_jointH1_gen c hn hodd hx),
      (LocalUniqueness.finrank_le_of_injective_map _
        (IdentityPlaneHecke.edgeH2_injective n hn hodd) _
        (jointH1 (n + 1) (-1) (LocalUniqueness.eIdentity n c))
        (fun _ hx => edgeH2_mem_jointH1_gen c hn hodd hx)).trans ?_⟩
    exact LevelOneEisenstein.finrank_jointH1_identity_le_one hodd _
      (c (TpExistence.tp LocalUniqueness.two)) hc rfl

/-- **Identity plane, pair character of a trivial-character datum, prime correspondences.** -/
theorem localUpperBoundGen_identityPlane_pair (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) .plane false 1 := by
  have key := localUpperBoundGen_identityPlane (n := n) (by omega) (pairCharacter D hecke hhecke)
    (pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne)
  rw [← hχ] at key
  exact key

/-! ### The identity plane, odd character of conductor three -/

/-- **The twisted identity-plane edge maps the prime eigenspace into the joint generalized
eigenspace of level-one `H¹`.** -/
theorem edgeH2T_mem_jointH1_gen (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ) (hn : 0 < n)
    (hodd : Odd n) {x : CuspH2 n χ .plane false}
    (hx : x ∈ localJointGen n χ c .plane false) :
    Twisted.edgeH2T n χ hχ hn hodd x ∈
      jointH1 (n + 1) 0 (Twisted.eIdentityT n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hxp := (Submodule.mem_iInf _).mp hx ⟨p, hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  exact Twisted.map_mem_maxGenEigenspace_of_affineT
    (Twisted.edgeH2T n χ hχ hn hodd)
    (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p) _ _ _ hs
    (Twisted.edgeH2T_localOp_tp n χ hχ p hn hodd hp3) hxp

/-- **Twisted identity-plane cusp, prime correspondences: dimension at most one.** -/
theorem localUpperBoundGen_identityPlane_twisted (hn : 0 < n) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4) :
    LocalUpperBoundGen n χ c .plane false 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · have hbot : localJointGen n χ c .plane false = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [Submodule.mem_bot]
      exact Twisted.cuspH2_identityPlane_eq_zeroT n χ hχ hn heven x
    unfold LocalUpperBoundGen
    rw [hbot]
    exact ⟨inferInstance, by simp⟩
  · have : FiniteDimensional ℂ (jointH1 (n + 1) 0 (Twisted.eIdentityT n c)) :=
      LevelOneEisenstein.jointH1_finiteDimensional _ _ _
    refine ⟨LevelOneEisenstein.finiteDimensional_of_injective_map
      (Twisted.edgeH2T n χ hχ hn hodd)
      (Twisted.edgeH2T_injective n χ hχ hn hodd) _
      (jointH1 (n + 1) 0 (Twisted.eIdentityT n c))
      (fun _ hx => edgeH2T_mem_jointH1_gen χ hχ c hn hodd hx),
      (LocalUniqueness.finrank_le_of_injective_map (Twisted.edgeH2T n χ hχ hn hodd)
        (Twisted.edgeH2T_injective n χ hχ hn hodd) _
        (jointH1 (n + 1) 0 (Twisted.eIdentityT n c))
        (fun _ hx => edgeH2T_mem_jointH1_gen χ hχ c hn hodd hx)).trans ?_⟩
    refine LevelOneEisenstein.finrank_jointH1_le_one_of_norm_lt hodd.add_one
      (Nat.succ_pos n) 0 _ ?_
    have hexp : (2 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1 - 0) = 2 ^ (n + 2) := by
      rw [show ((n + 1 : ℕ) : ℤ) + 1 - 0 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have h2 : ‖((LocalUniqueness.two.val : ℕ) : ℂ)‖ = 2 := by simp [LocalUniqueness.two]
    rw [hexp]
    change ‖Twisted.eIdentityT n c LocalUniqueness.two‖ < 2 ^ (n + 2)
    have hE : Twisted.eIdentityT n c LocalUniqueness.two =
        (c (TpExistence.tp LocalUniqueness.two) + 1) *
          ((LocalUniqueness.two.val : ℂ) ^ (n + 1)) := by
      unfold Twisted.eIdentityT
      rw [Twisted.sgnP_two, Int.cast_neg, Int.cast_one, sub_neg_eq_add, div_inv_eq_mul]
    rw [hE, norm_mul, norm_pow, h2]
    have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    calc ‖c (TpExistence.tp LocalUniqueness.two) + 1‖ * 2 ^ (n + 1) ≤ 3 / 4 * 2 ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hc hpos.le
      _ < 2 ^ (n + 2) := by
        have hx : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
        rw [hx]
        linarith

/-- **Twisted identity plane, pair character of a conductor-three datum, prime
correspondences.** -/
theorem localUpperBoundGen_identityPlane_pair_twisted (hn : 3 ≤ n) (D : InducingData n)
    (h3 : LevelOneNontrivial.ConductorThree D.chi)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) .plane false 1 :=
  localUpperBoundGen_identityPlane_twisted (by omega) D.chi hneg _
    (Twisted.pairCharacter_two_add_one_norm_le D h3 hneg hecke hhecke hn hne)

/-! ### The good plane, trivial character -/

/-- **The good-plane edge maps the prime eigenspace into the level-three joint generalized
eigenspace.** -/
theorem map_localJointGen_le (hn : 0 < n) (c : HeckeCorrespondence → ℂ) :
    (localJointGen n trivialCharacter c .plane true).map
        (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn) ≤
      LevelThree.GoodPlaneJoint.levelJoint n c := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [LevelThree.GoodPlaneJoint.levelJoint, Submodule.mem_iInf, Subtype.forall]
  intro p hp3
  have hy0 : y ∈ localJointGen n trivialCharacter c .plane true := hy
  rw [localJointGen, Submodule.mem_iInf] at hy0
  have hy' := hy0 ⟨p, hp3⟩
  have hp : ((p.val : ℂ) ^ (n + 2))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  refine LevelThree.GoodPlaneJoint.mem_maxGen_of_affine _ _ _ hp ?_
  refine intertwine_mem_maxGenEigenspace (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane true)
    (1 + ((p.val : ℂ) ^ (n + 2))⁻¹ • LevelThree.LevelThreeHeckeH1.levelHecke (n + 1) (-1)
      p hp3) ?_ _ hy'
  intro x
  rw [LevelThree.GoodPlaneLocalOp.goodPlaneEdge_localOp_tp p hp3 n hn x]
  rfl

/-- **Good-plane cusp, prime correspondences: dimension at most two.** -/
theorem localUpperBoundGen_goodPlane_two (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalUpperBoundGen n trivialCharacter c .plane true 2 := by
  have hn0 : 0 < n := by omega
  have hlevel := LevelThree.GoodPlaneBoundTwo.finrank_levelJoint_le_two n hn c hc
    (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)
  have : FiniteDimensional ℂ (CuspH2 n trivialCharacter .plane true) :=
    LevelThree.GoodPlaneEdge3.goodPlane_finiteDimensional hn0
  have : FiniteDimensional ℂ
      (CrossedH1 (LevelThree.ParabolicBounds.levelRep (n + 1) (-1))) :=
    LevelThree.ParabolicBounds.level_H1_finiteDimensional (-1) (Nat.succ_pos n)
  refine ⟨inferInstance, ?_⟩
  have heq := LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn0)
      (LevelThree.GoodPlaneEdge3.goodPlaneEdge_injective hn0)
      (localJointGen n trivialCharacter c .plane true))
  rw [heq]
  exact (Submodule.finrank_mono (map_localJointGen_le hn0 c)).trans hlevel

/-- **Good plane, pair character of a trivial-character datum, prime correspondences.** -/
theorem localUpperBoundGen_goodPlane_pair (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalUpperBoundGen n D.chi (pairCharacter D hecke hhecke) .plane true 2 := by
  have key := localUpperBoundGen_goodPlane_two (n := n) (by omega) (pairCharacter D hecke hhecke)
    (pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne)
  rw [← hχ] at key
  exact key

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
