module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inflation
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneCoordinate

@[expose] public section


/-!
# `K†` comparison, the averaging step for the existence clause

`res_classK_plane`: if the transport of a `Γ(N)`-class `c'` to `Γ ∩ Γ(N)` restricts at every plane as a `K†` stratum class `ξ` (`res_eq_of_reps`: it suffices to
know this at the representatives of the faces of `Γ(N)`), then the `K†`-corestriction `classK c'` restricts at every plane as `ξ` after restriction to `Γ_F ∩ Γ(N)`.
Uses the averaging formula `res_classK_eq_avg` and the compatibility `resPrincipal_transport` of the transport `stabilizerTransportH2` of `K†`-stratum classes with
the conjugation `actH2Conj`; `actH2_of_mem`: inner automorphisms act trivially on `H²`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- Inner automorphisms act trivially on `H²` of a group. -/
theorem actH2_of_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {N' : Subgroup G} {s : G} (hs : s ∈ N') (hn : ∀ m ∈ N', s⁻¹ * m * s ∈ N') (y : H2 N' ρ) :
    actH2 ρ s hn y = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (actCocycle ρ s hn z) = Submodule.Quotient.mk z
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact IsEq.act_mem ρ ((mem_cochains_iff ρ N' 2 _).mp z.val.2) hs


section Conj

omit [NeZero N] in
/-- Restriction to `Γ ∩ Γ(N)` commutes with the transport of the stabilizer cohomology along `q ∈ K†`. -/
theorem resPrincipal_transport (q : rationalLevel) {F' F : Flags .plane} (hF : q.val • F' = F)
    (hg : LevelTransfer.IsConj (fixedPointLevel (levelPrincipal N) F') (fixedPointLevel (levelPrincipal N) F) q.val)
    (z : H2 (fixedPointLevel rationalLevel F') (rationalCoefficientComponent n trivialCharacter)) :
    resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) q F' F hF z) =
      actH2Conj (rationalCoefficientComponent n trivialCharacter) q.val hg
        (resPrincipal N F' (rationalCoefficientComponent n trivialCharacter) z) := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

omit [NeZero N] in
/-- A class of `H²(Γ ∩ Γ(N))` restricts compatibly along the `Γ ∩ Γ(N)`-translates of a plane. -/
theorem res_levelPrincipal_conj (y : H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter))
    {q : RationalGL3} (hqP : q ∈ levelPrincipal N) {F F' : Flags .plane} (hF : F' = q⁻¹ • F) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F) y =
      actH2Conj (rationalCoefficientComponent n trivialCharacter) q
        (isConj_stab_principal N (levelPrincipal_le N hqP) hF)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F') y) := by
  have h := res_actH2_conj N n (levelPrincipal_le N hqP) hF y
  rwa [actH2_of_mem (rationalCoefficientComponent n trivialCharacter) hqP] at h

end Conj

section Existence

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

variable {N n}

omit [NeZero N] in
/-- **The restrictions of a `Γ ∩ Γ(N)`-class at all planes are determined by those at the representatives of the faces**, once they
agree with the `K†` stratum class `ξ` there. -/
theorem res_eq_of_reps (h3 : 3 ∣ N) (ξ : StratumH2 n trivialCharacter .plane)
    (y : H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter))
    (hrep : ∀ i : PlaneFaces N,
      resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt (planeFaceRepr i))) y =
      resPrincipal N (planeFlagAt (planeFaceRepr i)) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (planeFlagAt (planeFaceRepr i)) ξ))
    (F : Flags .plane) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F) y =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) := by
  obtain ⟨h, rfl⟩ := planeFlagAt_surjective F
  set i : PlaneFaces N := Quotient.mk (planeFaceSetoid N) h with hi
  obtain ⟨γ, hγ, hF⟩ := (planeFlagAt_orbit_iff N h (planeFaceRepr i)).mpr
    ((planeFaceSetoid N).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid N) h))
  have hqP : (Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹ ∈ levelPrincipal N :=
    (levelPrincipal N).inv_mem (mapGL_mem_levelPrincipal N h3 hγ)
  have hF' : planeFlagAt (planeFaceRepr i) = ((Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹)⁻¹ • planeFlagAt h := by
    rw [inv_inv]; exact hF
  have hF'' : ((Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹) • planeFlagAt (planeFaceRepr i) = planeFlagAt h := by
    rw [hF, smul_smul, inv_mul_cancel, one_smul]
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹ ∈ rationalLevel := levelPrincipal_le N hqP
  rw [res_levelPrincipal_conj N n _ hqP hF', hrep i]
  have := resPrincipal_transport (N := N) (n := n) ⟨_, hmem⟩ hF''
    (isConj_stab_principal N hmem hF') (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (planeFlagAt (planeFaceRepr i)) ξ)
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    ⟨_, hmem⟩ (planeFlagAt (planeFaceRepr i)) (planeFlagAt h) hF'' ξ
  rw [e] at this
  exact this.symm

omit [NeZero N] in
theorem res_act_term (g : ↥rationalLevel) (F : Flags .plane)
    (y : H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter))
    (ξ : StratumH2 n trivialCharacter .plane)
    (hy : ∀ F : Flags .plane, resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) F) y =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ)) :
    resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (actH2 (rationalCoefficientComponent n trivialCharacter) (g : RationalGL3)
          (levelPrincipal_norm N _ g.2) y) =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) := by
  have h1 := res_actH2_conj N n g.2 (F := F) (F' := g.val⁻¹ • F) rfl y
  rw [h1]
  rw [hy (g.val⁻¹ • F)]
  have hF' : g.val • (g.val⁻¹ • F) = F := smul_inv_smul g.val F
  have h2 := resPrincipal_transport (N := N) (n := n) g hF' (isConj_stab_principal N g.2 rfl)
    (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (g.val⁻¹ • F) ξ)
  have e := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    g (g.val⁻¹ • F) F hF' ξ
  rw [e] at h2
  exact h2.symm

/-- **The averaging step.**  If the transport of a `Γ(N)`-class `c'` to `Γ ∩ Γ(N)` restricts at every plane as the `K†` stratum
class `ξ`, then the `K†`-corestriction of `c'` restricts at every plane as `ξ`, after restriction to `Γ_F ∩ Γ(N)`. -/
theorem res_classK_plane (h3 : 3 ∣ N) (hN : 3 ≤ N) (c' : groupCohomology.H2 (gammaRep (gammaN N) n))
    (ξ : StratumH2 n trivialCharacter .plane)
    (hy : ∀ F : Flags .plane, resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) F) (classPrincipal N h3 n hN c') =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ))
    (F : Flags .plane) :
    resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n c')) =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) := by
  have h := res_classK_eq_avg N n h3 hN c' F
  refine Eq.trans h ?_
  have hterm : ∀ q : ↥rationalLevel ⧸ (levelPrincipal N).subgroupOf rationalLevel,
      resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_self (levelPrincipal N) F)
        (actH2 (rationalCoefficientComponent n trivialCharacter) ((Quotient.out q : ↥rationalLevel) : RationalGL3)
          (levelPrincipal_norm N _ (Quotient.out q).2) (classPrincipal N h3 n hN c')) =
      resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F ξ) := by
    intro q
    exact res_act_term (N := N) (n := n) (Quotient.out q) F _ ξ hy
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

end Existence

end TernaryPeriodPolynomials.Argument.KDaggerComparison
