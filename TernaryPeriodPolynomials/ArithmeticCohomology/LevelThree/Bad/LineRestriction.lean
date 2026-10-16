module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineLocalOp

@[expose] public section


/-!
# The radical restriction of the local `T_p` at the bad line

The local Hecke operator `T = localOp (T_p)` of the bad-line cusp acts on the radical restriction
`H²(Γ_F, V) → H²(U, V)` (a line, spanned by the `κ`-alternation) through the scalar
`λ_p = p + 1 + εp^{-(n+1)}` (`kappaAlt_hecke`): for every class `y`, `T y - λ_p y` lies in
`badLineLocalRadicalKernel n` (`hecke_sub_mem_kernel`, `badLine_localOp_sub_mem_kernel`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineRestriction

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineEdge BadLineKappa BadLineKernel BadLineModel
  BadLineLocal LocalHecke AmbientHecke IdentityPlaneCoordinate CuspReduction
open GoodLineCosets (cvec crep cq)
open GoodLineRestriction (altF altF_eq radical_alt_sum)

variable (n : ℕ)

/-- The `κ`-alternation of the radical restriction of a two-cocycle of `ΛB`. -/
def kappaAlt (c : groupCohomology.cocycles₂ (Aρ (ρn n))) : ℂ :=
  kappaB n (c (Ux (1, 0), Ux (0, 1))) - kappaB n (c (Ux (0, 1), Ux (1, 0)))

theorem cocycle_kappa (z : groupCohomology.cocycles₂ (Aρ (ρn n))) (x y w : ℤ × ℤ) :
    kappaB n (z (Ux (x + y), Ux w)) + kappaB n (z (Ux x, Ux y)) =
      kappaB n (z (Ux y, Ux w)) + kappaB n (z (Ux x, Ux (y + w))) := by
  have h := twoCocycle_relation (Aρ (ρn n)) z (Ux x) (Ux y) (Ux w)
  rw [Ux_mul, Ux_mul] at h
  have h2 := congrArg (kappaB n) h
  exact (((kappaB n).map_add (z (Ux (x + y), Ux w)) (z (Ux x, Ux y))).symm.trans
    (h2.trans ((kappaB n).map_add _ _))).trans
    (congrArg (· + kappaB n (z (Ux x, Ux (y + w)))) (kappaB_Ux n x _))

theorem det_Bl (p : Nat.Primes) (j : Option (Fin p.val)) :
    (ivmul (1, 0) (Bl p j)).1 * (ivmul (0, 1) (Bl p j)).2 -
      (ivmul (1, 0) (Bl p j)).2 * (ivmul (0, 1) (Bl p j)).1 = p.val := by
  cases j with
  | none =>
    simp only [ivmul, Bl]
    simp
    first | linear_combination (p.val : ℤ) * signP_mul_self p
  | some i =>
    simp [ivmul, Bl]

section Hecke

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- **The local Hecke operator multiplies the `κ`-alternation by `p + 1 + εp^{-(n+1)}`.** -/
theorem kappaAlt_hecke (z : groupCohomology.cocycles₂ (Aρ (ρn n))) :
    kappaAlt n (heckeTwo p hp3 (ρn n) z) =
      ((p.val : ℂ) + 1 + ((epsP p : ℂ)⁻¹) ^ (n + 1)) * kappaAlt n z := by
  set f : ℤ × ℤ → ℤ × ℤ → ℂ := fun x y => kappaB n (z (Ux x, Ux y)) with hfdef
  have hf : ∀ x y w, f (x + y) w + f x y = f y w + f x (y + w) := cocycle_kappa n z
  have hval : ∀ a b : ℤ × ℤ, kappaB n (heckeTwo p hp3 (ρn n) z (Ux a, Ux b)) =
      (∑ j : Option (Fin p.val), (p.val : ℂ)⁻¹ * f (ivmul a (Bl p j)) (ivmul b (Bl p j))) +
        ∑ c : Fin p.val × Fin p.val, ((epsP p : ℂ)⁻¹) ^ (n + 1) *
          f (-cq p (cvec p c - a)) (-cq p (cvec p (crep p (cvec p c - a)) - b)) := by
    intro a b
    rw [heckeTwo_apply, Fintype.sum_sum_type]
    simp only [delta_Ux_inl, next_Ux_inl, delta_Ux_inr, next_Ux_inr, rExpl]
    refine ((kappaB n).map_add _ _).trans (congrArg₂ (· + ·)
      ((map_sum (kappaB n) _ _).trans (Finset.sum_congr rfl (fun j _ => kappaB_sLev n p j _)))
      ((map_sum (kappaB n) _ _).trans (Finset.sum_congr rfl (fun c _ => kappaB_sRad n p c _))))
  have hA : kappaAlt n z = altF f (1, 0) (0, 1) := rfl
  have hlevi : ∀ j : Option (Fin p.val),
      f (ivmul (1, 0) (Bl p j)) (ivmul (0, 1) (Bl p j)) -
        f (ivmul (0, 1) (Bl p j)) (ivmul (1, 0) (Bl p j)) =
          (p.val : ℂ) * altF f (1, 0) (0, 1) := by
    intro j
    have h := altF_eq f hf (ivmul (1, 0) (Bl p j)) (ivmul (0, 1) (Bl p j))
    unfold altF at h
    rw [h, det_Bl]
    push_cast
    rfl
  have hrad := radical_alt_sum p f hf
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  unfold kappaAlt
  rw [hval, hval]
  change _ = _ * altF f (1, 0) (0, 1)
  calc _ = (p.val : ℂ)⁻¹ * ∑ j : Option (Fin p.val),
        (f (ivmul (1, 0) (Bl p j)) (ivmul (0, 1) (Bl p j)) -
          f (ivmul (0, 1) (Bl p j)) (ivmul (1, 0) (Bl p j))) +
      ((epsP p : ℂ)⁻¹) ^ (n + 1) * ∑ c : Fin p.val × Fin p.val,
        (f (-cq p (cvec p c - (1, 0))) (-cq p (cvec p (crep p (cvec p c - (1, 0))) - (0, 1))) -
          f (-cq p (cvec p c - (0, 1))) (-cq p (cvec p (crep p (cvec p c - (0, 1))) - (1, 0)))) := by
        simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
        ring
    _ = _ := by
        rw [Finset.sum_congr rfl (fun j _ => hlevi j), hrad, Finset.sum_const, Finset.card_univ,
          Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        push_cast
        ring

end Hecke

/-- The scalar `λ_p = p + 1 + εp^{-(n+1)}`. -/
def lamB (p : Nat.Primes) : ℂ := (p.val : ℂ) + 1 + ((epsP p : ℂ)⁻¹) ^ (n + 1)

theorem kappaAlt_sub_smul (z w : groupCohomology.cocycles₂ (Aρ (ρn n))) (a : ℂ) :
    kappaAlt n (z - a • w) = kappaAlt n z - a * kappaAlt n w := by
  have key : ∀ u v : HomogeneousPoly n, kappaB n (u - a • v) = kappaB n u - a * kappaB n v :=
    fun u v => by rw [map_sub, map_smul, smul_eq_mul]
  unfold kappaAlt
  refine (congrArg₂ (· - ·) (key (z (Ux (1, 0), Ux (0, 1))) (w (Ux (1, 0), Ux (0, 1))))
    (key (z (Ux (0, 1), Ux (1, 0))) (w (Ux (0, 1), Ux (1, 0))))).trans ?_
  ring

theorem modelCycle_sub_smul (z w : groupCohomology.cocycles₂ (Aρ (ρn n))) (a : ℂ) :
    modelCycle n (z - a • w) = modelCycle n z - a • modelCycle n w := rfl

/-- **Modulo the radical kernel, the local `T_p` at the bad line is the scalar `λ_p`.** -/
theorem hecke_sub_mem_kernel (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : H2 ΛB (ρn n)) :
    cohomologyAction (ρn n) (badLineCosets p hp3) y - lamB n p • y ∈
      badLineLocalRadicalKernel n := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change cohomologyAction (ρn n) (badLineCosets p hp3) (classOf ΛB (ρn n) C) -
    lamB n p • classOf ΛB (ρn n) C ∈ badLineLocalRadicalKernel n
  obtain ⟨c, hc⟩ : ∃ c : groupCohomology.cocycles₂ (Aρ (ρn n)),
      c = ambientCocycleToGroup ΛB (ρn n) C := ⟨_, rfl⟩
  have hy : classOf ΛB (ρn n) C =
      classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c) := by
    apply (standardBadLineInhomogeneousH2Equiv n).injective
    rw [equiv_classOf_lift n p hp3 c, standardBadLineInhomogeneousH2Equiv_classOf,
      semidirect_eq_model, ← hc]
  rw [hy]
  have hT := equiv_cohomologyAction n p hp3 c
  have hz := equiv_classOf_lift n p hp3 c
  let X : H2 ΛB (ρn n) := cohomologyAction (ρn n) (badLineCosets p hp3)
    (classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c))
  let Y : H2 ΛB (ρn n) := classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c)
  let u : H2 ΛB (ρn n) := X - lamB n p • Y
  have hmodel : (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n (heckeTwo p hp3 (ρn n) c)) -
      lamB n p • (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n c) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n (heckeTwo p hp3 (ρn n) c - lamB n p • c)) := by
    rw [modelCycle_sub_smul, map_sub, map_smul]
  have h1 : kappaAlt n (heckeTwo p hp3 (ρn n) c - lamB n p • c) = 0 := by
    rw [kappaAlt_sub_smul, kappaAlt_hecke, lamB, sub_self]
  unfold kappaAlt at h1
  have hκ := ((kappaB n).map_sub _ _).trans h1
  have hu : standardBadLineInhomogeneousH2Equiv n u =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n (heckeTwo p hp3 (ρn n) c)) -
      lamB n p • (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n c) := by
    have e1 : standardBadLineInhomogeneousH2Equiv n u =
        standardBadLineInhomogeneousH2Equiv n X -
          standardBadLineInhomogeneousH2Equiv n (lamB n p • Y) :=
      map_sub (standardBadLineInhomogeneousH2Equiv n) X (lamB n p • Y)
    have e2 : standardBadLineInhomogeneousH2Equiv n (lamB n p • Y) =
        lamB n p • standardBadLineInhomogeneousH2Equiv n Y :=
      map_smul (standardBadLineInhomogeneousH2Equiv n) (lamB n p) Y
    rw [e1, e2]
    exact congrArg₂ (fun a b => a - lamB n p • b) hT hz
  have hz0 : radicalRestrictionH2 integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n) (standardBadLineInhomogeneousH2Equiv n u) = 0 := by
    rw [hu, hmodel]
    exact radicalRestriction_zero n hn (heckeTwo p hp3 (ρn n) c - lamB n p • c) hκ
  exact Submodule.mem_comap.mpr hz0

/-- **The local `T_p` at the bad-line cusp modulo the radical kernel.** For the correspondence
`TpExistence.tp p` (`p ≠ 3`), `localOp y - λ_p y` has vanishing radical restriction, where
`λ_p = p + 1 + εp^{-(n+1)}`. -/
theorem badLine_localOp_sub_mem_kernel (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CuspH2 n trivialCharacter .line false) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line false y -
      lamB n p • y ∈ badLineLocalRadicalKernel n := by
  rw [BadLineLocalOp.localOp_badLine_tp p n hp3]
  exact hecke_sub_mem_kernel n hn p hp3 y

end TernaryPeriodPolynomials.LevelThree.BadLineRestriction
