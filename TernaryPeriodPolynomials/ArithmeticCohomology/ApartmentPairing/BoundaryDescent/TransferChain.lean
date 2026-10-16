module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.CosetSum

@[expose] public section


/-!
# The chain-level right-coset-sum transfer `∑_{H'\H}` and its identification with `resQ`

Formalized by Claude Sonnet 5.5.  Paper: passage to a finite-index subgroup in Lemma 3.3.

For a `G`-module `B` and subgroups `H' , H` of `G` with `[H : H']` finite, `trCoinv` is the transfer `B_H → B_{H'}`,
`[b]_H ↦ ∑_{r ∈ H'\H} [r · b]_{H'}`, a sum over the right cosets `H'\H` (`RCos`), well defined because the sum is independent of the chosen
representatives (`H'`-invariance of `[·]_{H'}`) and `H`-invariant (`sum_rcos_mul`).  `transferCx Y` is the induced chain map
`(Res_H Y)_H → (Res_{H'} Y)_{H'}` of coinvariant complexes (the differential of `Y` is `G`-equivariant).
`transfer_eq_resQ`: on `H₃(∂X̄_H; 𝓜)` its homology map is the already proved `resQ` (`[H:H']` times the quotient of the `H`-average).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open Representation

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Module

variable {G : Type} [Group G] (H H' : Subgroup G) [(H'.subgroupOf H).FiniteIndex]
  {B : Type} [AddCommGroup B] [Module ℚ B] (ρ : Representation ℚ G B)

/-- The class `b ↦ [ρ(x) b]_{H'}` for `x ∈ H`. -/
def trTerm (x : ↥H) : B →ₗ[ℚ] Coinvariants (ρ.comp H'.subtype) :=
  Coinvariants.mk (ρ.comp H'.subtype) ∘ₗ ρ x.1

omit [(H'.subgroupOf H).FiniteIndex] in
theorem trTerm_left (s : ↥(H'.subgroupOf H)) (x : ↥H) (b : B) :
    trTerm H H' ρ ((s : ↥H) * x) b = trTerm H H' ρ x b := by
  have hs : ((s : ↥H) : G) ∈ H' := Subgroup.mem_subgroupOf.mp s.2
  change Coinvariants.mk (ρ.comp H'.subtype) (ρ (((s : ↥H) : G) * (x : G)) b) = Coinvariants.mk (ρ.comp H'.subtype) (ρ x.1 b)
  rw [map_mul, Module.End.mul_apply]
  exact Coinvariants.mk_self_apply (ρ.comp H'.subtype) (⟨((s : ↥H) : G), hs⟩ : ↥H') (ρ x.1 b)

/-- **The transfer, as a literal sum over the right cosets `H'\H`**: `B → (B)_{H'}`, `b ↦ ∑_{r ∈ H'\H} [r · b]_{H'}`. -/
def trLin : B →ₗ[ℚ] Coinvariants (ρ.comp H'.subtype) :=
  ∑ r : RCos (H'.subgroupOf H), trTerm H H' ρ r.out

theorem trLin_apply (b : B) :
    trLin H H' ρ b = ∑ r : RCos (H'.subgroupOf H), Coinvariants.mk (ρ.comp H'.subtype) (ρ (r.out : ↥H).1 b) := by
  simp [trLin, LinearMap.sum_apply, trTerm]

theorem trLin_invariant (x : ↥H) : trLin H H' ρ ∘ₗ (ρ.comp H.subtype) x = trLin H H' ρ := by
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply]
  simp only [trLin, LinearMap.sum_apply]
  have h := sum_rcos_mul (H'.subgroupOf H) (fun y : ↥H => trTerm H H' ρ y b)
    (fun s hs y => trTerm_left H H' ρ ⟨s, hs⟩ y b) x
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun r _ => ?_
  change trTerm H H' ρ r.out (ρ x.1 b) = trTerm H H' ρ (r.out * x) b
  change Coinvariants.mk (ρ.comp H'.subtype) (ρ (r.out : ↥H).1 (ρ x.1 b)) =
    Coinvariants.mk (ρ.comp H'.subtype) (ρ ((r.out : ↥H).1 * x.1) b)
  rw [map_mul, Module.End.mul_apply]

/-- **The transfer `B_H → B_{H'}`**: `[b]_H ↦ ∑_{r ∈ H'\H} [r · b]_{H'}`. -/
def trCoinv : Coinvariants (ρ.comp H.subtype) →ₗ[ℚ] Coinvariants (ρ.comp H'.subtype) :=
  Coinvariants.lift _ (trLin H H' ρ) (trLin_invariant H H' ρ)

@[simp]
theorem trCoinv_mk (b : B) :
    trCoinv H H' ρ (Coinvariants.mk (ρ.comp H.subtype) b) =
      ∑ r : RCos (H'.subgroupOf H), Coinvariants.mk (ρ.comp H'.subtype) (ρ (r.out : ↥H).1 b) :=
  trLin_apply H H' ρ b

end Module

section Chain

variable {G : Type} [Group G] (H H' : Subgroup G) [(H'.subgroupOf H).FiniteIndex]

/-- A complex of `G`-modules restricted to the subgroup `H`. -/
abbrev resCx (Y : ChainComplex (Rep.{0} ℚ G) ℕ) : ChainComplex (Rep.{0} ℚ ↥H) ℕ :=
  ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y

theorem trCoinv_comm (Y : ChainComplex (Rep.{0} ℚ G) ℕ) (i j : ℕ) (v : Y.X i) :
    cK.map ((resCx H' Y).d i j) (trCoinv H H' (Y.X i).ρ (Coinvariants.mk ((Y.X i).ρ.comp H.subtype) v)) =
      trCoinv H H' (Y.X j).ρ (cK.map ((resCx H Y).d i j) (Coinvariants.mk ((Y.X i).ρ.comp H.subtype) v)) := by
  have h1 : ∀ r : RCos (H'.subgroupOf H),
      cK.map ((resCx H' Y).d i j) (Coinvariants.mk ((Y.X i).ρ.comp H'.subtype) ((Y.X i).ρ (r.out : ↥H).1 v)) =
        Coinvariants.mk ((Y.X j).ρ.comp H'.subtype) ((Y.X j).ρ (r.out : ↥H).1 ((Y.d i j).hom v)) := fun r =>
    (cK_map_mk ((resCx H' Y).d i j) ((Y.X i).ρ (r.out : ↥H).1 v)).trans
      (congrArg (Coinvariants.mk ((Y.X j).ρ.comp H'.subtype)) (Rep.hom_comm_apply (Y.d i j) (r.out : ↥H).1 v))
  have h2 : cK.map ((resCx H Y).d i j) (Coinvariants.mk ((Y.X i).ρ.comp H.subtype) v) =
      Coinvariants.mk ((Y.X j).ρ.comp H.subtype) ((Y.d i j).hom v) := cK_map_mk ((resCx H Y).d i j) v
  rw [trCoinv_mk, h2, trCoinv_mk]
  exact (map_sum (cK.map ((resCx H' Y).d i j)).hom _ _).trans (Finset.sum_congr rfl fun r _ => h1 r)

/-- **The chain-level transfer** `(Res_H Y)_H → (Res_{H'} Y)_{H'}`, `[y]_H ↦ ∑_{r ∈ H'\H} [r · y]_{H'}`. -/
def transferCx (Y : ChainComplex (Rep.{0} ℚ G) ℕ) : CxK (resCx H Y) ⟶ CxK (resCx H' Y) where
  f n := ModuleCat.ofHom (trCoinv H H' (Y.X n).ρ)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    apply LinearMap.ext
    intro v
    exact trCoinv_comm H H' Y i j v

theorem transferCx_mk (Y : ChainComplex (Rep.{0} ℚ G) ℕ) (n : ℕ) (v : (Y.X n)) :
    ((transferCx H H' Y).f n).hom (Coinvariants.mk _ v) =
      ∑ r : RCos (H'.subgroupOf H), Coinvariants.mk ((Y.X n).ρ.comp H'.subtype) ((Y.X n).ρ (r.out : ↥H).1 v) :=
  trCoinv_mk H H' (Y.X n).ρ v

end Chain

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
