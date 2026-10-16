module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeMixedFlag
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeDual
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Decomp

@[expose] public section


/-!
# The Stokes relation at `Γ(6)` for the induced module `Ind_{Γ(M)}^{Γ(6)} E`, decomposed along the orbit idempotents

Formalized by Claude Sonnet 5.5.

`eO Δ S o = jL ∘ qL` is the `S`-equivariant idempotent of `V = Fun(G/Δ, E)` cutting out the `S`-orbit `o` (`eO_equivariant`, `eO_orth`, `eO_sum`).  Instantiating the `gamma6_stokes_decomposed` at `ρ_V = permRep ρ Δ` with the families `eO` for the line groups `gammaNQAt 6 i.rep` and plane groups `gammaNPAt 6 (planeFaceRepr i)` gives
`gamma6_stokes_ind`: the Stokes relation as a sum over the faces and the orbits of the diagonal pairings `B_i(h2E e_O (res_i c_V), h2E e_Oᵀ (res_i c'_V))`.  For a level-`M` class
`c₀` and dual class `c₀'` with zero flag restrictions, the induced classes (Shapiro coordinates the transports of `c₀`, `c₀'`; the dual class through `dualRepHom`)
have zero flag restrictions at level 6 (`res_flag_ind_zero`, `res_h2Hom_zero`), whence `gamma6_stokes_ind_M`.  What remains for Stokes at `Γ(M)` is the identification of each
diagonal term with the `Γ(M)`-face pairing of the Mackey components (`phi_qRep`): the comparison of the cone pairing with the algebraic pairing for general coefficients.
-/

open CategoryTheory
open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Family

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ S : Subgroup G)

/-- The `S`-equivariant idempotent of `Fun(G/Δ, E)` cutting out the `S`-orbit `o`. -/
def eO (o : orbitRel.Quotient ↥S (G ⧸ Δ)) : ((G ⧸ Δ) → E) →ₗ[ℂ] ((G ⧸ Δ) → E) :=
  jL S (Quotient.out o : G ⧸ Δ) ∘ₗ qL S (Quotient.out o : G ⧸ Δ)

theorem eO_equivariant (o : orbitRel.Quotient ↥S (G ⧸ Δ)) (s : ↥S) (f : (G ⧸ Δ) → E) :
    eO Δ S o (permRep ρ Δ s.val f) = permRep ρ Δ s.val (eO Δ S o f) := by
  have hq : qL S (Quotient.out o : G ⧸ Δ) (permRep ρ Δ s.val f) =
      permRep (ρ.comp S.subtype) (stabilizer ↥S (Quotient.out o : G ⧸ Δ)) s (qL S (Quotient.out o : G ⧸ Δ) f) :=
    Rep.hom_comm_apply (qRep ρ S (Quotient.out o : G ⧸ Δ)) s f
  have hj : jL S (Quotient.out o : G ⧸ Δ) (permRep (ρ.comp S.subtype) (stabilizer ↥S (Quotient.out o : G ⧸ Δ)) s
      (qL S (Quotient.out o : G ⧸ Δ) f)) = permRep ρ Δ s.val (jL S (Quotient.out o : G ⧸ Δ) (qL S (Quotient.out o : G ⧸ Δ) f)) :=
    Rep.hom_comm_apply (jRep ρ S (Quotient.out o : G ⧸ Δ)) s (qL S (Quotient.out o : G ⧸ Δ) f)
  change jL S _ (qL S _ (permRep ρ Δ s.val f)) = _
  rw [hq]
  exact hj

theorem eO_orth {o o' : orbitRel.Quotient ↥S (G ⧸ Δ)} (h : o ≠ o') (f : (G ⧸ Δ) → E) :
    eO Δ S o' (eO Δ S o f) = 0 := by
  funext y
  by_cases hy : y ∈ orbit ↥S (Quotient.out o' : G ⧸ Δ)
  · have hy2 : y ∉ orbit ↥S (Quotient.out o : G ⧸ Δ) := fun hy2 =>
      h (((out_mem_orbit_iff S o y).mp hy2).symm.trans ((out_mem_orbit_iff S o' y).mp hy))
    change jL S (Quotient.out o' : G ⧸ Δ) (qL S (Quotient.out o' : G ⧸ Δ) (eO Δ S o f)) y = 0
    rw [jL_qL_of_mem S _ _ hy]
    exact jL_qL_of_not_mem S _ f hy2
  · exact jL_qL_of_not_mem S _ _ hy

theorem eO_sum [Fintype (orbitRel.Quotient ↥S (G ⧸ Δ))] (f : (G ⧸ Δ) → E) : ∑ o, eO Δ S o f = f := by
  funext y
  rw [Finset.sum_apply]
  exact sum_jL_qL S f y

/-- The finiteness of the orbit set from that of `G/Δ`. -/
instance orbitQuotientFintype [Finite (G ⧸ Δ)] : Fintype (orbitRel.Quotient ↥S (G ⧸ Δ)) := Fintype.ofFinite _

end Family

section HomZero

variable {G H : Type} [Group G] [Group H] (ι : H →* G) {A B : Rep ℂ G} (f : A ⟶ B)

/-- A morphism of `G`-modules carries a class with zero restriction along `ι` to a class with zero restriction. -/
theorem res_h2Hom_zero (x : groupCohomology.H2 A) (hx : twoCohomologyRestriction ι A x = 0) :
    twoCohomologyRestriction ι B (h2Hom f x) = 0 := by
  rw [twoCohomologyRestriction_eq_h2Map] at hx
  rw [twoCohomologyRestriction_eq_h2Map, h2Hom_eq_h2Map]
  have e1 := h2Map_comp (MonoidHom.id G) ι A B (Rep.res ι B) f.hom.toLinearMap (fun g v => Rep.hom_comm_apply f g v)
    LinearMap.id (fun _ _ => rfl) x
  have e2 := h2Map_comp ι (MonoidHom.id H) A (Rep.res ι A) (Rep.res ι B) LinearMap.id (fun _ _ => rfl)
    f.hom.toLinearMap (fun g v => Rep.hom_comm_apply f (ι g) v) x
  rw [hx, map_zero] at e2
  rw [e1]
  exact (h2Map_congr (by ext; rfl) _ _ _ _ (LinearMap.ext fun _ => rfl) x).trans e2.symm

end HomZero


section Faces

variable {E : Type} [AddCommGroup E] [Module ℂ E] [Module ℚ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (Δ : Subgroup ↥(gammaN 6))

/-- The line group of the face `i` as a subgroup of `Γ(6)`. -/
abbrev lineSub (i : LineFaces 6) : Subgroup ↥(gammaN 6) := (gammaNQAt 6 i.rep).subgroupOf (gammaN 6)

/-- The plane group of the face `i` as a subgroup of `Γ(6)`. -/
abbrev planeSub (i : PlaneFaces 6) : Subgroup ↥(gammaN 6) := (gammaNPAt 6 (planeFaceRepr i)).subgroupOf (gammaN 6)

omit [Module ℚ E] in
theorem eO_line_equivariant (i : LineFaces 6) (j : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ))
    (t : gammaNQAt 6 i.rep) (v : (↥(gammaN 6) ⧸ Δ) → E) :
    eO Δ (lineSub i) j (permRep ρ Δ (lineIncl i t) v) = permRep ρ Δ (lineIncl i t) (eO Δ (lineSub i) j v) :=
  eO_equivariant ρ Δ (lineSub i) j ⟨lineIncl i t, t.2⟩ v

omit [Module ℚ E] in
theorem eO_plane_equivariant (i : PlaneFaces 6) (j : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ))
    (t : gammaNPAt 6 (planeFaceRepr i)) (v : (↥(gammaN 6) ⧸ Δ) → E) :
    eO Δ (planeSub i) j (permRep ρ Δ (planeIncl i t) v) = permRep ρ Δ (planeIncl i t) (eO Δ (planeSub i) j v) :=
  eO_equivariant ρ Δ (planeSub i) j ⟨planeIncl i t, t.2⟩ v

variable [Finite (↥(gammaN 6) ⧸ Δ)]

/-- The face pairings of two classes of the induced module and its dual, summed over the faces and the orbit idempotents: the left side of the decomposed Stokes relation. -/
def stokesSum (c : groupCohomology.H2 (Rep.of (permRep ρ Δ))) (c' : groupCohomology.H2 (Rep.of (permRep ρ Δ).dual)) : ℂ :=
  ∑ i : LineFaces 6, ∑ j : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ), lineFacePairM (permRep ρ Δ) i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep ρ Δ))) (eO Δ (lineSub i) j)
        (fun k v => eO_line_equivariant ρ Δ i j k v)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep ρ Δ)) c))
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep ρ Δ).dual)) (eO Δ (lineSub i) j).dualMap
        (fun k v => lineHeD (permRep ρ Δ) i (eO Δ (lineSub i) j) (eO_line_equivariant ρ Δ i j) k v)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep ρ Δ).dual) c')) +
    ∑ i : PlaneFaces 6, ∑ j : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ), planeFacePairM (permRep ρ Δ) i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep ρ Δ))) (eO Δ (planeSub i) j)
        (fun k v => eO_plane_equivariant ρ Δ i j k v)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep ρ Δ)) c))
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep ρ Δ).dual)) (eO Δ (planeSub i) j).dualMap
        (fun k v => planeHeD (permRep ρ Δ) i (eO Δ (planeSub i) j) (eO_plane_equivariant ρ Δ i j) k v)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep ρ Δ).dual) c'))

/-- **The Stokes relation at `Γ(6)` for the induced module, decomposed along the orbit idempotents** (S1's `gamma6_stokes_decomposed` at `ρ_V = permRep ρ Δ`). -/
theorem gamma6_stokes_ind (c : groupCohomology.H2 (Rep.of (permRep ρ Δ))) (c' : groupCohomology.H2 (Rep.of (permRep ρ Δ).dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of (permRep ρ Δ)) c = 0)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of (permRep ρ Δ).dual) c' = 0) :
    stokesSum ρ Δ c c' = 0 :=
  gamma6_stokes_decomposed (permRep ρ Δ) c c' hz hz'
    (fun i => orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ)) (fun i j => eO Δ (lineSub i) j)
    (fun i j t v => eO_line_equivariant ρ Δ i j t v) (fun i v => eO_sum Δ (lineSub i) v)
    (fun i _ _ hjk v => eO_orth Δ (lineSub i) hjk v)
    (fun i => orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ)) (fun i j => eO Δ (planeSub i) j)
    (fun i j t v => eO_plane_equivariant ρ Δ i j t v) (fun i v => eO_sum Δ (planeSub i) v)
    (fun i _ _ hjk v => eO_orth Δ (planeSub i) hjk v)

end Faces

section Level

variable (M : ℕ) [NeZero M] {E : Type} [AddCommGroup E] [Module ℂ E] [Module ℚ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E)
  (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] [Module ℚ E] in
include hρ in
/-- The compatibility of the dual representations. -/
theorem hρ_dual : ∀ x : ↥(Δ6 M), ρM.dual (eΔ M x) = ρ.dual x.1 := fun x => by
  refine LinearMap.ext fun f => LinearMap.ext fun v => ?_
  change f (ρM (eΔ M x)⁻¹ v) = f (ρ x.1⁻¹ v)
  rw [← map_inv (eΔ M) x, hρ x⁻¹]
  rfl

/-- **The Stokes relation for the induced classes of level-`M` classes**: for `c₀ ∈ H²(Γ(M), E)` and `c₀' ∈ H²(Γ(M), E*)` with zero flag restrictions, and classes `c_V`, `c'_V` of the induced
modules `Fun(Γ(6)/Γ(M), E)`, `Fun(Γ(6)/Γ(M), E*)` with Shapiro coordinates (the transports of) `c₀`, `c₀'` (the dual one transported by `dualRepHom` to the dual of the induced module),
the sum over the faces and orbits of the diagonal face pairings vanishes. -/
theorem gamma6_stokes_ind_M [Fintype (↥(gammaN 6) ⧸ Δ6 M)] (c₀ : groupCohomology.H2 (Rep.of ρM)) (c₀' : groupCohomology.H2 (Rep.of ρM.dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN M g)) (Rep.of ρM) c₀ = 0)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN M g)) (Rep.of ρM.dual) c₀' = 0)
    (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀)
    (cVd : groupCohomology.H2 (Rep.of (permRep ρ.dual (Δ6 M))))
    (hcVd : PhiH ρ.dual (Δ6 M) cVd = transportΔ M ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) c₀') :
    stokesSum ρ (Δ6 M) cV (h2Hom (dualRepHom ρ (Δ6 M)) cVd) = 0 :=
  gamma6_stokes_ind ρ (Δ6 M) cV _ (res_flag_ind_zero M ρ ρM hρ c₀ hz cV hcV)
    (fun g => res_h2Hom_zero _ (dualRepHom ρ (Δ6 M)) cVd
      (res_flag_ind_zero M ρ.dual ρM.dual (hρ_dual M ρ ρM hρ) c₀' hz' cVd hcVd g))

end Level

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
