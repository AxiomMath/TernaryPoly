module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspRowsCross
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GramBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NPlaneValues
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NLinear

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# The dual cusp values, linearity and seed spanning for the dual series (complex coefficients)

Formalized by Claude Sonnet 5.5.

The complex `ȷ`-transport of the `CuspValues` (the exact restrictions of the classical series to the plane cusps):

* `jPullC`, `resToC`, `jPullC_res`: the complex `ȷ`-pullback `H²(Γ(N), E_ℂ) → H²(Γ(N), E^∨_ℂ)` and the complex restriction, with the transport
  `r_S (ȷ^* c) = ȷ^* (r_{S'} c)` (`resToC S hS (dualRhoC) (jPullC c) = facePullC … (resToC S' hS' gammaRhoC c)`);
* `dualClassC N n f hn b h`: the complexified dual series `ℰ_Q^∨` at the line cusp `h⁻¹Qh`, seed type `b`; `dualSeedC N n f b h`: the dual seed class at the line cusp
  `h` (`ȷ^*` of the `faceSeedKerClass` / `faceSeedConjKerClass` at the plane cusp `ȷ(h)`);
* `dualClassC_add/_smul`, `dualSeedC_add/_smul`: additivity and (twisted) homogeneity in the cusp form (S6/the `classCG_term_add/_smul`, `faceSeedKerClass_add/_smul` transported);
* `dualSeedLitC` (+ `_add/_smul`), `mem_dualCuspidalQLiteral_iff_seeds`: the same for the literal contragredient `E*` (`toLiteral`);
* `DualCuspValues`, `dualCuspValues`: for `3 ≤ N`, `4 ≤ n` the exact line restrictions of the dual series at every pair of cusps: in the dual seed span, zero for
  different orbits (`ȷ(h')ȷ(h)⁻¹` has no cell), and the dual seed class for the same cusp, both seeds;
* `dualCuspidalQ_eq_seeds`: Eichler-Shimura spanning for the dual coefficients: every class of `𝒞_Q(E^∨)` at the line cusp `h` is a sum of a holomorphic and an antiholomorphic dual seed
  class, and conversely.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

section Generic

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
  {K K' G G' : Type} [Group K] [Group K'] [Group G] [Group G']

/-- **Restriction commutes with pullback along a group homomorphism**, over an arbitrary field (the proof of `restrict_pullback`). -/
theorem restrict_pullbackK (β : K →* G) (α : G →* G') (α' : K →* K') (β' : K' →* G')
    (hcomm : ∀ k, α (β k) = β' (α' k))
    (ρG : Representation k G V) (ρG' : Representation k G' V) (hG : ∀ g, ρG g = ρG' (α g))
    (ρK : Representation k K V) (hK : ∀ k, ρK k = ρG (β k))
    (ρK' : Representation k K' V) (hK' : ∀ k, ρK' k = ρG' (β' k))
    (hKK : ∀ k, ρK k = ρK' (α' k))
    (x : groupCohomology.H2 (Rep.of ρG')) :
    (groupCohomology.map β (resMorK β ρK ρG hK) 2).hom
        ((groupCohomology.map α (resMorK α ρG ρG' hG) 2).hom x) =
      (groupCohomology.map α' (resMorK α' ρK ρK' hKK) 2).hom
        ((groupCohomology.map β' (resMorK β' ρK' ρG' hK') 2).hom x) := by
  have h1 := groupCohomology.map_comp α β (resMorK α ρG ρG' hG) (resMorK β ρK ρG hK) 2
  have h2 := groupCohomology.map_comp β' α' (resMorK β' ρK' ρG' hK') (resMorK α' ρK ρK' hKK) 2
  have h3 : groupCohomology.map (α.comp β) ((Rep.resFunctor β).map (resMorK α ρG ρG' hG) ≫
      resMorK β ρK ρG hK) 2 =
    groupCohomology.map (β'.comp α') ((Rep.resFunctor α').map (resMorK β' ρK' ρG' hK') ≫
      resMorK α' ρK ρK' hKK) 2 := by
    apply groupCohomology.map_congr (MonoidHom.ext hcomm)
    rfl
  have h4 := congrArg (fun m => m.hom x) (h1.symm.trans (h3.trans h2))
  exact h4

end Generic


section Complex

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

variable (N : ℕ) (n : ℕ)

/-- The complex `ȷ`-pullback `H²(Γ(N), E) → H²(Γ(N), E^∨)`. -/
def jPullC : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n)) →ₗ[ℂ] groupCohomology.H2 (Rep.of (dualRhoC N n)) :=
  (groupCohomology.map (jN N) (resMorK (jN N) (dualRhoC N n) (gammaRhoC (gammaN N) n) (fun _ => rfl)) 2).hom

/-- The complex group restriction to a subgroup `S ≤ Γ(N)`. -/
def resToC {ρ : Representation ℂ (gammaN N) (GeneralEisenstein.HomogeneousPoly n)} (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) :
    groupCohomology.H2 (Rep.of ρ) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion hS))) :=
  (groupCohomology.map (Subgroup.inclusion hS) (resMorK (Subgroup.inclusion hS) (ρ.comp (Subgroup.inclusion hS)) ρ (fun _ => rfl)) 2).hom

/-- **Transport of complex restrictions along `ȷ`.** -/
theorem jPullC_res {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (c' : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n))) :
    resToC N n (ρ := dualRhoC N n) S hS (jPullC N n c') =
      facePullC hS hS' hSS' n (resToC N n (ρ := gammaRhoC (gammaN N) n) S' hS' c') :=
  restrict_pullbackK (Subgroup.inclusion hS) (jN N) (jRestr S S' hSS') (Subgroup.inclusion hS')
    (jRestr_comm (gammaN N) (gammaN N) (jN N) (fun _ => rfl) S S' hS hS' hSS') (dualRhoC N n) (gammaRhoC (gammaN N) n)
    (fun _ => rfl) ((dualRhoC N n).comp (Subgroup.inclusion hS)) (fun _ => rfl)
    ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS')) (fun _ => rfl) (facePullC_compat hS hS' hSS') c'

/-- The complexification of the `ȷ`-pullback is the `ȷ`-pullback of the complexification. -/
theorem cxGen_jPull (x : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (jPull N n x) =
      jPullC N n (cxGen (gammaRho (gammaN N) n) (gammaRhoC (gammaN N) n) (fun _ _ => rfl) x) :=
  cxGen_map _ _ (fun _ _ => rfl) _ _ (fun _ _ => rfl) (jN N) (fun _ => rfl) (fun _ => rfl) x

end Complex


section Values

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The complexified dual series `ℰ_Q^∨` at the line cusp `h⁻¹Qh`** for the seed of type `b`: `ȷ^*` of the complexified series at the plane cusp `ȷ(h)`. -/
def dualClassC (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of (dualRhoC N n)) :=
  jPullC N n (EisensteinClass.complexify (gammaN N) n
    (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (jmath h) b hn))

/-- It is the complexification of the real dual series class `dualSeriesAtClass_gammaN`. -/
theorem dualClassC_eq_cxGen (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) :
    dualClassC N n f hn b h =
      cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (dualSeriesAtClass_gammaN N n f hn b h) := by
  rw [dualSeriesAtClass_gammaN_eq, cxGen_jPull, cxGen_eq_complexify]
  rfl

/-- The dual holomorphic seed class at the line cusp `h⁻¹Qh`: `ȷ^*` of S4c's seed class at the plane cusp `ȷ(h)`. -/
def dualSeedHolC (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) :=
  facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n
    (faceSeedKerClass N (jmath h) n f).1

/-- The dual antiholomorphic seed class at the line cusp `h⁻¹Qh`. -/
def dualSeedConjC (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) :=
  facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n
    (faceSeedConjKerClass N (jmath h) n f).1

/-- The dual seed class for the seed of type `b`. -/
def dualSeedC (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) :=
  if b then dualSeedConjC N n f h else dualSeedHolC N n f h

/-- **The dual series at its own line cusp restricts to the dual seed (holomorphic seed)** (complex coefficients; `3 ≤ N`, `4 ≤ n`). -/
theorem dualClassC_self_hol (hN : 3 ≤ N) (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n f hn false h) =
      dualSeedHolC N n f h := by
  unfold dualClassC
  rw [jPullC_res N n (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h)]
  exact congrArg _ ((TernaryPeriodPolynomials.Argument.FormClassK.cuspValues N n hN hn).self_hol f (jmath h))


/-- **The same for the antiholomorphic seed.** -/
theorem dualClassC_self_conj (hN : 3 ≤ N) (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n f hn true h) =
      dualSeedConjC N n f h := by
  unfold dualClassC
  rw [jPullC_res N n (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h)]
  exact congrArg _ ((TernaryPeriodPolynomials.Argument.FormClassK.cuspValues N n hN hn).self_conj f (jmath h))

theorem dualClassC_self (hN : 3 ≤ N) (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (h : SL(3, ℤ)) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n f hn b h) =
      dualSeedC N n f b h := by
  cases b
  · exact dualClassC_self_hol N n hN hn f h
  · exact dualClassC_self_conj N n hN hn f h

/-- **Different orbits: the dual series at the line cusp `h'` has zero line restriction at `h`** (no cell for `ȷ(h')ȷ(h)⁻¹`). -/
theorem dualClassC_none (hN : 3 ≤ N) (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (h h' : SL(3, ℤ))
    (hnone : ∀ c : Ck N (jmath h' * (jmath h)⁻¹), ¬ IsCellK N (jmath h' * (jmath h)⁻¹) c) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n f hn b h') = 0 := by
  unfold dualClassC
  rw [jPullC_res N n (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h)]
  have := (TernaryPeriodPolynomials.Argument.FormClassK.cuspValues N n hN hn).none f (jmath h) (jmath h') b hnone
  change facePullC _ _ _ n (TernaryPeriodPolynomials.Argument.FormClassK.resAtC N (jmath h) n _) = 0
  rw [this]
  exact map_zero _

/-- The span of the dual seed classes (holomorphic and antiholomorphic) at the line cusp `h⁻¹Qh`: the image of the plane seed span at `ȷ(h)` under `ȷ^*`. -/
def dualSeedSpan (h : SL(3, ℤ)) :
    Submodule ℂ (groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :=
  Submodule.map (facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n) (faceSeedSpan N (jmath h) n)

/-- **The line restriction of the dual series at ANY cusp lies in the dual seed span.** -/
theorem dualClassC_mem (hN : 3 ≤ N) (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (h h' : SL(3, ℤ)) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n f hn b h') ∈ dualSeedSpan N n h := by
  unfold dualClassC
  rw [jPullC_res N n (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h)]
  exact Submodule.mem_map_of_mem ((TernaryPeriodPolynomials.Argument.FormClassK.cuspValues N n hN hn).mem f (jmath h) (jmath h') b)


/-! ### Linearity in the cusp form -/

/-- **The dual series class is additive in the cusp form** (at every line cusp and seed type). -/
theorem dualClassC_add (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualClassC N n (f + g) hn b h = dualClassC N n f hn b h + dualClassC N n g hn b h := by
  unfold dualClassC
  have e : EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f + g) (jmath h) b hn) =
      EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (jmath h) b hn) +
      EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g (jmath h) b hn) :=
    Statements.EisensteinClass.eisensteinAtClassC_add (gammaN N) n (leviGroup N) b (CuspData.ofSL (jmath h)) hn
      (leviInCusp_gammaN N _) f g
  rw [e]
  exact map_add _ _ _

/-- **The dual series class is homogeneous for the twisted scalar action** (`cx b a`: conjugate-linear on the antiholomorphic seed). -/
theorem dualClassC_smul (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualClassC N n (a • f) hn b h = cx b a • dualClassC N n f hn b h := by
  unfold dualClassC
  have e : EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (a • f) (jmath h) b hn) =
      cx b a • EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (jmath h) b hn) :=
    Statements.EisensteinClass.eisensteinAtClassC_cmul (gammaN N) n (leviGroup N) b (CuspData.ofSL (jmath h)) hn
      (leviInCusp_gammaN N _) a f
  rw [e]
  exact map_smul _ _ _

theorem dualSeedHolC_add (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedHolC N n (f + g) h = dualSeedHolC N n f h + dualSeedHolC N n g h := by
  unfold dualSeedHolC
  rw [TernaryPeriodPolynomials.Argument.FormClassK.faceSeedKerClass_add, Submodule.coe_add]
  exact map_add _ _ _

theorem dualSeedHolC_smul (h : SL(3, ℤ)) (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedHolC N n (a • f) h = a • dualSeedHolC N n f h := by
  unfold dualSeedHolC
  rw [TernaryPeriodPolynomials.Argument.FormClassK.faceSeedKerClass_smul, Submodule.coe_smul]
  exact map_smul _ _ _

theorem dualSeedConjC_add (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedConjC N n (f + g) h = dualSeedConjC N n f h + dualSeedConjC N n g h := by
  unfold dualSeedConjC
  rw [TernaryPeriodPolynomials.Argument.FormClassK.faceSeedConjKerClass_add, Submodule.coe_add]
  exact map_add _ _ _

theorem dualSeedConjC_smul (h : SL(3, ℤ)) (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedConjC N n (a • f) h = (starRingEnd ℂ a) • dualSeedConjC N n f h := by
  unfold dualSeedConjC
  rw [TernaryPeriodPolynomials.Argument.FormClassK.faceSeedConjKerClass_smul, Submodule.coe_smul]
  exact map_smul _ _ _

theorem dualSeedC_add (b : Bool) (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedC N n (f + g) b h = dualSeedC N n f b h + dualSeedC N n g b h := by
  cases b
  · exact dualSeedHolC_add N n h f g
  · exact dualSeedConjC_add N n h f g

theorem dualSeedC_smul (b : Bool) (h : SL(3, ℤ)) (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedC N n (a • f) b h = cx b a • dualSeedC N n f b h := by
  cases b
  · exact dualSeedHolC_smul N n h a f
  · exact dualSeedConjC_smul N n h a f

/-! ### Eichler-Shimura spanning for the dual coefficients -/

/-- **Every class of `𝒞_Q(E^∨)` at the line cusp `h` is the sum of a holomorphic and an antiholomorphic dual seed class, and conversely**
(the `ȷ`-transport of S7's `exists_seed_sum`, Eichler-Shimura spanning for `Γ(N)`, unconditional). -/
theorem mem_dualCuspidalQ_iff_seeds (h : SL(3, ℤ))
    (η : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :
    η ∈ dualCuspidalQ N n h ↔
      ∃ f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), η = dualSeedHolC N n f h + dualSeedConjC N n g h := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨f, g, hfg⟩ := TernaryPeriodPolynomials.Argument.FormClassK.exists_seed_sum N n (jmath h) y hy
    refine ⟨f, g, ?_⟩
    rw [hfg]
    exact map_add _ _ _
  · rintro ⟨f, g, rfl⟩
    have hES := Statements.EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N))
    unfold dualCuspidalQ
    rw [← faceSeedSpan_eq_cuspidalInH2 N (jmath h) n hES]
    have h1 : (faceSeedKerClass N (jmath h) n f).1 ∈ faceSeedSpan N (jmath h) n :=
      ⟨_, Submodule.subset_span (Or.inl ⟨f, rfl⟩), rfl⟩
    have h2 : (faceSeedConjKerClass N (jmath h) n g).1 ∈ faceSeedSpan N (jmath h) n :=
      ⟨_, Submodule.subset_span (Or.inr ⟨g, rfl⟩), rfl⟩
    refine ⟨_, Submodule.add_mem _ h1 h2, ?_⟩
    exact map_add _ _ _

/-- The dual seed span is the mixed cuspidal group `𝒞_Q(E^∨)`. -/
theorem dualSeedSpan_eq_dualCuspidalQ (h : SL(3, ℤ)) : dualSeedSpan N n h = dualCuspidalQ N n h := by
  have hES := Statements.EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold dualSeedSpan dualCuspidalQ
  rw [faceSeedSpan_eq_cuspidalInH2 N (jmath h) n hES]


/-! ### The dual cusp values (mirror of S7's `CuspValues`) and the literal contragredient -/

/-- **The exact line restrictions of the dual series at every pair of line cusps** (mirror of `FormClassK.CuspValues`): in the dual seed span,
zero for different orbits, and the dual seed class for the same cusp, both seeds. -/
structure DualCuspValues (hn : 4 ≤ n) : Prop where
  mem : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool),
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n g hn b h') ∈ dualSeedSpan N n h
  none : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h h' : SL(3, ℤ)) (b : Bool),
    (∀ c : Ck N (jmath h' * (jmath h)⁻¹), ¬ IsCellK N (jmath h' * (jmath h)⁻¹) c) →
      resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n g hn b h') = 0
  self_hol : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)),
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n g hn false h) = dualSeedHolC N n g h
  self_conj : ∀ (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)),
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (dualClassC N n g hn true h) = dualSeedConjC N n g h

/-- **The dual cusp values hold unconditionally** (`3 ≤ N`, `4 ≤ n`): the `ȷ`-transport of `TernaryPeriodPolynomials.Argument.FormClassK.cuspValues`. -/
theorem dualCuspValues (hN : 3 ≤ N) (hn : 4 ≤ n) : DualCuspValues N n hn where
  mem g h h' b := dualClassC_mem N n hN hn g b h h'
  none g h h' b hnone := dualClassC_none N n hN hn g b h h' hnone
  self_hol g h := dualClassC_self_hol N n hN hn g h
  self_conj g h := dualClassC_self_conj N n hN hn g h

/-- The literal-contragredient dual seed classes: `dualIso` on `H²` of the line group `Γ_{h⁻¹Qh}`. -/
def dualSeedLitC (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) :=
  toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n (dualSeedC N n f b h)

theorem dualSeedLitC_add (b : Bool) (h : SL(3, ℤ)) (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedLitC N n (f + g) b h = dualSeedLitC N n f b h + dualSeedLitC N n g b h := by
  unfold dualSeedLitC
  rw [dualSeedC_add]
  exact map_add _ _ _

theorem dualSeedLitC_smul (b : Bool) (h : SL(3, ℤ)) (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    dualSeedLitC N n (a • f) b h = cx b a • dualSeedLitC N n f b h := by
  unfold dualSeedLitC
  rw [dualSeedC_smul]
  exact map_smul _ _ _

/-- **Spanning for the literal contragredient**: `𝒞_Q(E*)` at the line cusp `h` is exactly the sums of a holomorphic and an antiholomorphic literal dual seed class. -/
theorem mem_dualCuspidalQLiteral_iff_seeds (h : SL(3, ℤ))
    (η : groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :
    η ∈ dualCuspidalQLiteral N n h ↔
      ∃ f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), η = dualSeedLitC N n f false h + dualSeedLitC N n g true h := by
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    obtain ⟨f, g, hfg⟩ := (mem_dualCuspidalQ_iff_seeds N n h ξ).1 hξ
    refine ⟨f, g, ?_⟩
    rw [hfg]
    exact map_add _ _ _
  · rintro ⟨f, g, rfl⟩
    refine ⟨dualSeedHolC N n f h + dualSeedConjC N n g h, (mem_dualCuspidalQ_iff_seeds N n h _).2 ⟨f, g, rfl⟩, ?_⟩
    exact map_add _ _ _

end Values

end TernaryPeriodPolynomials.Argument.EisensteinDual
