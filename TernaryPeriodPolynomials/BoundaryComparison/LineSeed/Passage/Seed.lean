module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Data
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Relative

@[expose] public section


/-!
# The seed classes of `Γ₂(N)`-cusp forms on the line group `Γ(N) ∩ Q(ℤ)` (Passage 2)

Line mirror of `SeedC3S4c.GammaNSeed` (without the edge computation).  For `f ∈ S_{n+3}(Γ₂(N))`, the zig-zag cochain of the line seed `σ_f` on
`gammaNQLineData N` is a 2-cocycle with values in `lineStdRep N n` (`lineNCocycle₂`), vanishing on pairs of radical elements (`lineNRel`); the same
for the antiholomorphic seed (`lineNConjRel`).  `complexifyQ` is the complexification `H²(Γ_Q, E_n)_ℝ → H²(Γ_Q, E_n)_ℂ` (identity on cocycles) and
`complexifyQ_cuspSeedClass` identifies the image of the de Rham class of the seed with the class of `lineNRel`.  `lineNSeedKerClass`,
`lineNSeedConjKerClass` are the classes in the kernel of the radical restriction.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep realDescent realDescent_apply)
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ)

theorem gammaNQLam_inl (r : RadicalLattice) : gammaNQLam N (gammaNQInl N r) = 1 := by
  apply Units.ext
  ext i j
  rw [gammaNQLam_entry]
  fin_cases i <;> fin_cases j <;> simp [gammaNQInl, radEltQ]

/-- The Levi block lies in `Λ = Γ₂(N)` (as the Levi group `leviGroup N` of the plane). -/
theorem gammaNQ_lam_mem_levi (g : ↥(gammaNQ N)) :
    ((gammaNQLineData N).lam g : GL (Fin 2) ℝ) ∈ leviGroup N :=
  ⟨(gammaNQProj N g), (gammaNQProj N g).2, rfl⟩

section Seed

variable {N} [NeZero N] {n : ℕ} (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the line seed of `f ∈ S_{n+3}(Γ₂(N))` on `Γ_Q = Γ(N) ∩ Q(ℤ)`. -/
def lineNChain (g k : ↥(gammaNQ N)) : Coef n :=
  cuspSeedCochain (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f) g k

omit [NeZero N] in
theorem lineNChain_inl_right (g : ↥(gammaNQ N)) (r : RadicalLattice) : lineNChain f g (gammaNQInl N r) = 0 := by
  apply Coef.toPoly_injective
  unfold lineNChain
  rw [toPoly_cuspSeedCochain]
  have h1 : (gammaNQLineData N).lam (gammaNQInl N r) = 1 := gammaNQLam_inl N r
  have h2 : mob ((gammaNQLineData N).lam (gammaNQInl N r)) Complex.I = Complex.I := by
    rw [h1]; simp [mob]
  rw [h2]
  simp [momentPrim_zero]

/-- The seed cochain with values in the carrier of `lineStdRep N n`. -/
def lineNChainR (g k : ↥(gammaNQ N)) : lineStdRep N n := lineNChain f g k

/-- The seed cochain as a complex 2-cocycle of `Γ(N) ∩ Q(ℤ)`. -/
def lineNCocycle₂ : cocycles₂ (lineStdRep N n) :=
  ⟨fun p => lineNChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedCochain_cocycle (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f) g h j
    change lineNChainR f (g * h) j + lineNChainR f g h =
      (lineStdRep N n).ρ g (lineNChainR f h j) + lineNChainR f g (h * j)
    have e2 : (lineStdRep N n).ρ g (lineNChainR f h j) =
        (gammaNQLineData N).rhoR n g (lineNChain f h j) := lineNRep_ρ_std N n g _
    rw [e2]
    exact e)⟩

/-- **The relative 2-cocycle of the line seed of `f ∈ S_{n+3}(Γ₂(N))`** on `Γ(N) ∩ Q(ℤ)` (radical `Nℤ²`). -/
def lineNRel : relativeTwoCocycles (lineExt N).inl (lineStdRep N n) :=
  ⟨lineNCocycle₂ f, fun _ r' => lineNChain_inl_right f _ r'⟩

/-! ### The antiholomorphic seed -/

/-- The zig-zag cochain of the antiholomorphic line seed on `Γ(N) ∩ Q(ℤ)`. -/
def lineNConjChain (g k : ↥(gammaNQ N)) : Coef n :=
  cuspSeedConjCochain (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f) g k

omit [NeZero N] in
theorem lineNConjChain_eq (g k : ↥(gammaNQ N)) : lineNConjChain f g k = Coef.conjCoef (lineNChain f g k) :=
  cuspSeedConjCochain_eq (gammaNQLineData N) (gammaNQ_lam_mem_levi N) g k

/-- The antiholomorphic seed cochain with values in the carrier of `lineStdRep N n`. -/
def lineNConjChainR (g k : ↥(gammaNQ N)) : lineStdRep N n := lineNConjChain f g k

/-- The antiholomorphic seed cochain as a complex 2-cocycle. -/
def lineNConjCocycle₂ : cocycles₂ (lineStdRep N n) :=
  ⟨fun p => lineNConjChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedConjCochain_cocycle (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f) g h j
    change lineNConjChainR f (g * h) j + lineNConjChainR f g h =
      (lineStdRep N n).ρ g (lineNConjChainR f h j) + lineNConjChainR f g (h * j)
    have e2 : (lineStdRep N n).ρ g (lineNConjChainR f h j) =
        (gammaNQLineData N).rhoR n g (lineNConjChain f h j) := lineNRep_ρ_std N n g _
    rw [e2]
    exact e)⟩

omit [NeZero N] in
theorem lineNConjChain_inl_right (g : ↥(gammaNQ N)) (r : RadicalLattice) :
    lineNConjChain f g (gammaNQInl N r) = 0 := by
  rw [lineNConjChain_eq, lineNChain_inl_right]
  apply Coef.toPoly_injective
  simp

/-- The relative 2-cocycle of the antiholomorphic line seed on `Γ(N) ∩ Q(ℤ)`. -/
def lineNConjRel : relativeTwoCocycles (lineExt N).inl (lineStdRep N n) :=
  ⟨lineNConjCocycle₂ f, fun _ r' => lineNConjChain_inl_right f _ r'⟩

end Seed

/-! ### Complexification and the kernel classes -/

section Complex

variable (n : ℕ)

/-- Coefficients, real carrier to complex carrier (the identity). -/
def cxVecQ (x : Rep.of ((gammaNQLineData N).rhoR n)) : lineStdRep N n := x

/-- Real 2-cocycles of `Γ_Q` with values in `E_n` are complex 2-cocycles. -/
def cxCocyclesQ :
    cocycles₂ (Rep.of ((gammaNQLineData N).rhoR n)) →ₗ[ℝ] cocycles₂ (lineStdRep N n) where
  toFun c := ⟨fun p => cxVecQ N n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    change cxVecQ N n (c.1 (g * h, j)) + cxVecQ N n (c.1 (g, h)) =
      (lineStdRep N n).ρ g (cxVecQ N n (c.1 (h, j))) + cxVecQ N n (c.1 (g, h * j))
    have e2 : (lineStdRep N n).ρ g (cxVecQ N n (c.1 (h, j))) =
        cxVecQ N n ((gammaNQLineData N).rhoR n g (c.1 (h, j))) := lineNRep_ρ_std N n g _
    rw [e2]
    exact e)⟩
  map_add' a b := by
    apply Subtype.ext
    funext p
    exact rfl
  map_smul' r a := by
    apply Subtype.ext
    funext p
    exact rfl

/-- The complexification map `H²(Γ_Q, E_n)_ℝ → H²(Γ_Q, E_n)_ℂ`, the identity on cocycles. -/
def complexifyQ : H2 (Rep.of ((gammaNQLineData N).rhoR n)) →ₗ[ℝ] H2 (lineStdRep N n) :=
  realDescent (H2π (Rep.of ((gammaNQLineData N).rhoR n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (lineStdRep N n)).hom.restrictScalars ℝ).comp (cxCocyclesQ N n))
    (fun a b hab => by
      have h : H2π (Rep.of ((gammaNQLineData N).rhoR n)) a = H2π (Rep.of ((gammaNQLineData N).rhoR n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (lineStdRep N n) (cxCocyclesQ N n a) = H2π (lineStdRep N n) (cxCocyclesQ N n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVecQ N n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      change (lineStdRep N n).ρ p.1 (cxVecQ N n (y p.2)) - cxVecQ N n (y (p.1 * p.2)) +
          cxVecQ N n (y p.1) = cxVecQ N n (a.1 p) - cxVecQ N n (b.1 p)
      have e2 : (lineStdRep N n).ρ p.1 (cxVecQ N n (y p.2)) =
          cxVecQ N n ((gammaNQLineData N).rhoR n p.1 (y p.2)) := lineNRep_ρ_std N n p.1 _
      rw [e2]
      exact hp)

theorem complexifyQ_H2π (c : cocycles₂ (Rep.of ((gammaNQLineData N).rhoR n))) :
    complexifyQ N n (H2π (Rep.of ((gammaNQLineData N).rhoR n)) c) =
      H2π (lineStdRep N n) (cxCocyclesQ N n c) :=
  realDescent_apply _ _ _ _ c

variable {N n} [NeZero N] (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The complexification of the de Rham class of the line seed is the class of `lineNRel`. -/
theorem complexifyQ_cuspSeedClass :
    complexifyQ N n (cuspSeedClass (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f)) =
      (relativeTwoCocycleClass (lineExt N).inl (lineStdRep N n) (lineNRel f)).val := by
  change complexifyQ N n (H2π (Rep.of ((gammaNQLineData N).rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (lineStdRep N n) (lineNCocycle₂ f)
  rw [complexifyQ_H2π]
  rfl

/-- The complexification of the de Rham class of the antiholomorphic line seed is the class of `lineNConjRel`. -/
theorem complexifyQ_cuspSeedConjClass :
    complexifyQ N n (cuspSeedConjClass (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := f)) =
      (relativeTwoCocycleClass (lineExt N).inl (lineStdRep N n) (lineNConjRel f)).val := by
  change complexifyQ N n (H2π (Rep.of ((gammaNQLineData N).rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (lineStdRep N n) (lineNConjCocycle₂ f)
  rw [complexifyQ_H2π]
  rfl

end Complex

section Ker

variable {N} [NeZero N] {n : ℕ}

/-- The class of the line seed of `f` in the kernel of the radical restriction at `Γ_Q`. -/
def lineNSeedKerClass (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (lineExt N).inl (lineStdRep N n)).ker :=
  relativeTwoCocycleClass (lineExt N).inl (lineStdRep N n) (lineNRel f)

/-- The class of the antiholomorphic line seed of `f` in the kernel of the radical restriction at `Γ_Q`. -/
def lineNSeedConjKerClass (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (lineExt N).inl (lineStdRep N n)).ker :=
  relativeTwoCocycleClass (lineExt N).inl (lineStdRep N n) (lineNConjRel f)

end Ker

end TernaryPeriodPolynomials.Argument.LineSeed
