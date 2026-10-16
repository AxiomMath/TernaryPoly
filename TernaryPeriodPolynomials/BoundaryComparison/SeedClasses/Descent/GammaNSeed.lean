module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNScale
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.SpanEq

@[expose] public section


/-!
# The seeds on the paper's plane group `Γ(N) ∩ P(ℤ)` (radical `Nℤ²`)

Paper: Lemma C.3
(`ar:lem:seed`).

The holomorphic and antiholomorphic seeds of `f ∈ S_{n+3}(Γ₂(N))` as relative 2-cocycles of the
split extension `gammaNExt N` (radical `Nℤ²`), with values in `gammaNRep N n`. Their
Hochschild--Serre edges are, in the binary coordinates of `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)`,
`(n+1)⁻¹` times the classes of the period cocycles (`gammaNSeedEdge`, `gammaNSeedConjEdge`): the
conjugation `T = ρ(diag(1,1,N))` carries the edge cocycles to those of `ℤ² ⋊ Γ₂(N)`. Spanning is
conditional on `ESSpan (Γ(N)) n` (`gammaN_seed_span_conditional`); edge injectivity is
unconditional (`gammaNEdge_injective_binary`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open groupCohomology

section Lemmas

variable {N : ℕ}

theorem gammaN_lamM (g : ↥(gammaNP N)) :
    (gammaNPlaneData N).lamM g = blockA (realMat g.1) := by
  show blockA ((((gammaNSigma N) g : GL (Fin 3) ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) = _
  rw [gammaNSigma_val]

theorem gammaN_w (g : ↥(gammaNP N)) : (gammaNPlaneData N).w g = blockW (realMat g.1) := by
  show blockW ((((gammaNSigma N) g : GL (Fin 3) ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) = _
  rw [gammaNSigma_val]

theorem gammaN_lamM_inl (r : RadicalLattice) :
    (gammaNPlaneData N).lamM (gammaNInl N r) = 1 := by
  rw [gammaN_lamM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaNInl, blockA, realMat, radElt]

theorem gammaN_w_inl (r : RadicalLattice) : (gammaNPlaneData N).w (gammaNInl N r) =
    ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))] := by
  rw [gammaN_w]
  funext i
  fin_cases i <;> simp [gammaNInl, blockW, realMat, radElt]

theorem gammaN_lamM_sect (A : ↥(CongruenceSubgroup.Gamma N)) :
    (gammaNPlaneData N).lamM (gammaNSect N A) =
      ((SpecialLinearGroup.mapGL ℝ A.1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [gammaN_lamM, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaNSect, blockA, realMat, ConvergenceC4.blockDiag,
      Matrix.SpecialLinearGroup.map_apply_coe]

theorem gammaN_w_sect (A : ↥(CongruenceSubgroup.Gamma N)) :
    (gammaNPlaneData N).w (gammaNSect N A) = 0 := by
  rw [gammaN_w]
  funext i
  fin_cases i <;> simp [gammaNSect, blockW, realMat, ConvergenceC4.blockDiag]

theorem gammaN_lam_inl (r : RadicalLattice) : (gammaNPlaneData N).lam (gammaNInl N r) = 1 := by
  apply Units.ext
  exact gammaN_lamM_inl r

theorem gammaN_lam_sect (A : ↥(CongruenceSubgroup.Gamma N)) :
    (gammaNPlaneData N).lam (gammaNSect N A) = SpecialLinearGroup.mapGL ℝ A.1 := by
  apply Units.ext
  exact gammaN_lamM_sect A

theorem gammaNRep_ρ [NeZero N] (n : ℕ) (g : ↥(gammaNP N)) (x : Coef n) :
    (gammaNRep N n).ρ g x = (gammaNPlaneData N).rhoR n g x := rfl

end Lemmas

section Seed

variable {N : ℕ} [NeZero N] {n : ℕ}
  (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the seed of `f ∈ S_{n+3}(Γ₂(N))` on `Γ_P = Γ(N) ∩ P(ℤ)`. -/
def gammaNChain (g k : ↥(gammaNP N)) : Coef n :=
  cuspSeedCochain (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) g k

/-- The Eichler cocycle of the moment primitives at the Levi block of `k`. -/
def gammaNEps (k : ↥(gammaNP N)) : MvPolynomial (Fin 3) ℂ :=
  rename Fin.castSucc
    (eichlerCocycle n (momentPrim (LamGL (CongruenceSubgroup.Gamma N)) n f)
      ((gammaNPlaneData N).lam k))

omit [NeZero N] in
theorem toPoly_gammaNChain (g k : ↥(gammaNP N)) :
    Coef.toPoly (gammaNChain f g k) =
      C (((n : ℂ) + 1)⁻¹) *
        ddiv (rho ((gammaNPlaneData N).plm g) (gammaNEps f k) -
          rho (parabolicMatrix ((gammaNPlaneData N).lamM g) 0) (gammaNEps f k)) :=
  toPoly_cuspSeedCochain (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) g k

omit [NeZero N] in
theorem gammaNEps_inl (r : RadicalLattice) : gammaNEps f (gammaNInl N r) = 0 := by
  have h1 : (gammaNPlaneData N).lam (gammaNInl N r) = 1 := gammaN_lam_inl r
  have h2 : mob ((gammaNPlaneData N).lam (gammaNInl N r)) Complex.I = Complex.I := by
    rw [h1]; simp [mob]
  unfold gammaNEps
  rw [eichlerCocycle, h2, eichlerPoly_base n _ (momentPrim_zero _ n f), map_zero]

omit [NeZero N] in
theorem gammaNChain_inl_inl (r r' : RadicalLattice) :
    gammaNChain f (gammaNInl N r) (gammaNInl N r') = 0 := by
  apply Coef.toPoly_injective
  rw [toPoly_gammaNChain, gammaNEps_inl]
  simp [rho, ddiv_zero]


/-- The seed cochain with values in the carrier of `gammaNRep N n`. -/
def gammaNChainR (g k : ↥(gammaNP N)) : gammaNRep N n := gammaNChain f g k

/-- The seed cochain as a complex 2-cocycle of `Γ(N) ∩ P(ℤ)`. -/
def gammaNCocycle₂ : cocycles₂ (gammaNRep N n) :=
  ⟨fun p => gammaNChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedCochain_cocycle (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
      (f := f) g h j
    change gammaNChainR f (g * h) j + gammaNChainR f g h =
      (gammaNRep N n).ρ g (gammaNChainR f h j) + gammaNChainR f g (h * j)
    have e2 : (gammaNRep N n).ρ g (gammaNChainR f h j) =
        (gammaNPlaneData N).rhoR n g (gammaNChain f h j) := rfl
    rw [e2]
    exact e)⟩

/-- **The relative 2-cocycle of the seed of `f ∈ S_{n+3}(Γ₂(N))`** on the paper's plane group
`Γ(N) ∩ P(ℤ)` with radical `Nℤ²`. -/
def gammaNRel : relativeTwoCocycles (gammaNExt N).inl (gammaNRep N n) :=
  ⟨gammaNCocycle₂ f, fun r r' => gammaNChain_inl_inl f r r'⟩

omit [NeZero N] in
theorem toPoly_gammaNChain_sect (A : ↥(CongruenceSubgroup.Gamma N)) (k : ↥(gammaNP N)) :
    Coef.toPoly (gammaNChain f (gammaNSect N A) k) = 0 := by
  rw [toPoly_gammaNChain]
  have hw : (gammaNPlaneData N).plm (gammaNSect N A) =
      parabolicMatrix ((gammaNPlaneData N).lamM (gammaNSect N A)) 0 := by
    rw [PlaneData.plm_eq, gammaN_w_sect]
  rw [hw, sub_self, ddiv_zero, mul_zero]

omit [NeZero N] in
theorem toPoly_gammaNChain_inl (r : RadicalLattice) (k : ↥(gammaNP N)) :
    Coef.toPoly (gammaNChain f (gammaNInl N r) k) = C (((n : ℂ) + 1)⁻¹) *
      ddiv (bind₁ (shiftSub ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))])
        (gammaNEps f k) - gammaNEps f k) := by
  rw [toPoly_gammaNChain]
  have hp : (gammaNPlaneData N).plm (gammaNInl N r) = parabolicMatrix 1
      ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))] := by
    rw [PlaneData.plm_eq, gammaN_lamM_inl, gammaN_w_inl]
  rw [hp, gammaN_lamM_inl, rho_par_one, rho_par_zero]

/-- The mixed part of the seed cocycle, with values in `E_n`. -/
def gammaNEdgeVal (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) : Coef n :=
  splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNRel f) r

omit [NeZero N] in
theorem gammaNEps_sect (A : ↥(CongruenceSubgroup.Gamma N)) :
    gammaNEps f (gammaNSect N A) = binaryPolynomialLift (eichlerForm f A.1).val := by
  unfold gammaNEps
  rw [gammaN_lam_sect]
  rfl

theorem toPoly_gammaNEdgeVal (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) :
    Coef.toPoly (gammaNEdgeVal f A r) =
      -(C (((n : ℂ) + 1)⁻¹) *
        ddiv (bind₁ (shiftSub ![((N : ℝ) * (r.toAdd.1 : ℝ)), ((N : ℝ) * (r.toAdd.2 : ℝ))])
          (binaryPolynomialLift (eichlerForm f A.1).val) -
            binaryPolynomialLift (eichlerForm f A.1).val)) := by
  rw [← gammaNEps_sect, ← toPoly_gammaNChain_inl]
  change Coef.toPoly (gammaNChain f (gammaNSect N A)
    (gammaNInl N (splitRadicalInput (gammaNSplitting N) A r)) -
    gammaNChain f (gammaNInl N r) (gammaNSect N A)) = _
  rw [Coef.toPoly_sub, toPoly_gammaNChain_sect, zero_sub]



/-- The edge cocycle is carried by `T` to the edge cocycle of `ℤ² ⋊ Γ₂(N)`. -/
theorem tOp_gammaNEdgeVal (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) :
    tOp N n (gammaNEdgeVal f A r) = levelEdgeVal f A r := by
  apply Coef.toPoly_injective
  have h1 := tOp_coe N n (show HomogeneousPoly n from gammaNEdgeVal f A r)
  have h2 := toPoly_gammaNEdgeVal f A r
  have h3 := toPoly_levelEdgeVal f A r
  rw [levelEps_section] at h3
  have h4 := tOp_edgePoly N (((n : ℂ) + 1)⁻¹) (eichlerForm f A.1) r
  change ((tOp N n (show HomogeneousPoly n from gammaNEdgeVal f A r) : HomogeneousPoly n) :
    MvPolynomial (Fin 3) ℂ) = Coef.toPoly (levelEdgeVal f A r)
  rw [h1, h3]
  change C ((N : ℂ)⁻¹) * sc ((N : ℂ)⁻¹) (Coef.toPoly (gammaNEdgeVal f A r)) = _
  rw [h2]
  exact h4


theorem gammaNEdgeCyc_pull (A : ↥(CongruenceSubgroup.Gamma N)) :
    oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
        (tOp N n) (tOp_rad_intertwines N n)
        (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNRel f)) =
      levelEdgeCyc f A := by
  apply groupCohomology.cocycles₁_ext
  intro r
  exact tOp_gammaNEdgeVal f A r

/-- **The edge of the seed of `f ∈ S_{n+3}(Γ₂(N))` on the paper's plane group
`Γ(N) ∩ P(ℤ)`** (radical `Nℤ²`), in the binary coordinates of `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)`, is
`(n+1)⁻¹` times the class of the holomorphic period cocycle. -/
theorem gammaNSeedEdge :
    gammaNEdge N n (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNRel f)) =
      (((n : ℂ) + 1)⁻¹) • H1π (binRep (CongruenceSubgroup.Gamma N) n) (holCocycle f) := by
  have h1 : splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNRel f)) =
      H1π (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n))
        (splitCocycleEdge (gammaNSplitting N) (gammaNRep N n) (gammaNRel f)) :=
    splitCohomologyEdge_apply (gammaNSplitting N) (gammaNRep N n) (gammaNRel f)
  change (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
    (gammaNCoordinateIso N n).hom 1)
    (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNRel f))) = _
  rw [h1, H1π_comp_map_apply, ← map_smul]
  refine congrArg (fun z => H1π (binRep (CongruenceSubgroup.Gamma N) n) z) ?_
  apply cocycles₁_ext
  intro A
  change gammaNRadicalCoordinate N n (H1π _
      (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNRel f))) = _
  refine (gammaNRadicalCoordinate_π N n _).trans ?_
  rw [gammaNEdgeCyc_pull, levelEdge_coordinate]
  rfl

/-! ### The antiholomorphic seed -/

/-- The zig-zag cochain of the antiholomorphic seed on `Γ(N) ∩ P(ℤ)`. -/
def gammaNConjChain (g k : ↥(gammaNP N)) : Coef n :=
  cuspSeedConjCochain (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) g k

omit [NeZero N] in
theorem gammaNConjChain_eq (g k : ↥(gammaNP N)) :
    gammaNConjChain f g k = Coef.conjCoef (gammaNChain f g k) :=
  cuspSeedConjCochain_eq (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) g k

/-- The antiholomorphic seed cochain with values in `gammaNRep N n`. -/
def gammaNConjChainR (g k : ↥(gammaNP N)) : gammaNRep N n := gammaNConjChain f g k

/-- The antiholomorphic seed cochain as a complex 2-cocycle. -/
def gammaNConjCocycle₂ : cocycles₂ (gammaNRep N n) :=
  ⟨fun p => gammaNConjChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedConjCochain_cocycle (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
      (f := f) g h j
    change gammaNConjChainR f (g * h) j + gammaNConjChainR f g h =
      (gammaNRep N n).ρ g (gammaNConjChainR f h j) + gammaNConjChainR f g (h * j)
    have e2 : (gammaNRep N n).ρ g (gammaNConjChainR f h j) =
        (gammaNPlaneData N).rhoR n g (gammaNConjChain f h j) := rfl
    rw [e2]
    exact e)⟩

omit [NeZero N] in
theorem gammaNConjChain_inl_inl (r r' : RadicalLattice) :
    gammaNConjChain f (gammaNInl N r) (gammaNInl N r') = 0 := by
  rw [gammaNConjChain_eq, gammaNChain_inl_inl]
  apply Coef.toPoly_injective
  simp

/-- The relative 2-cocycle of the antiholomorphic seed on `Γ(N) ∩ P(ℤ)`. -/
def gammaNConjRel : relativeTwoCocycles (gammaNExt N).inl (gammaNRep N n) :=
  ⟨gammaNConjCocycle₂ f, fun r r' => gammaNConjChain_inl_inl f r r'⟩

theorem gammaNEdgeValConj_eq (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) :
    (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNConjRel f) r : Coef n) =
      Coef.conjCoef (gammaNEdgeVal f A r) := by
  change gammaNConjChain f (gammaNSect N A)
        (gammaNInl N (splitRadicalInput (gammaNSplitting N) A r)) -
      gammaNConjChain f (gammaNInl N r) (gammaNSect N A) =
    Coef.conjCoef (gammaNChain f (gammaNSect N A)
        (gammaNInl N (splitRadicalInput (gammaNSplitting N) A r)) -
      gammaNChain f (gammaNInl N r) (gammaNSect N A))
  rw [gammaNConjChain_eq, gammaNConjChain_eq]
  apply Coef.toPoly_injective
  simp

theorem tOp_conj (x : Coef n) :
    tOp N n (Coef.conjCoef x) = Coef.conjCoef (tOp N n x) := by
  apply Coef.toPoly_injective
  refine (tOp_coe N n _).trans ?_
  change _ = MvPolynomial.map (starRingEnd ℂ) ((tOp N n x : HomogeneousPoly n) :
    MvPolynomial (Fin 3) ℂ)
  refine Eq.trans ?_ (congrArg (MvPolynomial.map (starRingEnd ℂ)) (tOp_coe N n x)).symm
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_map, coeff_C_mul, coeff_sc, coeff_C_mul, coeff_sc]
  have hc : (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by simp
  simp only [map_mul, map_pow, hc]
  rfl


theorem gammaNEdgeCycConj_pull (A : ↥(CongruenceSubgroup.Gamma N)) :
    oneCocyclePullback (gammaNRadRep N n) (upperRadicalLatticeRep n) (MonoidHom.id _)
        (tOp N n) (tOp_rad_intertwines N n)
        (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNConjRel f)) =
      levelEdgeCycConj f A := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change tOp N n (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNConjRel f) r) =
    splitEdgeCycle (levelSplitting _) (levelRep _ n) A (levelConjRel f) r
  rw [levelEdgeValConj_eq, gammaNEdgeValConj_eq]
  rw [tOp_conj, tOp_gammaNEdgeVal]

/-- **The edge of the antiholomorphic seed on `Γ(N) ∩ P(ℤ)`** is `(n+1)⁻¹` times the class of the
antiholomorphic period cocycle. -/
theorem gammaNSeedConjEdge :
    gammaNEdge N n (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNConjRel f)) =
      (((n : ℂ) + 1)⁻¹) • H1π (binRep (CongruenceSubgroup.Gamma N) n) (antiholCocycle f) := by
  have h1 : splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNConjRel f)) =
      H1π (splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n))
        (splitCocycleEdge (gammaNSplitting N) (gammaNRep N n) (gammaNConjRel f)) :=
    splitCohomologyEdge_apply (gammaNSplitting N) (gammaNRep N n) (gammaNConjRel f)
  change (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
    (gammaNCoordinateIso N n).hom 1)
    (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n)
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNConjRel f))) = _
  rw [h1, H1π_comp_map_apply, ← map_smul]
  refine congrArg (fun z => H1π (binRep (CongruenceSubgroup.Gamma N) n) z) ?_
  apply cocycles₁_ext
  intro A
  change gammaNRadicalCoordinate N n (H1π _
      (splitEdgeCycle (gammaNSplitting N) (gammaNRep N n) A (gammaNConjRel f))) = _
  refine (gammaNRadicalCoordinate_π N n _).trans ?_
  rw [gammaNEdgeCycConj_pull, levelEdgeConj_coordinate]
  rfl

end Seed

/-! ### Complexification and spanning on `Γ(N) ∩ P(ℤ)` -/

section Complex

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- Coefficients, real carrier to complex carrier (the identity). -/
def cxVecG (x : Rep.of ((gammaNPlaneData N).rhoR n)) : gammaNRep N n := x

/-- Real 2-cocycles of `Γ_P` with values in `E_n` are complex 2-cocycles. -/
def cxCocyclesG :
    cocycles₂ (Rep.of ((gammaNPlaneData N).rhoR n)) →ₗ[ℝ] cocycles₂ (gammaNRep N n) where
  toFun c := ⟨fun p => cxVecG N n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    change cxVecG N n (c.1 (g * h, j)) + cxVecG N n (c.1 (g, h)) =
      (gammaNRep N n).ρ g (cxVecG N n (c.1 (h, j))) + cxVecG N n (c.1 (g, h * j))
    have e2 : (gammaNRep N n).ρ g (cxVecG N n (c.1 (h, j))) =
        cxVecG N n ((gammaNPlaneData N).rhoR n g (c.1 (h, j))) := gammaNRep_ρ (N := N) n g _
    rw [e2]
    exact e)⟩
  map_add' a b := rfl
  map_smul' r a := rfl

/-- The complexification map `H²(Γ_P, E_n)_ℝ → H²(Γ_P, E_n)_ℂ`, the identity on cocycles. -/
def complexifyG :
    H2 (Rep.of ((gammaNPlaneData N).rhoR n)) →ₗ[ℝ] H2 (gammaNRep N n) :=
  realDescent (H2π (Rep.of ((gammaNPlaneData N).rhoR n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (gammaNRep N n)).hom.restrictScalars ℝ).comp (cxCocyclesG N n))
    (fun a b hab => by
      have h : H2π (Rep.of ((gammaNPlaneData N).rhoR n)) a =
          H2π (Rep.of ((gammaNPlaneData N).rhoR n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (gammaNRep N n) (cxCocyclesG N n a) = H2π (gammaNRep N n) (cxCocyclesG N n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVecG N n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      change (gammaNRep N n).ρ p.1 (cxVecG N n (y p.2)) - cxVecG N n (y (p.1 * p.2)) +
          cxVecG N n (y p.1) = cxVecG N n (a.1 p) - cxVecG N n (b.1 p)
      have e2 : (gammaNRep N n).ρ p.1 (cxVecG N n (y p.2)) =
          cxVecG N n ((gammaNPlaneData N).rhoR n p.1 (y p.2)) := gammaNRep_ρ (N := N) n p.1 _
      rw [e2]
      exact hp)

theorem complexifyG_H2π (c : cocycles₂ (Rep.of ((gammaNPlaneData N).rhoR n))) :
    complexifyG N n (H2π (Rep.of ((gammaNPlaneData N).rhoR n)) c) =
      H2π (gammaNRep N n) (cxCocyclesG N n c) :=
  realDescent_apply _ _ _ _ c

variable {N n} (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ))

/-- The complexification of the de Rham class of the seed is the class of `gammaNRel`. -/
theorem complexifyG_cuspSeedClass :
    complexifyG N n (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) =
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNRel f)).val := by
  change complexifyG N n (H2π (Rep.of ((gammaNPlaneData N).rhoR n))
    (ZigZag.cochainCocycle _ _)) = H2π (gammaNRep N n) (gammaNCocycle₂ f)
  rw [complexifyG_H2π]
  rfl

/-- The complexification of the de Rham class of the antiholomorphic seed is the class of
`gammaNConjRel`. -/
theorem complexifyG_cuspSeedConjClass :
    complexifyG N n (cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
      (f := f)) =
      (relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNConjRel f)).val := by
  change complexifyG N n (H2π (Rep.of ((gammaNPlaneData N).rhoR n))
    (ZigZag.cochainCocycle _ _)) = H2π (gammaNRep N n) (gammaNConjCocycle₂ f)
  rw [complexifyG_H2π]
  rfl

end Complex

section Spanning

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The class of the seed of `f` in the kernel of the radical restriction at `Γ_P`. -/
def gammaNSeedKerClass (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker :=
  relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNRel f)

/-- The class of the antiholomorphic seed of `f` in the kernel of the radical restriction. -/
def gammaNSeedConjKerClass
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker :=
  relativeTwoCocycleClass (gammaNExt N).inl (gammaNRep N n) (gammaNConjRel f)

/-- The span of the holomorphic and antiholomorphic seed classes at `Γ_P`. -/
def gammaNSeedKerSpan :
    Submodule ℂ ↥(twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker :=
  Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        gammaNSeedKerClass N n f) ∪
      Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        gammaNSeedConjKerClass N n f))

/-- **Spanning at the paper's plane group, conditional on Eichler--Shimura for `Γ(N)`.**
Assume `ESSpan (Γ(N)) n`. Every class of the kernel of the radical restriction (radical `Nℤ²`)
whose Hochschild--Serre edge is a parabolic class of `H¹(Γ(N), Sym^{n+1} ⊗ det⁻¹)` is a
combination of the classes of the holomorphic and antiholomorphic seeds. -/
theorem gammaN_seed_span_of_ESSpan (hES : ESSpan (CongruenceSubgroup.Gamma N) n)
    (x : ↥(twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker)
    (hx : gammaNEdge N n x ∈ parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    x ∈ gammaNSeedKerSpan N n := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hle : parabolicH1 (CongruenceSubgroup.Gamma N) n ≤
      Submodule.map (gammaNEdge N n) (gammaNSeedKerSpan N n) := by
    refine hES.trans (Submodule.span_le.2 ?_)
    rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
    · refine ⟨((n : ℂ) + 1) • gammaNSeedKerClass N n f, Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inl ⟨f, rfl⟩)), ?_⟩
      rw [map_smul, gammaNSeedKerClass, gammaNSeedEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]
    · refine ⟨((n : ℂ) + 1) • gammaNSeedConjKerClass N n f, Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inr ⟨f, rfl⟩)), ?_⟩
      rw [map_smul, gammaNSeedConjKerClass, gammaNSeedConjEdge, smul_smul, mul_inv_cancel₀ hn,
        one_smul]
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [← gammaNEdge_injective_binary N n hyx]

/-- The span of the complexified de Rham classes of the seeds at `Γ_P`, in `H²(Γ_P, E_n)`. -/
def gammaNSeedSpan : Submodule ℂ (H2 (gammaNRep N n)) :=
  Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        complexifyG N n
          (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f))) ∪
      Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        complexifyG N n
          (cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f))))

/-- **Spanning of the mixed cuspidal group of `Γ(N) ∩ P(ℤ)` by the paper's seeds,
conditional on Eichler--Shimura for `Γ(N)`.** A class of `H²(Γ_P, E_n)` restricting to zero on the
radical `Nℤ²` and whose edge is parabolic lies in the span of the complexified de Rham classes of
the seeds `ω_f` and `\overline{ω_f}`, `f ∈ S_{n+3}(Γ₂(N))`. -/
theorem gammaN_seed_span_conditional (hES : ESSpan (CongruenceSubgroup.Gamma N) n)
    (y : H2 (gammaNRep N n))
    (hy : twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n) y = 0)
    (hpar : gammaNEdge N n ⟨y, hy⟩ ∈ parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    y ∈ gammaNSeedSpan N n := by
  have h := gammaN_seed_span_of_ESSpan N n hES ⟨y, hy⟩ hpar
  have hmap : Submodule.map (LinearMap.ker (twoCohomologyRestriction (gammaNExt N).inl
      (gammaNRep N n))).subtype (gammaNSeedKerSpan N n) ≤ gammaNSeedSpan N n := by
    rw [gammaNSeedKerSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, (⟨f, rfl⟩ | ⟨f, rfl⟩), rfl⟩
    · have e : ((gammaNSeedKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
          (gammaNRep N n)).ker) : H2 (gammaNRep N n)) =
          complexifyG N n
            (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) :=
        (complexifyG_cuspSeedClass f).symm
      change ((gammaNSeedKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
        (gammaNRep N n)).ker) : H2 (gammaNRep N n)) ∈ _
      rw [e]
      exact Submodule.subset_span (Or.inl ⟨f, rfl⟩)
    · have e : ((gammaNSeedConjKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
          (gammaNRep N n)).ker) : H2 (gammaNRep N n)) =
          complexifyG N n
            (cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) :=
        (complexifyG_cuspSeedConjClass f).symm
      change ((gammaNSeedConjKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
        (gammaNRep N n)).ker) : H2 (gammaNRep N n)) ∈ _
      rw [e]
      exact Submodule.subset_span (Or.inr ⟨f, rfl⟩)
  exact hmap (Submodule.mem_map_of_mem h)

/-- The seeds at `Γ_P` have parabolic edge (unconditional). -/
theorem gammaNSeedKerSpan_le_comap :
    gammaNSeedKerSpan N n ≤
      Submodule.comap (gammaNEdge N n) (parabolicH1 (CongruenceSubgroup.Gamma N) n) := by
  rw [gammaNSeedKerSpan, Submodule.span_le]
  rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
  · change gammaNEdge N n (gammaNSeedKerClass N n f) ∈
      parabolicH1 (CongruenceSubgroup.Gamma N) n
    rw [gammaNSeedKerClass, gammaNSeedEdge]
    exact Submodule.smul_mem _ _ ⟨holCocycle f, holCocycle_mem_parabolicCocycles f, rfl⟩
  · change gammaNEdge N n (gammaNSeedConjKerClass N n f) ∈
      parabolicH1 (CongruenceSubgroup.Gamma N) n
    rw [gammaNSeedConjKerClass, gammaNSeedConjEdge]
    exact Submodule.smul_mem _ _ ⟨antiholCocycle f, antiholCocycle_mem_parabolicCocycles f, rfl⟩

/-- **The kernel of the radical restriction with parabolic edge is spanned by the seeds at `Γ_P`,
conditional on `ESSpan (Γ(N)) n`.** -/
theorem gammaNSeedKerSpan_eq_comap (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    gammaNSeedKerSpan N n =
      Submodule.comap (gammaNEdge N n) (parabolicH1 (CongruenceSubgroup.Gamma N) n) :=
  le_antisymm (gammaNSeedKerSpan_le_comap N n)
    (fun x hx => gammaN_seed_span_of_ESSpan N n hES x hx)

end Spanning

end TernaryPeriodPolynomials.Argument.SeedC3S4c
