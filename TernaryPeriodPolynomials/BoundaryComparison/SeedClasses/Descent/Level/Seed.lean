module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.Group
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.EdgeConj

@[expose] public section


/-!
# The seed of `f ∈ S_{n+3}(Λ)` on `ℤ² ⋊ Λ`, its edge, and spanning conditional on Eichler--Shimura

Paper: Lemma C.3
(`ar:lem:seed`), last sentence (spanning of the mixed cuspidal group `𝒞_P(E)`).

For a subgroup `Λ ⊆ SL₂(ℤ)` (for instance the principal congruence subgroup `Γ₂(N)`) and a cusp
form `f` of weight `n + 3` for the image `LamGL Λ` in `GL₂(ℝ)`, the zig-zag cochain of the seed
`ω_f` (and of the antiholomorphic seed `\overline{ω_f}`) on the plane group `ℤ² ⋊ Λ`
(`levelPlaneData`, the restriction of `Λ₀⁺`) is a relative 2-cocycle `levelRel f`
(`levelConjRel f`), whose class is the complexification of the real de Rham class
(`complexifyL_cuspSeedClass`). Its `(1,1)` Hochschild--Serre edge in the binary coordinates of
`H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` is `(n+1)⁻¹` times the class of the holomorphic (antiholomorphic)
period cocycle `holCocycle f` (`antiholCocycle f`) (`levelSeedEdge`, `levelSeedConjEdge`).
Since the edge is injective for every `Λ` (`levelEdge_injective_binary`), the seeds span the
classes with parabolic edge as soon as `ESSpan Λ n` holds (`seed_span_of_ESSpan`,
`seed_span_conditional`): the Eichler--Shimura spanning hypothesis `ESSpan Λ n` is the single input of the spanning clause.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3
open CategoryTheory groupCohomology

variable (Λ : Subgroup SL(2, ℤ))

/-- `ℤ² ⋊ Λ` as a plane parabolic group (the restriction of `plusPlaneData`). -/
def levelPlaneData : PlaneData (levelGroup Λ) where
  lam := plusLam.comp (levelGroup Λ).subtype
  w g := plusW g.1
  det_one g := plusPlaneData.det_one g.1
  w_mul g h := plusPlaneData.w_mul g.1 h.1

theorem level_hΛ (g : levelGroup Λ) : ((levelPlaneData Λ).lam g : GL (Fin 2) ℝ) ∈ LamGL Λ :=
  ⟨plusProjS g.1, g.2, (plusLam_eq_mapGL g.1).symm⟩

theorem levelRep_ρ (n : ℕ) (g : levelGroup Λ) (x : Coef n) :
    (levelRep Λ n).ρ g x = (levelPlaneData Λ).rhoR n g x :=
  plusRep_ρ n g.1 x

section

variable {Λ} {n : ℕ} (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the seed of `f ∈ S_{n+3}(Λ)`, on `ℤ² ⋊ Λ`. -/
def levelChain (g k : levelGroup Λ) : Coef n :=
  cuspSeedCochain (levelPlaneData Λ) (level_hΛ Λ) (f := f) g k

theorem levelChain_cocycle (g h j : levelGroup Λ) :
    levelChain f (g * h) j + levelChain f g h =
      (levelPlaneData Λ).rhoR n g (levelChain f h j) + levelChain f g (h * j) :=
  cuspSeedCochain_cocycle (levelPlaneData Λ) (level_hΛ Λ) g h j

/-- The Eichler cocycle of the moment primitives at the Levi block of `k`, as a polynomial in
`X, Y, Z`. -/
def levelEps (k : levelGroup Λ) : MvPolynomial (Fin 3) ℂ :=
  rename Fin.castSucc
    (eichlerCocycle n (momentPrim (LamGL Λ) n f) ((levelPlaneData Λ).lam k))

theorem toPoly_levelChain (g k : levelGroup Λ) :
    Coef.toPoly (levelChain f g k) =
      C (((n : ℂ) + 1)⁻¹) *
        ddiv (rho ((levelPlaneData Λ).plm g) (levelEps f k) -
          rho (parabolicMatrix ((levelPlaneData Λ).lamM g) 0) (levelEps f k)) :=
  toPoly_cuspSeedCochain (levelPlaneData Λ) (level_hΛ Λ) (f := f) g k

theorem levelEps_inl (r : RadicalLattice) : levelEps f (levelInl Λ r) = 0 := by
  have h1 : ((levelPlaneData Λ).lam (levelInl Λ r)) = 1 := plusLam_inl r
  have h2 : mob ((levelPlaneData Λ).lam (levelInl Λ r)) Complex.I = Complex.I := by
    rw [h1]; simp [mob]
  unfold levelEps
  rw [eichlerCocycle, h2, eichlerPoly_base n _ (momentPrim_zero (LamGL Λ) n f), map_zero]

theorem levelChain_inl_inl (r r' : RadicalLattice) :
    levelChain f (levelInl Λ r) (levelInl Λ r') = 0 := by
  apply Coef.toPoly_injective
  rw [toPoly_levelChain, levelEps_inl]
  simp [rho, ddiv_zero]

/-- The seed cochain with values in the carrier of `levelRep Λ n`. -/
def levelChainR (g k : levelGroup Λ) : levelRep Λ n := levelChain f g k

/-- The seed cochain as a complex 2-cocycle of `ℤ² ⋊ Λ`. -/
def levelCocycle₂ : cocycles₂ (levelRep Λ n) :=
  ⟨fun p => levelChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := levelChain_cocycle f g h j
    change levelChainR f (g * h) j + levelChainR f g h =
      (levelRep Λ n).ρ g (levelChainR f h j) + levelChainR f g (h * j)
    have e2 : (levelRep Λ n).ρ g (levelChainR f h j) =
        (levelPlaneData Λ).rhoR n g (levelChain f h j) := levelRep_ρ Λ n g _
    rw [e2]
    exact e)⟩

/-- **The relative 2-cocycle of the seed of `f ∈ S_{n+3}(Λ)`** on `ℤ² ⋊ Λ`: it vanishes on pairs of
radical elements. -/
def levelRel : relativeTwoCocycles (levelExt Λ).inl (levelRep Λ n) :=
  ⟨levelCocycle₂ f, fun r r' => levelChain_inl_inl f r r'⟩

end

/-! ### Complexification of the coefficients -/

/-- Coefficients, real carrier to complex carrier (the identity). -/
def cxVecL (n : ℕ) (x : Rep.of ((levelPlaneData Λ).rhoR n)) : levelRep Λ n := x

/-- Real 2-cocycles of `ℤ² ⋊ Λ` with values in `E_n` are complex 2-cocycles. -/
def cxCocyclesL (n : ℕ) :
    cocycles₂ (Rep.of ((levelPlaneData Λ).rhoR n)) →ₗ[ℝ] cocycles₂ (levelRep Λ n) where
  toFun c := ⟨fun p => cxVecL Λ n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    change cxVecL Λ n (c.1 (g * h, j)) + cxVecL Λ n (c.1 (g, h)) =
      (levelRep Λ n).ρ g (cxVecL Λ n (c.1 (h, j))) + cxVecL Λ n (c.1 (g, h * j))
    have e2 : (levelRep Λ n).ρ g (cxVecL Λ n (c.1 (h, j))) =
        cxVecL Λ n ((levelPlaneData Λ).rhoR n g (c.1 (h, j))) := levelRep_ρ Λ n g _
    rw [e2]
    exact e)⟩
  map_add' a b := rfl
  map_smul' r a := rfl

/-- The complexification map `H²(ℤ² ⋊ Λ, E_n)_ℝ → H²(ℤ² ⋊ Λ, E_n)_ℂ`, the identity on cocycles. -/
def complexifyL (n : ℕ) :
    H2 (Rep.of ((levelPlaneData Λ).rhoR n)) →ₗ[ℝ] H2 (levelRep Λ n) :=
  realDescent (H2π (Rep.of ((levelPlaneData Λ).rhoR n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (levelRep Λ n)).hom.restrictScalars ℝ).comp (cxCocyclesL Λ n))
    (fun a b hab => by
      have h : H2π (Rep.of ((levelPlaneData Λ).rhoR n)) a =
          H2π (Rep.of ((levelPlaneData Λ).rhoR n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (levelRep Λ n) (cxCocyclesL Λ n a) = H2π (levelRep Λ n) (cxCocyclesL Λ n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVecL Λ n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      change (levelRep Λ n).ρ p.1 (cxVecL Λ n (y p.2)) - cxVecL Λ n (y (p.1 * p.2)) +
          cxVecL Λ n (y p.1) = cxVecL Λ n (a.1 p) - cxVecL Λ n (b.1 p)
      have e2 : (levelRep Λ n).ρ p.1 (cxVecL Λ n (y p.2)) =
          cxVecL Λ n ((levelPlaneData Λ).rhoR n p.1 (y p.2)) := levelRep_ρ Λ n p.1 _
      rw [e2]
      exact hp)

theorem complexifyL_H2π (n : ℕ) (c : cocycles₂ (Rep.of ((levelPlaneData Λ).rhoR n))) :
    complexifyL Λ n (H2π (Rep.of ((levelPlaneData Λ).rhoR n)) c) =
      H2π (levelRep Λ n) (cxCocyclesL Λ n c) :=
  realDescent_apply _ _ _ _ c

section

variable {Λ} {n : ℕ} (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ))

/-- The complexification of the de Rham class of the seed is the class of `levelRel`. -/
theorem complexifyL_cuspSeedClass :
    complexifyL Λ n (cuspSeedClass (levelPlaneData Λ) (level_hΛ Λ) (f := f)) =
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelRel f)).val := by
  change complexifyL Λ n (H2π (Rep.of ((levelPlaneData Λ).rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (levelRep Λ n) (levelCocycle₂ f)
  rw [complexifyL_H2π]
  rfl

/-- The zig-zag cochain of the antiholomorphic seed, on `ℤ² ⋊ Λ`. -/
def levelConjChain (g k : levelGroup Λ) : Coef n :=
  cuspSeedConjCochain (levelPlaneData Λ) (level_hΛ Λ) (f := f) g k

theorem levelConjChain_eq (g k : levelGroup Λ) :
    levelConjChain f g k = Coef.conjCoef (levelChain f g k) :=
  cuspSeedConjCochain_eq (levelPlaneData Λ) (level_hΛ Λ) g k

/-- The antiholomorphic seed cochain with values in the carrier of `levelRep Λ n`. -/
def levelConjChainR (g k : levelGroup Λ) : levelRep Λ n := levelConjChain f g k

/-- The antiholomorphic seed cochain as a complex 2-cocycle of `ℤ² ⋊ Λ`. -/
def levelConjCocycle₂ : cocycles₂ (levelRep Λ n) :=
  ⟨fun p => levelConjChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedConjCochain_cocycle (levelPlaneData Λ) (level_hΛ Λ) (f := f) g h j
    change levelConjChainR f (g * h) j + levelConjChainR f g h =
      (levelRep Λ n).ρ g (levelConjChainR f h j) + levelConjChainR f g (h * j)
    have e2 : (levelRep Λ n).ρ g (levelConjChainR f h j) =
        (levelPlaneData Λ).rhoR n g (levelConjChain f h j) := levelRep_ρ Λ n g _
    rw [e2]
    exact e)⟩

theorem levelConjChain_inl_inl (r r' : RadicalLattice) :
    levelConjChain f (levelInl Λ r) (levelInl Λ r') = 0 := by
  rw [levelConjChain_eq, levelChain_inl_inl]
  apply Coef.toPoly_injective
  simp

/-- **The relative 2-cocycle of the antiholomorphic seed.** -/
def levelConjRel : relativeTwoCocycles (levelExt Λ).inl (levelRep Λ n) :=
  ⟨levelConjCocycle₂ f, fun r r' => levelConjChain_inl_inl f r r'⟩

/-- The complexification of the de Rham class of the antiholomorphic seed is the class of
`levelConjRel`. -/
theorem complexifyL_cuspSeedConjClass :
    complexifyL Λ n (cuspSeedConjClass (levelPlaneData Λ) (level_hΛ Λ) (f := f)) =
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelConjRel f)).val := by
  change complexifyL Λ n (H2π (Rep.of ((levelPlaneData Λ).rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (levelRep Λ n) (levelConjCocycle₂ f)
  rw [complexifyL_H2π]
  rfl

end

/-! ### The edge of the seed -/

section Edge

variable {Λ} {n : ℕ} (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ))

theorem toPoly_levelChain_section (m : Λ) (k : levelGroup Λ) :
    Coef.toPoly (levelChain f (levelSection Λ m) k) = 0 := by
  rw [toPoly_levelChain]
  have hw : (levelPlaneData Λ).plm (levelSection Λ m) =
      parabolicMatrix ((levelPlaneData Λ).lamM (levelSection Λ m)) 0 := by
    rw [PlaneData.plm_eq]
    show parabolicMatrix _ (plusW (plusSectionS m.1)) = _
    rw [plusW_section]
  rw [hw, sub_self, ddiv_zero, mul_zero]

theorem toPoly_levelChain_inl (r : RadicalLattice) (k : levelGroup Λ) :
    Coef.toPoly (levelChain f (levelInl Λ r) k) = C (((n : ℂ) + 1)⁻¹) *
      ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) (levelEps f k) -
        levelEps f k) := by
  rw [toPoly_levelChain]
  have hl : (levelPlaneData Λ).lamM (levelInl Λ r) = 1 := by
    show ((plusLam (plusInl r) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [plusLam_inl]
    rfl
  have hp : (levelPlaneData Λ).plm (levelInl Λ r) =
      parabolicMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)] := by
    rw [PlaneData.plm_eq, hl]
    show parabolicMatrix 1 (plusW (plusInl r)) = _
    rw [plusW_inl]
  rw [hp, hl, rho_par_one, rho_par_zero]

/-- The mixed part of the seed cocycle, with values in `E_n`. -/
def levelEdgeVal (m : Λ) (r : RadicalLattice) : Coef n :=
  splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelRel f) r

/-- The mixed part of the seed cocycle: `r ↦ -c(n_r, s(m))`. -/
theorem toPoly_levelEdgeVal (m : Λ) (r : RadicalLattice) :
    Coef.toPoly (levelEdgeVal f m r) =
      -(C (((n : ℂ) + 1)⁻¹) *
        ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) (levelEps f (levelSection Λ m)) -
          levelEps f (levelSection Λ m))) := by
  rw [← toPoly_levelChain_inl]
  change Coef.toPoly (levelChain f (levelSection Λ m)
    (levelInl Λ (splitRadicalInput (levelSplitting Λ) m r)) -
    levelChain f (levelInl Λ r) (levelSection Λ m)) = _
  rw [Coef.toPoly_sub, toPoly_levelChain_section, zero_sub]

theorem levelEps_section (m : Λ) :
    levelEps f (levelSection Λ m) = binaryPolynomialLift (eichlerForm f m.1).val := by
  unfold levelEps
  rw [show (levelPlaneData Λ).lam (levelSection Λ m) = SpecialLinearGroup.mapGL ℝ m.1 from
    plusLam_section m.1]
  rfl

/-- The mixed radical cocycle of the seed, as a cocycle of the library's upper radical
representation. -/
def levelEdgeCyc (m : Λ) : cocycles₁ (upperRadicalLatticeRep n) :=
  splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelRel f)

/-- **The binary coordinate of the mixed radical cocycle of the seed**: `(n+1)⁻¹ ε_m`. -/
theorem levelEdge_coordinate (m : Λ) :
    upperRadicalCocycleCoordinate n (levelEdgeCyc f m) =
      (((n : ℂ) + 1)⁻¹) • eichlerForm f m.1 := by
  refine coordinate_of_gen n _ _ fun i => ?_
  have h := toPoly_levelEdgeVal f m (radicalLatticeGenerator i)
  rw [gen_shift, ← unitShift_eq, levelEps_section] at h
  exact h

end Edge

section EdgeClass

variable {Λ} {n : ℕ} (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ))

/-- The binary form `\overline{ε_m}` of the conjugate Eichler cocycle. -/
def conjForm (m : Λ) : Binary.HomogeneousPoly (n + 1) := conjB (eichlerForm f m.1)

/-- The mixed radical cocycle of the antiholomorphic seed. -/
def levelEdgeCycConj (m : Λ) : cocycles₁ (upperRadicalLatticeRep n) :=
  splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelConjRel f)

theorem levelEdgeValConj_eq (m : Λ) (r : RadicalLattice) :
    (splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelConjRel f) r : Coef n) =
      Coef.conjCoef (levelEdgeVal f m r) := by
  change levelConjChain f (levelSection Λ m)
        (levelInl Λ (splitRadicalInput (levelSplitting Λ) m r)) -
      levelConjChain f (levelInl Λ r) (levelSection Λ m) =
    Coef.conjCoef (levelChain f (levelSection Λ m)
        (levelInl Λ (splitRadicalInput (levelSplitting Λ) m r)) -
      levelChain f (levelInl Λ r) (levelSection Λ m))
  rw [levelConjChain_eq, levelConjChain_eq]
  apply Coef.toPoly_injective
  simp

theorem lvec_levelEdgeCycConj (m : Λ) (i : Fin 2) :
    lvec n (levelEdgeCycConj f m (radicalLatticeGenerator i)) =
      -(C (((n : ℂ) + 1)⁻¹) * ddiv (bind₁ (unitShift i)
          (binaryPolynomialLift (conjB (eichlerForm f m.1)).val) -
        binaryPolynomialLift (conjB (eichlerForm f m.1)).val)) := by
  have h := toPoly_levelEdgeVal f m (radicalLatticeGenerator i)
  rw [gen_shift, ← unitShift_eq, levelEps_section] at h
  have h2 : lvec n (levelEdgeCycConj f m (radicalLatticeGenerator i)) =
      MvPolynomial.map (starRingEnd ℂ)
        (Coef.toPoly (levelEdgeVal f m (radicalLatticeGenerator i))) := by
    have := congrArg Coef.toPoly (levelEdgeValConj_eq f m (radicalLatticeGenerator i))
    exact this
  rw [h2, h]
  simp only [map_neg, map_mul, MvPolynomial.map_C, map_sub, map_conj_ddiv, map_conj_bind_unitShift]
  have hc : (starRingEnd ℂ) (((n : ℂ) + 1)⁻¹) = ((n : ℂ) + 1)⁻¹ := by
    simp
  rw [hc]
  have hl : MvPolynomial.map (starRingEnd ℂ) (binaryPolynomialLift (eichlerForm f m.1).val) =
      binaryPolynomialLift (conjB (eichlerForm f m.1)).val := by
    simp [binaryPolynomialLift, conjB, MvPolynomial.map_rename]
  rw [hl]

theorem levelEdgeConj_coordinate (m : Λ) :
    upperRadicalCocycleCoordinate n (levelEdgeCycConj f m) =
      (((n : ℂ) + 1)⁻¹) • conjB (eichlerForm f m.1) :=
  coordinate_of_gen n _ _ (lvec_levelEdgeCycConj f m)

/-- **The edge of the seed of `f ∈ S_{n+3}(Λ)`** is `(n+1)⁻¹` times the class of the holomorphic
period cocycle. -/
theorem levelSeedEdge :
    levelEdge Λ n (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelRel f)) =
      (((n : ℂ) + 1)⁻¹) • H1π (binRep Λ n) (holCocycle f) := by
  have h1 : splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelRel f)) =
      H1π (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n))
        (splitCocycleEdge (levelSplitting Λ) (levelRep Λ n) (levelRel f)) :=
    splitCohomologyEdge_apply (levelSplitting Λ) (levelRep Λ n) (levelRel f)
  change (groupCohomology.map (MonoidHom.id Λ) (levelCoordinateIso Λ n).hom 1)
    (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelRel f))) = _
  rw [h1, H1π_comp_map_apply]
  refine Eq.trans ?_ (LinearMap.map_smul (H1π (binRep Λ n)).hom (((n : ℂ) + 1)⁻¹) (holCocycle f))
  refine congrArg (fun z => H1π (binRep Λ n) z) ?_
  apply cocycles₁_ext
  intro m
  change upperRadicalH1Coordinate n (H1π _
      (splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelRel f))) = _
  refine (upperRadicalH1Coordinate_apply (levelEdgeCyc f m)).trans ?_
  rw [levelEdge_coordinate]
  rfl

/-- **The edge of the antiholomorphic seed of `f ∈ S_{n+3}(Λ)`** is `(n+1)⁻¹` times the class of
the antiholomorphic period cocycle. -/
theorem levelSeedConjEdge :
    levelEdge Λ n (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelConjRel f)) =
      (((n : ℂ) + 1)⁻¹) • H1π (binRep Λ n) (antiholCocycle f) := by
  have h1 : splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelConjRel f)) =
      H1π (splitRadicalH1Representation (levelSplitting Λ) (levelRep Λ n))
        (splitCocycleEdge (levelSplitting Λ) (levelRep Λ n) (levelConjRel f)) :=
    splitCohomologyEdge_apply (levelSplitting Λ) (levelRep Λ n) (levelConjRel f)
  change (groupCohomology.map (MonoidHom.id Λ) (levelCoordinateIso Λ n).hom 1)
    (splitCohomologyEdge (levelSplitting Λ) (levelRep Λ n)
      (relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelConjRel f))) = _
  rw [h1, H1π_comp_map_apply]
  refine Eq.trans ?_ (LinearMap.map_smul (H1π (binRep Λ n)).hom (((n : ℂ) + 1)⁻¹) (antiholCocycle f))
  refine congrArg (fun z => H1π (binRep Λ n) z) ?_
  apply cocycles₁_ext
  intro m
  change upperRadicalH1Coordinate n (H1π _
      (splitEdgeCycle (levelSplitting Λ) (levelRep Λ n) m (levelConjRel f))) = _
  refine (upperRadicalH1Coordinate_apply (levelEdgeCycConj f m)).trans ?_
  rw [levelEdgeConj_coordinate]
  rfl

end EdgeClass

/-! ### Spanning, conditional on Eichler--Shimura -/

section Spanning

variable {Λ} {n : ℕ}

/-- The class of the seed of `f` in the kernel of the radical restriction. -/
def seedKerClass (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker :=
  relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelRel f)

/-- The class of the antiholomorphic seed of `f` in the kernel of the radical restriction. -/
def seedConjKerClass (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker :=
  relativeTwoCocycleClass (levelExt Λ).inl (levelRep Λ n) (levelConjRel f)

variable (Λ n)

/-- The span of the holomorphic and antiholomorphic seed classes, as a subspace of the kernel of
the radical restriction. -/
def seedKerSpan : Submodule ℂ ↥(twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker :=
  Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) => seedKerClass f) ∪
      Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) => seedConjKerClass f))

/-- **Spanning, conditional on Eichler--Shimura for `Λ`.** If `ESSpan Λ n` holds, every class of
the kernel of the radical restriction whose Hochschild--Serre edge is a parabolic class of
`H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` is a combination of the classes of the holomorphic and antiholomorphic
seeds of cusp forms of weight `n + 3` for `Λ`. -/
theorem seed_span_of_ESSpan (hES : ESSpan Λ n)
    (x : ↥(twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n)).ker)
    (hx : levelEdge Λ n x ∈ parabolicH1 Λ n) : x ∈ seedKerSpan Λ n := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hle : parabolicH1 Λ n ≤ Submodule.map (levelEdge Λ n) (seedKerSpan Λ n) := by
    refine hES.trans (Submodule.span_le.2 ?_)
    rintro _ (⟨f, rfl⟩ | ⟨f, rfl⟩)
    · refine ⟨((n : ℂ) + 1) • seedKerClass f, Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inl ⟨f, rfl⟩)), ?_⟩
      rw [map_smul, seedKerClass, levelSeedEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]
    · refine ⟨((n : ℂ) + 1) • seedConjKerClass f, Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inr ⟨f, rfl⟩)), ?_⟩
      rw [map_smul, seedConjKerClass, levelSeedConjEdge, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hobtain1 := hle hx
  obtain ⟨y, hy, hyx⟩ := hobtain1
  rwa [← levelEdge_injective_binary Λ n hyx]

/-- The span of the complexified de Rham classes of the seeds, in `H²(ℤ² ⋊ Λ, E_n)`. -/
def seedSpan : Submodule ℂ (H2 (levelRep Λ n)) :=
  Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
        complexifyL Λ n (cuspSeedClass (levelPlaneData Λ) (level_hΛ Λ) (f := f))) ∪
      Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
        complexifyL Λ n (cuspSeedConjClass (levelPlaneData Λ) (level_hΛ Λ) (f := f))))

/-- **Spanning of the mixed cuspidal group by the paper's seeds, conditional on
Eichler--Shimura.** Assume `ESSpan Λ n`. A class `y ∈ H²(ℤ² ⋊ Λ, E_n)` that restricts to zero on the
radical lattice and whose edge is a parabolic class of `H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` lies in the span
of the complexified de Rham classes of the seeds `ω_f` and `\overline{ω_f}`,
`f ∈ S_{n+3}(Λ)`. -/
theorem seed_span_conditional (hES : ESSpan Λ n) (y : H2 (levelRep Λ n))
    (hy : twoCohomologyRestriction (levelExt Λ).inl (levelRep Λ n) y = 0)
    (hpar : levelEdge Λ n ⟨y, hy⟩ ∈ parabolicH1 Λ n) : y ∈ seedSpan Λ n := by
  have h := seed_span_of_ESSpan Λ n hES ⟨y, hy⟩ hpar
  have hmap : Submodule.map (LinearMap.ker (twoCohomologyRestriction (levelExt Λ).inl
      (levelRep Λ n))).subtype (seedKerSpan Λ n) ≤ seedSpan Λ n := by
    rw [seedKerSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, (⟨f, rfl⟩ | ⟨f, rfl⟩), rfl⟩
    · have e : ((seedKerClass f : ↥(twoCohomologyRestriction (levelExt Λ).inl
          (levelRep Λ n)).ker) : H2 (levelRep Λ n)) =
          complexifyL Λ n (cuspSeedClass (levelPlaneData Λ) (level_hΛ Λ) (f := f)) :=
        (complexifyL_cuspSeedClass f).symm
      change ((seedKerClass f : ↥(twoCohomologyRestriction (levelExt Λ).inl
        (levelRep Λ n)).ker) : H2 (levelRep Λ n)) ∈ _
      rw [e]
      exact Submodule.subset_span (Or.inl ⟨f, rfl⟩)
    · have e : ((seedConjKerClass f : ↥(twoCohomologyRestriction (levelExt Λ).inl
          (levelRep Λ n)).ker) : H2 (levelRep Λ n)) =
          complexifyL Λ n (cuspSeedConjClass (levelPlaneData Λ) (level_hΛ Λ) (f := f)) :=
        (complexifyL_cuspSeedConjClass f).symm
      change ((seedConjKerClass f : ↥(twoCohomologyRestriction (levelExt Λ).inl
        (levelRep Λ n)).ker) : H2 (levelRep Λ n)) ∈ _
      rw [e]
      exact Submodule.subset_span (Or.inr ⟨f, rfl⟩)
  exact hmap (Submodule.mem_map_of_mem h)

end Spanning

end TernaryPeriodPolynomials.Argument.SeedC3S4c
