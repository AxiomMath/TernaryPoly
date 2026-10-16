module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EdgeToCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantExt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.EtaExists
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspHomSum

@[expose] public section


/-!
# The global term: `∑_c (r e(X_c, C'(σ_c)) - μ σ_c) = ½ r (facePairingCan)`

Formalized by Claude Sonnet 5.5.

For normal-form relative cocycles `z`, `z'` and a primitive `γ` (vanishing on radical triples, `dγ = z ∪ z'`) of the extension `1 → ℤ² → E → Γ(N) → 1`, `μ σ = ⟨γ, Sh₁ σ⟩`.
`exists_eta_edge`: the cup cocycle of the edge classes has a primitive `η : gammaNGL N → ℂ` (`H²(Γ(N), ℂ) = 0`).  `rEta_add_mu_additive`: `r ∘ η + μ ∘ gammaEquiv⁻¹` is additive
(`fibre_primitive_alt`), hence has cusp sum zero (`hom_cusp_sum_zero`); `cusp_total` combines this with `edge_pairing_cusp_sum`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open CongruenceSubgroup
open scoped Classical MatrixGroups

variable {N : ℕ}

section Eta

variable (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
  (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (W : Rep ℂ E) [FiniteDimensional ℂ W]
  (C : groupCohomology.cocycles₁ (splitRadicalH1Representation s W))
  (C' : groupCohomology.cocycles₁ (splitRadicalH1Representation s (dualRepG W)))

/-- **A primitive `η` of the cup cocycle of two edge cocycles** (`H²(Γ(N), ℂ) = 0`), as a function on `gammaNGL N`. -/
theorem exists_eta_edge :
    ∃ η : gammaNGL N → ℂ, ∀ x y, η (x * y) = η x + η y - (leviCoupling hN s hdet W).e (C.1 ((gammaEquiv hN).symm x))
      ((transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ x (C'.1 ((gammaEquiv hN).symm y))) := by
  have hinv : ∀ (g : Gamma N) u u', (leviCoupling hN s hdet W).e ((splitRadicalH1Representation s W).ρ g u)
      ((splitRadicalH1Representation s (dualRepG W)).ρ g u') = (leviCoupling hN s hdet W).e u u' := by
    intro g u u'
    have := (leviCoupling hN s hdet W).inv (gammaEquiv hN g) u u'
    simpa [transRep_ρ] using this
  obtain ⟨η, hη⟩ := exists_eta (Γ := Gamma N) (fun x => H2_vanish_level (Gamma N) _ x)
    (leviCoupling hN s hdet W).e hinv C.1
    (fun x y => (groupCohomology.mem_cocycles₁_iff C.1).1 C.2 x y)
    C'.1 (fun x y => (groupCohomology.mem_cocycles₁_iff C'.1).1 C'.2 x y)
  refine ⟨fun x => η ((gammaEquiv hN).symm x), fun x y => ?_⟩
  simp only [map_mul]
  rw [hη]
  rfl

end Eta

section Total

variable (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
  (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (W : Rep ℂ E) [FiniteDimensional ℂ W]

theorem levi_e_edge (c : groupCohomology.cocycles₁ (Rep.res ext.inl W))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG W))) :
    (leviCoupling hN s hdet W).e (groupCohomology.H1π _ c) (groupCohomology.H1π _ c') =
      altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) c.1 c'.1 latE1 latE2 :=
  radPairingOf_spec (ext := ext) (perfectInv_dual W) c c'

theorem edge_pair_eq (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W)) (α β : Gamma N) :
    (leviCoupling hN s hdet W).e ((splitCocycleEdge s W z).1 α)
      ((splitRadicalH1Representation s (dualRepG W)).ρ α ((splitCocycleEdge s (dualRepG W) z').1 β)) =
      altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (splitEdgeCycle s W α z)
        (splitRadicalCocycleAction s (dualRepG W) α (splitEdgeCycle s (dualRepG W) β z')) latE1 latE2 := by
  have e1 : (splitCocycleEdge s W z).1 α = groupCohomology.H1π _ (splitEdgeCycle s W α z) := rfl
  have e2 : (splitCocycleEdge s (dualRepG W) z').1 β = groupCohomology.H1π _ (splitEdgeCycle s (dualRepG W) β z') := rfl
  rw [e1, e2]
  change (leviCoupling hN s hdet W).e _ (splitRadicalH1Action s (dualRepG W) α _) = _
  rw [splitRadicalH1Action_apply]
  exact levi_e_edge hN s hdet W _ _

end Total

section Sum

variable (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
  (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (W : Rep ℂ E) [FiniteDimensional ℂ W]
  [Module ℚ W] [Module ℚ (dualRepG W)] (ρ' : Representation ℚ E (dualRepG W))
  (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x) (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ)
  (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
  (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W))
  (hU : ∀ a b : Gamma N, z.val (s a, s b) = 0) (hmix : ∀ (r : RadicalLattice) (l : Gamma N), z.val (ext.inl r, s l) = 0)
  (hmix' : ∀ (r : RadicalLattice) (l : Gamma N), z'.val (ext.inl r, s l) = 0)
  (γ : E → E → E → ℚ) (hγ : ∀ a b c : RadicalLattice, γ (ext.inl a) (ext.inl b) (ext.inl c) = 0)
  (hd : dd3T γ = cup22 ρ' eQ (fun a b => z.val (a, b)) (fun a b => z'.val (a, b)))

include hρ' he hU hmix hmix' hγ hd in
/-- **`r ∘ η + μ ∘ gammaEquiv⁻¹` is additive** for any primitive `η` of the cup cocycle of the edge classes. -/
theorem rEta_add_mu_additive (η : gammaNGL N → ℂ)
    (hη : ∀ x y, η (x * y) = η x + η y - (leviCoupling hN s hdet W).e ((splitCocycleEdge s W z).1 ((gammaEquiv hN).symm x))
      ((transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ x ((splitCocycleEdge s (dualRepG W) z').1 ((gammaEquiv hN).symm y)))) (x y : gammaNGL N) :
    r (η (x * y)) + (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm (x * y)) =
      (r (η x) + (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm x)) +
        (r (η y) + (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm y)) := by
  have hf := fibre_primitive_alt s ρ' hρ' eQ (Module.Dual.eval ℂ W) r he hdet z z' hU hmix hmix' γ hγ hd
    ((gammaEquiv hN).symm x) ((gammaEquiv hN).symm y)
  have hA := edge_pair_eq hN s hdet W z z' ((gammaEquiv hN).symm x) ((gammaEquiv hN).symm y)
  rw [hη x y, map_mul, map_sub, map_add]
  have h2 : (transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ x
      ((splitCocycleEdge s (dualRepG W) z').1 ((gammaEquiv hN).symm y)) =
      (splitRadicalH1Representation s (dualRepG W)).ρ ((gammaEquiv hN).symm x)
        ((splitCocycleEdge s (dualRepG W) z').1 ((gammaEquiv hN).symm y)) := rfl
  rw [h2, hA]
  linarith

include hρ' he hU hmix hmix' hγ hd in
/-- **The global term.**  With `X_c = Φ c + v` the cusp values of the edge class of `z`, `C'σ_c` the edge of `z'` at the cusp generator, and `μ σ = ⟨γ, Sh₁ σ⟩`:
`∑_c (r e(X_c, C'σ_c) - μ σ_c) = ½ r (facePairingCan edges)`. -/
theorem cusp_total
    (hC : groupCohomology.H1π _ (splitCocycleEdge s W z) ∈ cuspidalSubspace (Gamma N) (splitRadicalH1Representation s W))
    (hC' : groupCohomology.H1π _ (splitCocycleEdge s (dualRepG W) z') ∈
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG W)))
    (Φ : Tw (transRep hN (splitRadicalH1Representation s W)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation s (dualRepG W))).ρ)
    (v : splitRadicalH1Representation s W) (v' : splitRadicalH1Representation s (dualRepG W))
    (h0 : Φ.1 cusp1 = 0)
    (hCΦ : ∀ g : Gamma N, (splitCocycleEdge s W z).1 g = fTw (transRep hN (splitRadicalH1Representation s W)) Φ.1 (gammaEquiv hN g) +
      (v - (splitRadicalH1Representation s W).ρ g v))
    (hCΦ' : ∀ g : Gamma N, (splitCocycleEdge s (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation s (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation s (dualRepG W)).ρ g v')) :
    ∑ c ∈ (cuspReps hN).R, (r ((leviCoupling hN s hdet W).e (Φ.1 c + v)
        ((splitCocycleEdge s (dualRepG W) z').1 ((gammaEquiv hN).symm (cuspSigma c)))) -
      (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm (cuspSigma c))) =
      (1 / 2) * r (facePairingCan hN s hdet W ⟨groupCohomology.H1π _ (splitCocycleEdge s W z), hC⟩
        ⟨groupCohomology.H1π _ (splitCocycleEdge s (dualRepG W) z'), hC'⟩) := by
  obtain ⟨η, hη⟩ := exists_eta_edge hN s hdet W (splitCocycleEdge s W z) (splitCocycleEdge s (dualRepG W) z')
  have hcan := edge_pairing_cusp_sum hN s hdet W _ _ hC hC' Φ Φ' v v' h0 hCΦ hCΦ' η hη
  have hadd := rEta_add_mu_additive hN s hdet W ρ' hρ' eQ r he z z' hU hmix hmix' γ hγ hd η hη
  have hz := hom_cusp_sum_zero hN (fun x => (((r (η x) + (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2)
      ((gammaEquiv hN).symm x) : ℚ) : ℂ))) (fun x y => by
    have := hadd x y
    simp only [map_mul]
    exact_mod_cast this)
  have hz' : ∑ c ∈ (cuspReps hN).R, (r (η (cuspSigma c)) +
      (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) ((gammaEquiv hN).symm (cuspSigma c))) = 0 := by
    exact_mod_cast hz
  rw [hcan]
  have h2 : ∀ X : ℂ, r (2 * X) = 2 * r X := fun X => by rw [two_mul, map_add]; ring
  rw [h2, map_sum]
  simp only [map_add]
  rw [Finset.sum_add_distrib] at hz' ⊢
  rw [Finset.sum_sub_distrib]
  linarith

end Sum

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
