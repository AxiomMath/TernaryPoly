module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Orth
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final

@[expose] public section


/-!
# The Stokes relation at `Γ(6)` for an arbitrary coefficient module, decomposed along finite families of equivariant idempotents

Formalized by Claude Sonnet 5.5.

* `lineMixedSub_of_zeroFlags`, `planeMixedSub_of_zeroFlags`: the restriction to a line (plane) face of a global class of `H²(Γ(6), ρ)` with zero flag restrictions is mixed, for every `ρ`.
* `lineFacePairM_decomp_family`, `planeFacePairM_decomp_family`: if `(e j)_j` is a finite family of `S`-equivariant endomorphisms of the coefficients with `∑ e j = id` and `e k ∘ e j = 0` for `j ≠ k`, the face
  pairing of mixed classes is the sum of the diagonal terms `B(h2E (e j) x, h2E (e j)ᵀ y)`.
* `gamma6_stokes_decomposed`: the Stokes relation at `Γ(6)` with the face pairings replaced by these sums over arbitrary families of idempotents attached to each face (no comparison hypothesis).
  For `ρ = Ind_{Γ(M)}^{Γ(6)} E` and the orbit idempotents of the faces this is the `Γ(6)` side of Stokes at level `M`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section H2ESum

theorem h2E_zero {K : Type} [Group K] (A : Rep ℂ K) (he : ∀ k v, (0 : A →ₗ[ℂ] A) (A.ρ k v) = A.ρ k ((0 : A →ₗ[ℂ] A) v))
    (x : groupCohomology.H2 A) : h2E A 0 he x = 0 := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective A x
  rw [h2E_π]
  have : groupCohomology.mapCocycles₂ (MonoidHom.id K) (EdgeNat.comparison (MonoidHom.id K) A A 0 (fun g v => he g v)) z = 0 := by
    apply Subtype.ext
    funext ab
    rfl
  rw [this, map_zero]

theorem h2E_finset_sum {K : Type} [Group K] (A : Rep ℂ K) {J : Type} [DecidableEq J] (e : J → A →ₗ[ℂ] A)
    (he : ∀ j k v, e j (A.ρ k v) = A.ρ k (e j v)) (s : Finset J)
    (hs : ∀ k v, (∑ j ∈ s, e j) (A.ρ k v) = A.ρ k ((∑ j ∈ s, e j) v)) (x : groupCohomology.H2 A) :
    h2E A (∑ j ∈ s, e j) hs x = ∑ j ∈ s, h2E A (e j) (he j) x := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : ∀ k v, (0 : A →ₗ[ℂ] A) (A.ρ k v) = A.ρ k ((0 : A →ₗ[ℂ] A) v) := fun k v => by simp
    rw [h2E_congr A (Finset.sum_empty) hs h0, Finset.sum_empty]
    exact h2E_zero A h0 x
  | insert a s ha ih =>
    have hs' : ∀ k v, (∑ j ∈ s, e j) (A.ρ k v) = A.ρ k ((∑ j ∈ s, e j) v) := fun k v => by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl (fun j _ => he j k v)
    have hins : ∀ k v, (e a + ∑ j ∈ s, e j) (A.ρ k v) = A.ρ k ((e a + ∑ j ∈ s, e j) v) := fun k v => by
      rw [LinearMap.add_apply, LinearMap.add_apply, he a k v, hs' k v, map_add]
    rw [h2E_congr A (Finset.sum_insert ha) hs hins, h2E_add A (e a) (∑ j ∈ s, e j) (he a) hs' hins x,
      ih hs' , Finset.sum_insert ha]

end H2ESum

/-- The inclusion of the line group of the face `i` into `Γ(6) ⊂ SL₃(ℤ)`. -/
abbrev lineIncl (i : LineFaces 6) : gammaNQAt 6 i.rep →* gammaN 6 :=
  Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)

/-- The inclusion of the plane group of the face `i`. -/
abbrev planeIncl (i : PlaneFaces 6) : gammaNPAt 6 (planeFaceRepr i) →* gammaN 6 :=
  Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)


section LineFam

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **The restriction to a line face of a global class with zero flag restrictions is mixed.** -/
theorem lineMixedSub_of_zeroFlags (c : groupCohomology.H2 (Rep.of ρ))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c ∈
      lineMixedSub ρ i := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  obtain ⟨g, hg⟩ := lineFlagStab_map_exists_gammaNBAt 6 (by norm_num) i.rep F
  have hmem : ∀ k : lineFlagStab 6 i.rep F, ((k : gammaNQAt 6 i.rep) : SL(3, ℤ)) ∈ gammaNBAt 6 (blockDiagQ g⁻¹ * i.rep) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : lineFlagStab 6 i.rep F →* gammaNBAt 6 (blockDiagQ g⁻¹ * i.rep) :=
    ((gammaNQAt 6 i.rep).subtype.comp (lineFlagStab 6 i.rep F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
    (lineFlagStab 6 i.rep F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN 6 (blockDiagQ g⁻¹ * i.rep))) κ
    (by ext; rfl) (Rep.of ρ) c (hz _)

/-- **Decomposition of the face pairing along a finite family of orthogonal `S`-equivariant idempotents with sum the identity.** -/
theorem lineFacePairM_decomp_family {J : Type} [Fintype J] (e : J → V →ₗ[ℂ] V)
    (h : ∀ j (t : gammaNQAt 6 i.rep) (v : V), e j (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e j v))
    (hsum : ∀ v, ∑ j, e j v = v) (horth : ∀ j k, j ≠ k → ∀ v, e k (e j v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i) :
    lineFacePairM ρ i x y = ∑ j, lineFacePairM ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) (e j) (fun k v => h j k v) x)
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) (e j).dualMap
        (fun k v => lineHeD ρ i (e j) (h j) k v) y) := by
  classical
  let a : J → lineMixedSub ρ i := fun j => ⟨_, lineMixedSub_h2E ρ i (e j) (h j) x hx⟩
  let b : J → lineMixedSub ρ.dual i := fun j => ⟨_, lineMixedSub_h2E_dual ρ i (e j) (h j) y hy⟩
  have hs1 : ∀ k v, (∑ j, e j) (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) ((∑ j, e j) v) := fun k v => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun j _ => h j k v)
  have hxs : x = ∑ j, h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) (e j) (fun k v => h j k v) x := by
    rw [← h2E_finset_sum _ e (fun j k v => h j k v) Finset.univ (fun k v => hs1 k v) x]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun v => by rw [LinearMap.sum_apply]; exact hsum v)) _ (fun k v => rfl)]
    exact (h2E_id _ _ x).symm
  have hs2 : ∀ k (f : Module.Dual ℂ V), (∑ j, (e j).dualMap) (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) f) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) ((∑ j, (e j).dualMap) f) := fun k f => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun j _ => lineHeD ρ i (e j) (h j) k f)
  have hys : y = ∑ j, h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) (e j).dualMap
      (fun k v => lineHeD ρ i (e j) (h j) k v) y := by
    rw [← h2E_finset_sum _ (fun j => (e j).dualMap) (fun j k v => lineHeD ρ i (e j) (h j) k v) Finset.univ
      (fun k v => hs2 k v) y]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun f => LinearMap.ext (fun v => by
      change (∑ j, (e j).dualMap) f v = f v
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      change ∑ j, f (e j v) = f v
      rw [← map_sum, hsum]))) _ (fun k v => rfl)]
    exact (h2E_id _ _ y).symm
  have hxa : (⟨x, hx⟩ : lineMixedSub ρ i) = ∑ j, a j := Subtype.ext (by rw [Submodule.coe_sum]; exact hxs)
  have hyb : (⟨y, hy⟩ : lineMixedSub ρ.dual i) = ∑ j, b j := Subtype.ext (by rw [Submodule.coe_sum]; exact hys)
  have key : lineFacePairBil ρ i ⟨x, hx⟩ ⟨y, hy⟩ = ∑ j, lineFacePairBil ρ i (a j) (b j) := by
    rw [hxa, hyb]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · intro k _ hkj
      exact lineFacePairM_orth ρ i (e k) (e j) (h k) (h j) (horth k j hkj) x y hx hy
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  exact key

end LineFam

section PlaneFam

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- **The restriction to a line face of a global class with zero flag restrictions is mixed.** -/
theorem planeMixedSub_of_zeroFlags (c : groupCohomology.H2 (Rep.of ρ))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c ∈
      planeMixedSub ρ i := by
  refine (Submodule.mem_iInf _).2 (fun F => LinearMap.mem_ker.2 ?_)
  obtain ⟨g, hg⟩ := faceFlagStab_map_exists_gammaNBAt 6 (by norm_num) (planeFaceRepr i) F
  have hmem : ∀ k : faceFlagStab 6 (planeFaceRepr i) F, ((k : gammaNPAt 6 (planeFaceRepr i)) : SL(3, ℤ)) ∈ gammaNBAt 6 (blockDiag g⁻¹ * (planeFaceRepr i)) := by
    intro k
    rw [← hg]
    exact ⟨k.1, k.2, rfl⟩
  let κ : faceFlagStab 6 (planeFaceRepr i) F →* gammaNBAt 6 (blockDiag g⁻¹ * (planeFaceRepr i)) :=
    ((gammaNPAt 6 (planeFaceRepr i)).subtype.comp (faceFlagStab 6 (planeFaceRepr i) F).subtype).codRestrict _ hmem
  exact res_res_eq_zero (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
    (faceFlagStab 6 (planeFaceRepr i) F).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN 6 (blockDiag g⁻¹ * (planeFaceRepr i)))) κ
    (by ext; rfl) (Rep.of ρ) c (hz _)

/-- **Decomposition of the face pairing along a finite family of orthogonal `S`-equivariant idempotents with sum the identity.** -/
theorem planeFacePairM_decomp_family {J : Type} [Fintype J] (e : J → V →ₗ[ℂ] V)
    (h : ∀ j (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), e j (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) t) (e j v))
    (hsum : ∀ v, ∑ j, e j v = v) (horth : ∀ j k, j ≠ k → ∀ v, e k (e j v) = 0)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (hx : x ∈ planeMixedSub ρ i) (hy : y ∈ planeMixedSub ρ.dual i) :
    planeFacePairM ρ i x y = ∑ j, planeFacePairM ρ i
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) (e j) (fun k v => h j k v) x)
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) (e j).dualMap
        (fun k v => planeHeD ρ i (e j) (h j) k v) y) := by
  classical
  let a : J → planeMixedSub ρ i := fun j => ⟨_, planeMixedSub_h2E ρ i (e j) (h j) x hx⟩
  let b : J → planeMixedSub ρ.dual i := fun j => ⟨_, planeMixedSub_h2E_dual ρ i (e j) (h j) y hy⟩
  have hs1 : ∀ k v, (∑ j, e j) (ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) k) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) k) ((∑ j, e j) v) := fun k v => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun j _ => h j k v)
  have hxs : x = ∑ j, h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) (e j) (fun k v => h j k v) x := by
    rw [← h2E_finset_sum _ e (fun j k v => h j k v) Finset.univ (fun k v => hs1 k v) x]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun v => by rw [LinearMap.sum_apply]; exact hsum v)) _ (fun k v => rfl)]
    exact (h2E_id _ _ x).symm
  have hs2 : ∀ k (f : Module.Dual ℂ V), (∑ j, (e j).dualMap) (ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) k) f) =
      ρ.dual (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) k) ((∑ j, (e j).dualMap) f) := fun k f => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun j _ => planeHeD ρ i (e j) (h j) k f)
  have hys : y = ∑ j, h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) (e j).dualMap
      (fun k v => planeHeD ρ i (e j) (h j) k v) y := by
    rw [← h2E_finset_sum _ (fun j => (e j).dualMap) (fun j k v => planeHeD ρ i (e j) (h j) k v) Finset.univ
      (fun k v => hs2 k v) y]
    rw [h2E_congr _ (e' := LinearMap.id) (LinearMap.ext (fun f => LinearMap.ext (fun v => by
      change (∑ j, (e j).dualMap) f v = f v
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      change ∑ j, f (e j v) = f v
      rw [← map_sum, hsum]))) _ (fun k v => rfl)]
    exact (h2E_id _ _ y).symm
  have hxa : (⟨x, hx⟩ : planeMixedSub ρ i) = ∑ j, a j := Subtype.ext (by rw [Submodule.coe_sum]; exact hxs)
  have hyb : (⟨y, hy⟩ : planeMixedSub ρ.dual i) = ∑ j, b j := Subtype.ext (by rw [Submodule.coe_sum]; exact hys)
  have key : planeFacePairBil ρ i ⟨x, hx⟩ ⟨y, hy⟩ = ∑ j, planeFacePairBil ρ i (a j) (b j) := by
    rw [hxa, hyb]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · intro k _ hkj
      exact planeFacePairM_orth ρ i (e k) (e j) (h k) (h j) (horth k j hkj) x y hx hy
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  exact key

end PlaneFam
section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The Stokes relation at `Γ(6)` with the face pairings decomposed along families of orthogonal equivariant idempotents** (one family for each line face and each plane face). -/
theorem gamma6_stokes_decomposed
    (c : groupCohomology.H2 (Rep.of ρ)) (c' : groupCohomology.H2 (Rep.of ρ.dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ.dual) c' = 0)
    (J : LineFaces 6 → Type) [∀ i, Fintype (J i)] (eL : ∀ i, J i → V →ₗ[ℂ] V)
    (hL : ∀ (i : LineFaces 6) (j : J i) (t : gammaNQAt 6 i.rep) (v : V), eL i j (ρ (lineIncl i t) v) = ρ (lineIncl i t) (eL i j v))
    (hsumL : ∀ (i : LineFaces 6) (v : V), ∑ j, eL i j v = v) (horthL : ∀ (i : LineFaces 6) (j k : J i), j ≠ k → ∀ v : V, eL i k (eL i j v) = 0)
    (K : PlaneFaces 6 → Type) [∀ i, Fintype (K i)] (eP : ∀ i, K i → V →ₗ[ℂ] V)
    (hP : ∀ (i : PlaneFaces 6) (j : K i) (t : gammaNPAt 6 (planeFaceRepr i)) (v : V), eP i j (ρ (planeIncl i t) v) = ρ (planeIncl i t) (eP i j v))
    (hsumP : ∀ (i : PlaneFaces 6) (v : V), ∑ j, eP i j v = v) (horthP : ∀ (i : PlaneFaces 6) (j k : K i), j ≠ k → ∀ v : V, eP i k (eP i j v) = 0) :
    ∑ i : LineFaces 6, ∑ j, lineFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) (eL i j) (fun k v => hL i j k v)
          (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) (eL i j).dualMap
          (fun k v => lineHeD ρ i (eL i j) (hL i j) k v)
          (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) c')) +
      ∑ i : PlaneFaces 6, ∑ j, planeFacePairM ρ i
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)) (eP i j) (fun k v => hP i j k v)
          (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c))
        (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)) (eP i j).dualMap
          (fun k v => planeHeD ρ i (eP i j) (hP i j) k v)
          (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) c')) = 0 := by
  rw [← gamma6_stokes_of_zeroFlags ρ c c' hz hz']
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (lineFacePairM_decomp_family ρ i (eL i) (hL i) (hsumL i) (horthL i) _ _
      (lineMixedSub_of_zeroFlags ρ i c hz) (lineMixedSub_of_zeroFlags ρ.dual i c' hz')).symm
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (planeFacePairM_decomp_family ρ i (eP i) (hP i) (hsumP i) (horthP i) _ _
      (planeMixedSub_of_zeroFlags ρ i c hz) (planeMixedSub_of_zeroFlags ρ.dual i c' hz')).symm

end Main

end TernaryPeriodPolynomials.Argument.GammaNStokes
