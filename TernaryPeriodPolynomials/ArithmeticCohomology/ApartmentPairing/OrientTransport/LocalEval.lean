module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.AffineAW
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.AffineSimplex
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Thom
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ThomR2
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricBoundaryCancellation
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains

@[expose] public section



/-!
# Orientation transport: the Alexander-Whitney cap of the product simplex

Let `σ₀` be the affine 5-simplex of `ℝ³ × ℝ²` with vertices
`(0, 3b₀), (0, 3b₁), (4a₂, 3b₂), (4a₃, 0), (4a₄, 0), (4a₅, 0)` where `(a₂, a₃, a₄, a₅) = (e₂, e₁, e₃, -(e₁+e₂+e₃))` is the
reference tetrahedron `rv` of `Orient.AffineSimplex` (local degree `lamPos`) and `(b₀, b₁, b₂) = ((1,0),(0,1),(-1,-1))` the
reference triangle (`sigma0V`).  The first three vertices project to the triangle `rtri` (scale `3`), the last four to
the tetrahedron `tetraV` (scale `4`), and the barycentre of `σ₀` is the origin.

* `faceSimplex_affSimp`, `boundary_affSimp_mem`: faces of affine simplices, and boundaries of affine simplices lie in the
  chains subordinate to a set containing all their faces.
* `tetra_face_far`, `tri_face_far`: the faces of `tetraV` and the edges of `rtri` lie outside the unit ball (explicit
  separating functionals).
* `thom3_tetra`, `thom2_tri`: a Thom cochain of `ℝ³` (resp. `ℝ²`) of radius `1` takes the value `lamPos` (resp. `lam2`,
  the local degree of the reference triangle) on them.
* **`aw_value_sigma0`**: for Thom cochains `y₀`, `θ₀` pulled back along the two projections, the Alexander-Whitney
  pairing `y(back σ₀) · θ(front σ₀)` of the product simplex is `lamPos · lam2`
  (`capPair_generator`: `capPair y φ σ = y(backSimplex σ) • φ(frontSimplex σ)`).

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPeriodPolynomials.Argument.Lemma33.Locality


variable {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]

theorem faceSimplex_affSimp (n : ℕ) (k : Fin (n + 2)) (w : Fin (n + 2) → V) :
    faceSimplex (TopCat.of V) n k (affSimp (n + 1) w) = affSimp n (fun i => w (k.succAbove i)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of V) (Opposite.op (SimplexCategory.mk n))).injective
  have h := faceSimplex_continuousMap (TopCat.of V) n k (affSimp (n + 1) w)
  change singularSimplexAsContinuousMap (TopCat.of V) n _ = singularSimplexAsContinuousMap (TopCat.of V) n _
  rw [h, asContinuousMap_affSimp, asContinuousMap_affSimp]
  apply ContinuousMap.ext
  intro x
  change ∑ j, (Convexity.StdSimplex.map k.succAbove x : Delta (n + 1)).weights j • w j =
    ∑ i, x.weights i • w (k.succAbove i)
  exact sum_map_smul _ x w

theorem isSubordinate_affSimp {S : Set V} {n : ℕ} {w : Fin (n + 1) → V}
    (h : ∀ t, affMapN n w t ∈ S) : IsSubordinate S (affSimp n w) := by
  rintro _ ⟨t, rfl⟩
  have : mvSimplexMap (affSimp n w) = affMapN n w := asContinuousMap_affSimp n w
  rw [this]
  exact h t

theorem boundary_affSimp_mem (S : Set V) (n : ℕ) (w : Fin (n + 2) → V)
    (h : ∀ k : Fin (n + 2), ∀ t, affMapN n (fun i => w (k.succAbove i)) t ∈ S) :
    (singularBoundary ℚ (TopCat.of V) n).hom (chainGenerator ℚ (TopCat.of V) (n + 1) (affSimp (n + 1) w)) ∈
      subChainSubmodule ℚ (TopCat.of V) S n := by
  rw [singularBoundary_chainGenerator_formula]
  refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
  rw [faceSimplex_affSimp]
  exact chainGenerator_mem_subChainSubmodule (isSubordinate_affSimp (h k))

theorem norm_gt_one_of3 (x : E3) (a b c h : ℝ) (hlin : a * x 0 + b * x 1 + c * x 2 = h)
    (hh : a ^ 2 + b ^ 2 + c ^ 2 < h ^ 2) : 1 < ‖x‖ := by
  by_contra hcon
  have hn : ‖x‖ ≤ 1 := not_lt.mp hcon
  have hsq : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three]
  have h1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hcs : (a * x 0 + b * x 1 + c * x 2) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
    nlinarith [sq_nonneg (a * x 1 - b * x 0), sq_nonneg (a * x 2 - c * x 0), sq_nonneg (b * x 2 - c * x 1)]
  rw [hlin, hsq] at hcs
  have hpos : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos]

theorem norm_gt_one_of2 (x : R2) (a b h : ℝ) (hlin : a * x 0 + b * x 1 = h)
    (hh : a ^ 2 + b ^ 2 < h ^ 2) : 1 < ‖x‖ := by
  by_contra hcon
  have hn : ‖x‖ ≤ 1 := not_lt.mp hcon
  have hsq : x 0 ^ 2 + x 1 ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  have h1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hcs : (a * x 0 + b * x 1) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by
    nlinarith [sq_nonneg (a * x 1 - b * x 0)]
  rw [hlin, hsq] at hcs
  have hpos : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos]

theorem tetra_face_far (k : Fin 4) (t : Delta 2) :
    1 < ‖affMapN 2 (fun i => rref (fun _ => 4) (k.succAbove i)) t‖ := by
  have hs : ∑ i, t.weights i = 1 := t.total_of_fintype
  rw [Fin.sum_univ_three] at hs
  have h0 : 0 ≤ t.weights 0 := t.weights_nonneg 0
  have h1 : 0 ≤ t.weights 1 := t.weights_nonneg 1
  have h2 : 0 ≤ t.weights 2 := t.weights_nonneg 2
  fin_cases k
  · refine norm_gt_one_of3 _ 1 (-3) 1 4 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_three, rref, rv, mk3, Fin.succAbove]
    linear_combination 4 * hs
  · refine norm_gt_one_of3 _ (-3) 1 1 4 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_three, rref, rv, mk3, Fin.succAbove]
    linear_combination 4 * hs
  · refine norm_gt_one_of3 _ 1 1 (-3) 4 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_three, rref, rv, mk3, Fin.succAbove]
    linear_combination 4 * hs
  · refine norm_gt_one_of3 _ 1 1 1 4 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_three, rref, rv, mk3, Fin.succAbove]
    linear_combination 4 * hs

/-- The point `(a, b)` of the plane. -/
def mk2 (a b : ℝ) : R2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![a, b]

@[simp] theorem mk2_zero (a b : ℝ) : mk2 a b 0 = a := rfl
@[simp] theorem mk2_one (a b : ℝ) : mk2 a b 1 = b := rfl

/-- The reference triangle `((1,0), (0,1), (-1,-1))` with centroid at the origin. -/
def rt : Fin 3 → R2 := ![mk2 1 0, mk2 0 1, mk2 (-1) (-1)]

/-- The reference triangle scaled by `3`, so that its edges avoid the unit disc. -/
def rtri : Fin 3 → R2 := fun k => (3 : ℝ) • rt k

theorem tri_face_far (k : Fin 3) (t : Delta 1) :
    1 < ‖affMapN 1 (fun i => rtri (k.succAbove i)) t‖ := by
  have hs : ∑ i, t.weights i = 1 := t.total_of_fintype
  rw [Fin.sum_univ_two] at hs
  fin_cases k
  · refine norm_gt_one_of2 _ (-2) 1 3 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_two, rtri, rt, mk2, Fin.succAbove]
    linear_combination 3 * hs
  · refine norm_gt_one_of2 _ 1 (-2) 3 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_two, rtri, rt, mk2, Fin.succAbove]
    linear_combination 3 * hs
  · refine norm_gt_one_of2 _ 1 1 3 ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_two, rtri, rt, mk2, Fin.succAbove]
    linear_combination 3 * hs

theorem degR3_affSimp (W : Fin (3 + 1) → E3) (hW : FacesAvoid W)
    (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom (chainGenerator ℚ (TopCat.of R3) 3 (affSimp 3 W))) = 0) :
    degR3 (chainGenerator ℚ (TopCat.of R3) 3 (affSimp 3 W)) h = degAff W hW := by
  rfl

theorem unitBall_compl_subset3 : ({v : R3 | 1 < ‖v‖} : Set R3) ⊆ (({0} : Set R3)ᶜ) := by
  intro v hv h0
  rw [Set.mem_singleton_iff.mp h0] at hv
  have h1 : (1 : ℝ) < ‖(0 : R3)‖ := hv
  rw [norm_zero] at h1
  exact absurd h1 (by norm_num)

theorem unitBall_compl_subset2 : ({v : R2 | 1 < ‖v‖} : Set R2) ⊆ (({0} : Set R2)ᶜ) := by
  intro v hv h0
  rw [Set.mem_singleton_iff.mp h0] at hv
  have h1 : (1 : ℝ) < ‖(0 : R2)‖ := hv
  rw [norm_zero] at h1
  exact absurd h1 (by norm_num)

/-- The reference tetrahedron scaled by `4`: its faces avoid the unit ball. -/
def tetraV : Fin (3 + 1) → R3 := rref (fun _ => 4)

theorem tetra_boundary_mem :
    (singularBoundary ℚ (TopCat.of R3) 2).hom (chainGenerator ℚ (TopCat.of R3) 3 (affSimp 3 tetraV)) ∈
      subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 :=
  boundary_affSimp_mem _ 2 tetraV (fun k t => tetra_face_far k t)

theorem tri_boundary_mem :
    (singularBoundary ℚ (TopCat.of R2) 1).hom (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) ∈
      subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 :=
  boundary_affSimp_mem _ 1 rtri (fun k t => tri_face_far k t)

/-- The local degree of the reference triangle (scale `3`) around the origin of the plane. -/
def lam2 : ℚ :=
  degR2 (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri))
    (locR2_cycle_of_boundary_mem unitBall_compl_subset2 tri_boundary_mem)

/-- A Thom cochain of `ℝ³` (radius `1`) takes the value `lamPos` on the scaled reference tetrahedron. -/
theorem thom3_tetra (y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ)
    (hy : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₀ c = degR3 c h) :
    y₀ (chainGenerator ℚ (TopCat.of R3) 3 (affSimp 3 tetraV)) = lamPos := by
  obtain ⟨h, h'⟩ := hy _ tetra_boundary_mem
  rw [h', degR3_affSimp tetraV (rref_facesAvoid _ (fun _ => by norm_num)) h]
  exact degAff_rref _ (fun _ => by norm_num)

/-- A Thom cochain of `ℝ²` (radius `1`) takes the value `lam2` on the scaled reference triangle. -/
theorem thom2_tri (θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ)
    (hθ : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 →
      ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₀ c = degR2 c h) :
    θ₀ (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) = lam2 := by
  obtain ⟨h, h'⟩ := hθ _ tri_boundary_mem
  rw [h']
  rfl

/-- The vertices of the product simplex `σ₀` in `ℝ³ × ℝ²`: the first three project to the reference triangle, the last
four to the reference tetrahedron, and the barycentre is the origin. -/
def sigma0V : Fin (5 + 1) → R3 × R2 :=
  ![(0, rtri 0), (0, rtri 1), (tetraV 0, rtri 2), (tetraV 1, 0), (tetraV 2, 0), (tetraV 3, 0)]

/-- The scalar action on `ℝ³ × ℝ²` is continuous (stated once, so that instance search does not
have to rediscover it from the normed-space structures at each use). -/
local instance continuousSMul_R3_R2 : ContinuousSMul ℝ (R3 × R2) := Prod.continuousSMul

/-- The first projection of `ℝ³ × ℝ²` as a morphism of spaces. -/
def piHom : TopCat.of (R3 × R2) ⟶ TopCat.of R3 := TopCat.ofHom ⟨(LinearMap.fst ℝ R3 R2), continuous_fst⟩

/-- The second projection of `ℝ³ × ℝ²` as a morphism of spaces. -/
def rhoHom : TopCat.of (R3 × R2) ⟶ TopCat.of R2 := TopCat.ofHom ⟨(LinearMap.snd ℝ R3 R2), continuous_snd⟩

theorem pi_back_sigma0 :
    pushSimplex piHom 3 (backSimplex (TopCat.of (R3 × R2)) 2 3 (affSimp (2 + 3) sigma0V)) =
      affSimp 3 tetraV := by
  rw [backSimplex_affSimp]
  have := pushSimplex_affSimp (V := R3 × R2) (W := R3) (LinearMap.fst ℝ R3 R2) continuous_fst 3
    (fun i => sigma0V ⟨i.val + 2, by omega⟩)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [sigma0V]

theorem rho_front_sigma0 :
    pushSimplex rhoHom 2 (frontSimplex (TopCat.of (R3 × R2)) 2 3 (affSimp (2 + 3) sigma0V)) =
      affSimp 2 rtri := by
  rw [frontSimplex_affSimp]
  have := pushSimplex_affSimp (V := R3 × R2) (W := R2) (LinearMap.snd ℝ R3 R2) continuous_snd 2
    (fun i => sigma0V (Fin.castLE (by omega) i))
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [sigma0V]

/-- **The Alexander-Whitney cap of the product simplex.**  For Thom cochains `y₀` of `ℝ³` and `θ₀` of `ℝ²` (radius `1`),
pulled back to `ℝ³ × ℝ²` along the two projections, the product `y(back σ₀) · θ(front σ₀)` of their values on the back
and front faces of the product simplex `σ₀` is `lamPos · lam2`. -/
theorem aw_value_sigma0 (y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ)
    (hy : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₀ c = degR3 c h)
    (θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ)
    (hθ : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 →
      ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₀ c = degR2 c h) :
    y₀ ((singularChainMap ℚ piHom 3).hom
        (chainGenerator ℚ (TopCat.of (R3 × R2)) 3
          (backSimplex (TopCat.of (R3 × R2)) 2 3 (affSimp (2 + 3) sigma0V)))) *
      θ₀ ((singularChainMap ℚ rhoHom 2).hom
        (chainGenerator ℚ (TopCat.of (R3 × R2)) 2
          (frontSimplex (TopCat.of (R3 × R2)) 2 3 (affSimp (2 + 3) sigma0V)))) = lamPos * lam2 := by
  rw [singularChainMap_generator, singularChainMap_generator, pi_back_sigma0, rho_front_sigma0,
    thom3_tetra y₀ hy, thom2_tri θ₀ hθ]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
