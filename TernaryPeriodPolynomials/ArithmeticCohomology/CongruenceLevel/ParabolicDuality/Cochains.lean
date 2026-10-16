module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Equivariant
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.LinearAlgebra
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyNeighbours

@[expose] public section

/-!
# The Farey cochain complexes of a subgroup `Γ ≤ GL₂(ℤ)` and their pairings

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

The modular curve `Γ\ℍ` of a torsion-free `Γ ≤ GL₂(ℤ)` is triangulated by the Farey tessellation (ideal triangles = `Tri`, edges, cusps), and
retracts onto the dual trivalent graph.  Both cochain complexes are expressed on the Farey tree:
* `C0 ρ`: equivariant functions on triangles; `C1 ρ`: antisymmetric equivariant functions on oriented dual edges (= cochains on Farey edges);
* `delta : C0 → C1` (ordinary cohomology: `H¹(Γ, E) = C¹ / δ C⁰`), `dc : C1 → C0` (compactly supported cohomology: `H¹_c = ker d_c`, the
  triangle relation `∑_{q leaves t} F(q) = 0`; cusps carry zero cochains);
* `pair1_delta`: the two complexes are adjoint for the orbit pairing `⟨F, δH'⟩ = -2 ⟨d_c F, H'⟩` (this *is* the cusp relation / surface duality:
  every Farey triangle has three edges and every edge two triangles);
* `pair1_left_perfect`, `pair1_right_perfect`: the pairing `C¹(E) × C¹(E')` is perfect for a perfect invariant pairing `E × E' → ℂ`
  (the orbit sum over the representatives `FareyData.RE`, antisymmetrized by the self-adjoint swap).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

/-- Combinatorial data for a subgroup `Γ ≤ GL₂(ℤ)` acting on the Farey tree: a finite system of representatives of the triangles,
freeness of the action on triangles and no element reversing an oriented edge (both hold for torsion-free finite-index subgroups,
e.g. `Γ(N)`, `N ≥ 3`). -/
structure FareyData (Γ : Subgroup IntegralGL) where
  RT : RepSystem Γ Tri
  freeT : FreeAction Γ Tri
  noFlip : ∀ (γ : Γ) (q : OTE), γ • q ≠ q.swap

variable {Γ : Subgroup IntegralGL}

theorem FareyData.freeO (D : FareyData Γ) : FreeAction Γ OTE := by
  intro γ q h
  apply D.freeT
  have := congrArg (fun p : OTE => p.1.1) h
  exact this

/-- Representatives of the oriented edges: the edges leaving the representative triangles. -/
def FareyData.RE (D : FareyData Γ) : RepSystem Γ OTE where
  R := D.RT.R.biUnion nbF
  cover := by
    intro q
    obtain ⟨r, hr, γ, hγ⟩ := D.RT.cover q.1.1
    refine ⟨(γ⁻¹ : Γ) • q, Finset.mem_biUnion.mpr ⟨r, hr, ?_⟩, γ, by simp⟩
    rw [mem_nbF]
    change ((γ⁻¹ : Γ) : IntegralGL) • q.1.1 = r
    rw [← hγ]
    change (γ⁻¹ : IntegralGL) • ((γ : IntegralGL) • r) = r
    simp
  inj := by
    intro r hr r' hr' γ h
    obtain ⟨y, hy, hry⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨y', hy', hry'⟩ := Finset.mem_biUnion.mp hr'
    rw [mem_nbF] at hry hry'
    have h1 : γ • y = y' := by
      have := congrArg (fun p : OTE => p.1.1) h
      change (γ : IntegralGL) • r.1.1 = r'.1.1 at this
      rw [hry, hry'] at this
      exact this
    have h2 : y = y' := D.RT.inj y hy y' hy' γ h1
    subst h2
    have h3 : γ = 1 := D.freeT γ y h1
    rw [h3, one_smul] at h
    exact h

/-- Reversing the representatives. -/
def FareyData.RE' (D : FareyData Γ) : RepSystem Γ OTE where
  R := D.RE.R.image OTE.swap
  cover := by
    intro q
    obtain ⟨r, hr, γ, hγ⟩ := D.RE.cover q.swap
    refine ⟨r.swap, Finset.mem_image_of_mem _ hr, γ, ?_⟩
    have := congrArg OTE.swap hγ
    rw [OTE.swap_swap] at this
    rw [← this]
    exact (OTE.swap_smul (γ : IntegralGL) r).symm
  inj := by
    intro r hr r' hr' γ h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hr'
    have : γ • a = a' := by
      have h' := congrArg OTE.swap h
      rw [OTE.swap_swap] at h'
      rw [← h']
      rfl
    rw [D.RE.inj a ha a' ha' γ this]

section Complexes

variable {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ Γ E)

/-- Antisymmetric equivariant functions on oriented dual edges: the cochains `C¹` of the Farey tree (equivalently the Farey edges
with orientation-twisted coefficients). -/
def C1 : Submodule ℂ (OTE → E) where
  carrier := {F | F ∈ EqFn Γ OTE ρ ∧ ∀ q : OTE, F q.swap = -F q}
  add_mem' := fun {a b} ha hb => ⟨(EqFn Γ OTE ρ).add_mem ha.1 hb.1, fun q => by simp only [Pi.add_apply, ha.2 q, hb.2 q, neg_add]⟩
  zero_mem' := ⟨(EqFn Γ OTE ρ).zero_mem, fun q => by simp⟩
  smul_mem' := fun c {a} ha => ⟨(EqFn Γ OTE ρ).smul_mem c ha.1, fun q => by simp [ha.2 q]⟩

/-- Equivariant functions on triangles: the cochains `C⁰`. -/
abbrev C0 : Submodule ℂ (Tri → E) := EqFn Γ Tri ρ

/-- The coboundary `δ : C⁰ → C¹`, `(δH)(q) = H(q.2) - H(q.1)` (ordinary cohomology of `Γ` with coefficients in `E`). -/
def delta : C0 ρ →ₗ[ℂ] C1 ρ where
  toFun H := ⟨fun q => H.1 q.1.2 - H.1 q.1.1, fun γ q => by
      have h1 := H.2 γ q.1.2
      have h2 := H.2 γ q.1.1
      change H.1 ((γ : IntegralGL) • q.1.2) - H.1 ((γ : IntegralGL) • q.1.1) =
        ρ γ (H.1 q.1.2 - H.1 q.1.1)
      rw [map_sub]
      exact congrArg₂ (· - ·) h1 h2, fun q => by
      change H.1 q.1.1 - H.1 q.1.2 = -(H.1 q.1.2 - H.1 q.1.1)
      abel⟩
  map_add' H H' := by
    apply Subtype.ext
    funext q
    change (H.1 + H'.1) q.1.2 - (H.1 + H'.1) q.1.1 = _
    simp only [Pi.add_apply]
    change _ = (H.1 q.1.2 - H.1 q.1.1) + (H'.1 q.1.2 - H'.1 q.1.1)
    abel
  map_smul' c H := by
    apply Subtype.ext
    funext q
    change c • H.1 q.1.2 - c • H.1 q.1.1 = c • (H.1 q.1.2 - H.1 q.1.1)
    rw [smul_sub]

theorem delta_apply (H : C0 ρ) (q : OTE) : (delta ρ H).1 q = H.1 q.1.2 - H.1 q.1.1 := rfl

/-- The compactly supported coboundary `d_c : C¹ → C⁰`, `(d_c F)(t) = ∑_{q leaves t} F(q)` (the triangle relation of the
Farey cells). -/
def dc : C1 ρ →ₗ[ℂ] C0 ρ where
  toFun F := ⟨fun t => ∑ q ∈ nbF t, F.1 q, fun γ t => by
      change ∑ q ∈ nbF ((γ : IntegralGL) • t), F.1 q = ρ γ (∑ q ∈ nbF t, F.1 q)
      rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective (γ : IntegralGL) h), map_sum]
      exact Finset.sum_congr rfl fun q _ => F.2.1 γ q⟩
  map_add' F F' := by
    apply Subtype.ext
    funext t
    change ∑ q ∈ nbF t, (F.1 + F'.1) q = _
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext t
    change ∑ q ∈ nbF t, c • F.1 q = c • ∑ q ∈ nbF t, F.1 q
    rw [Finset.smul_sum]

theorem dc_apply (F : C1 ρ) (t : Tri) : (dc ρ F).1 t = ∑ q ∈ nbF t, F.1 q := rfl

end Complexes

section Pairings

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  {ρ : Representation ℂ Γ E} {ρ' : Representation ℂ Γ E'} (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)

/-- The orbit-sum bilinear form. -/
def pairBil {X : Type} [MulAction Γ X] (S : RepSystem Γ X) : (X → E) →ₗ[ℂ] (X → E') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun F G => pairR e S F G)
    (fun F F' G => by simp [pairR, Finset.sum_add_distrib])
    (fun c F G => by simp [pairR, Finset.mul_sum])
    (fun F G G' => by simp [pairR, Finset.sum_add_distrib])
    (fun c F G => by simp [pairR, Finset.mul_sum])

theorem pairBil_apply {X : Type} [MulAction Γ X] (S : RepSystem Γ X) (F : X → E) (G : X → E') :
    pairBil e S F G = pairR e S F G := rfl

theorem sum_RE (D : FareyData Γ) (φ : OTE → ℂ) :
    ∑ r ∈ D.RE.R, φ r = ∑ y ∈ D.RT.R, ∑ q ∈ nbF y, φ q := by
  unfold FareyData.RE
  rw [Finset.sum_biUnion]
  intro y _ y' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro q hq hq'
  rw [mem_nbF] at hq hq'
  exact hne (hq.symm.trans hq')

variable (he : ∀ (γ : Γ) v w, e (ρ γ v) (ρ' γ w) = e v w)
include he

/-- The swap on oriented edges is self-adjoint for the orbit pairing. -/
theorem pair_swap_adjoint (D : FareyData Γ) {F : OTE → E} {G : OTE → E'} (hF : F ∈ EqFn Γ OTE ρ) (hG : G ∈ EqFn Γ OTE ρ') :
    pairR e D.RE (fun q => F q.swap) G = pairR e D.RE F (fun q => G q.swap) := by
  have hψ : ∀ (γ : Γ) (x : OTE), e (F (γ • x).swap) (G (γ • x)) = e (F x.swap) (G x) := by
    intro γ x
    have : (γ • x).swap = γ • x.swap := OTE.swap_smul (γ : IntegralGL) x
    rw [this, hF γ, hG γ, he]
  unfold pairR
  rw [sum_rep_indep D.freeO D.RE D.RE' (fun x => e (F x.swap) (G x)) hψ]
  unfold FareyData.RE'
  rw [Finset.sum_image (fun a _ b _ h => by simpa using congrArg OTE.swap h)]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp

omit he in
/-- The sum of `⟨F(r), H'(source r)⟩` over the edge representatives is the triangle pairing with `d_c F`. -/
theorem pair_source (D : FareyData Γ) (F : C1 ρ) (H' : C0 ρ') :
    ∑ r ∈ D.RE.R, e (F.1 r) (H'.1 r.1.1) = pairR e D.RT (dc ρ F).1 H'.1 := by
  rw [sum_RE D (fun r : OTE => e (F.1 r) (H'.1 r.1.1))]
  unfold pairR
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dc_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_nbF] at hq
  rw [hq]

/-- **Adjointness**: `⟨F, δ H'⟩_{C¹} = -2 ⟨d_c F, H'⟩_{C⁰}`. -/
theorem pair1_delta (D : FareyData Γ) (F : C1 ρ) (H' : C0 ρ') :
    pairR e D.RE F.1 (delta ρ' H').1 = -2 * pairR e D.RT (dc ρ F).1 H'.1 := by
  have hψ : ∀ (γ : Γ) (x : OTE), e (F.1 (γ • x)) (H'.1 (γ • x).1.2) = e (F.1 x) (H'.1 x.1.2) := by
    intro γ x
    rw [F.2.1 γ x]
    change e (ρ γ (F.1 x)) (H'.1 (γ • x.1.2)) = e (F.1 x) (H'.1 x.1.2)
    rw [H'.2 γ x.1.2, he]
  have h1 : ∑ r ∈ D.RE.R, e (F.1 r) (H'.1 r.1.2) = -pairR e D.RT (dc ρ F).1 H'.1 := by
    rw [sum_rep_indep D.freeO D.RE D.RE' _ hψ]
    unfold FareyData.RE'
    rw [Finset.sum_image (fun a _ b _ h => by simpa using congrArg OTE.swap h), ← pair_source e D F H',
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : F.1 r.swap = -F.1 r := F.2.2 r
    change e (F.1 r.swap) (H'.1 r.1.1) = -e (F.1 r) (H'.1 r.1.1)
    rw [this, map_neg, LinearMap.neg_apply]
  unfold pairR
  have h2 : ∀ r : OTE, e (F.1 r) ((delta ρ' H').1 r) = e (F.1 r) (H'.1 r.1.2) - e (F.1 r) (H'.1 r.1.1) := by
    intro r
    rw [delta_apply, map_sub]
  simp only [h2, Finset.sum_sub_distrib]
  rw [h1, pair_source e D F H']
  unfold pairR
  ring

omit he in
/-- The antisymmetrization of an equivariant function is a `C¹` cochain. -/
theorem antisym_mem (G : OTE → E') (hG : G ∈ EqFn Γ OTE ρ') : (fun q => (1 / 2 : ℂ) • (G q - G q.swap)) ∈ C1 ρ' := by
  refine ⟨fun γ q => ?_, fun q => ?_⟩
  · change (1 / 2 : ℂ) • (G (γ • q) - G ((γ • q).swap)) = ρ' γ ((1 / 2 : ℂ) • (G q - G q.swap))
    have : (γ • q).swap = γ • q.swap := OTE.swap_smul (γ : IntegralGL) q
    rw [this, hG γ q, hG γ q.swap, map_smul, map_sub]
  · change (1 / 2 : ℂ) • (G q.swap - G q.swap.swap) = -((1 / 2 : ℂ) • (G q - G q.swap))
    rw [OTE.swap_swap, ← smul_neg, neg_sub]

theorem pair1_left_perfect (D : FareyData Γ) (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (F : C1 ρ)
    (h : ∀ G : C1 ρ', pairR e D.RE F.1 G.1 = 0) : F = 0 := by
  apply Subtype.ext
  refine pairR_left_perfect ρ ρ' e D.RE D.freeO hL F.2.1 ?_
  intro G hG
  have h1 := h ⟨_, antisym_mem G hG⟩
  have h2 := pair_swap_adjoint e he D F.2.1 hG
  have h3 : (fun q : OTE => F.1 q.swap) = -F.1 := funext fun q => F.2.2 q
  rw [h3] at h2
  have h4 : pairR e D.RE (-F.1) G = -pairR e D.RE F.1 G := by
    rw [← pairBil_apply, ← pairBil_apply, map_neg, LinearMap.neg_apply]
  rw [h4] at h2
  change pairR e D.RE F.1 (fun q => (1 / 2 : ℂ) • (G q - G q.swap)) = 0 at h1
  have h5 : pairR e D.RE F.1 (fun q => (1 / 2 : ℂ) • (G q - G q.swap)) =
      (1 / 2 : ℂ) * (pairR e D.RE F.1 G - pairR e D.RE F.1 (fun q => G q.swap)) := by
    have : (fun q => (1 / 2 : ℂ) • (G q - G q.swap)) = (1 / 2 : ℂ) • (G - fun q => G q.swap) := rfl
    rw [this, ← pairBil_apply, map_smul, map_sub, ← pairBil_apply, ← pairBil_apply, smul_eq_mul]
  rw [h5, ← h2] at h1
  have : pairR e D.RE F.1 G = 0 := by
    have h6 : (1 / 2 : ℂ) * (pairR e D.RE F.1 G - -pairR e D.RE F.1 G) = 0 := h1
    have : (1 / 2 : ℂ) * (pairR e D.RE F.1 G - -pairR e D.RE F.1 G) = pairR e D.RE F.1 G := by ring
    rwa [this] at h6
  exact this

omit he in
/-- The antisymmetrization of an equivariant function (first factor). -/
theorem antisym_mem' (F : OTE → E) (hF : F ∈ EqFn Γ OTE ρ) :
    (fun q => (1 / 2 : ℂ) • (F q - F q.swap)) ∈ C1 ρ :=
  antisym_mem F hF

theorem pair1_right_perfect (D : FareyData Γ) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) (G : C1 ρ')
    (h : ∀ F : C1 ρ, pairR e D.RE F.1 G.1 = 0) : G = 0 := by
  apply Subtype.ext
  refine pairR_right_perfect ρ ρ' e D.RE D.freeO hR G.2.1 ?_
  intro F hF
  have h1 := h ⟨_, antisym_mem' F hF⟩
  have h2 := pair_swap_adjoint e he D hF G.2.1
  have h3 : (fun q : OTE => G.1 q.swap) = -G.1 := funext fun q => G.2.2 q
  rw [h3] at h2
  have h4 : pairR e D.RE F (-G.1) = -pairR e D.RE F G.1 := by
    rw [← pairBil_apply, ← pairBil_apply, map_neg]
  rw [h4] at h2
  change pairR e D.RE (fun q => (1 / 2 : ℂ) • (F q - F q.swap)) G.1 = 0 at h1
  have h5 : pairR e D.RE (fun q => (1 / 2 : ℂ) • (F q - F q.swap)) G.1 =
      (1 / 2 : ℂ) * (pairR e D.RE F G.1 - pairR e D.RE (fun q => F q.swap) G.1) := by
    have : (fun q => (1 / 2 : ℂ) • (F q - F q.swap)) = (1 / 2 : ℂ) • (F - fun q => F q.swap) := rfl
    rw [this, ← pairBil_apply, map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, ← pairBil_apply,
      ← pairBil_apply, smul_eq_mul]
  rw [h5, h2] at h1
  have h6 : (1 / 2 : ℂ) * (pairR e D.RE F G.1 - -pairR e D.RE F G.1) = 0 := h1
  have : (1 / 2 : ℂ) * (pairR e D.RE F G.1 - -pairR e D.RE F G.1) = pairR e D.RE F G.1 := by ring
  rwa [this] at h6

end Pairings

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
