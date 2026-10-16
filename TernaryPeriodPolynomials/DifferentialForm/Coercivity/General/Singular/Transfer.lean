module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Intrinsic

@[expose] public section


/-!
# Restriction, transfer and induction for the degree-two vanishing, in the function model

Let `φ : H →* G` be a homomorphism whose range has finite index, with `H` and `G` acting on a
space `E` compatibly (`h • x = φ h • x`).  For equivariant simplex functions (the model of
`Singular/Intrinsic`):
* `funVanish_of_res`: vanishing of `FunVanish` for the restricted coefficients `Rep.res φ V` on
  `H` implies vanishing for `V` on `G` (averaging over the cosets; characteristic zero);
* `funVanish_res_of_ind`: vanishing for the induced coefficients `indRep φ V` on `G` implies
  vanishing for `Rep.res φ V` on `H` (Shapiro: evaluate at the trivial coset), for supports
  `S' ⊇ S` with `S` `G`-invariant.
Here `FunVanish S` says: every closed equivariant degree-two simplex function that vanishes on the
simplices subordinate to the set `S` (the zero, or exterior, region) is the coboundary of an
equivariant one-cochain.  For the covering `p`, `compactForget` corresponds to the regions
`S = p⁻¹(Kᶜ)` with `K` compact.  In `funVanish_res_of_ind` the inclusion `S ⊆ S'` is a condition on
these zero regions, not on compact supports: a cochain that vanishes ON the simplices subordinate to
the larger zero region `S'` vanishes, in particular, on the simplices subordinate to the `G`-invariant
region `S`.  Both lemmas are finite sums and group manipulations; no topology enters.

Formalized by Claude Sonnet 5.5.
-/


open CategoryTheory
open scoped Simplicial

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularCohomology
  TernaryPoly.EquivariantSingularSmall SphereOddDegree

section Faces

variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]

/-- Faces of singular simplices are equivariant for the deck action. -/
theorem face_smul {n : ℕ} (i : Fin (n + 2)) (g : G) (σ : SingularSimplex E (n + 1)) :
    (TopCat.toSSet.obj E).δ i (g • σ) = g • (TopCat.toSSet.obj E).δ i σ := by
  rw [singular_smul_eq_map G E, singular_smul_eq_map G E]
  exact (congrFun (congrArg (fun f => f.hom) ((TopCat.toSSet.map (scalarMap G E g)).naturality
    (SimplexCategory.δ i).op)).symm σ)

end Faces


section Transfer

variable {G H : Type} [Group G] [Group H] (φ : H →* G)
  {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [MulAction H E] [ContinuousConstSMul H E]
  (hact : ∀ (h : H) (x : E), h • x = φ h • x)

include hact in
theorem simplex_smul_hact (n : ℕ) (h : H) (σ : SingularSimplex E n) : h • σ = φ h • σ := by
  apply (TopCat.toSSetObjEquiv E (.op ⦋n⦌)).injective
  rw [singularEquiv_smul, singularEquiv_smul]
  ext x
  exact hact h _


variable (V : Rep.{0} ℚ G)

/-- Restriction to a subgroup of an equivariant simplex function. -/
def resEF (n : ℕ) (f : equivariantFunctions G E V n) :
    equivariantFunctions H E (Rep.res φ V) n :=
  ⟨f.val, fun h σ => by
    rw [simplex_smul_hact φ hact]
    exact f.property (φ h) σ⟩

/-- A function of `r : G` constant on cosets of `φ.range` descends to the quotient. -/
def liftTerm (F : G → V) (hF : ∀ (r : G) (h : H), F (r * φ h) = F r) : G ⧸ φ.range → V :=
  Quotient.lift (s := QuotientGroup.leftRel φ.range) F (fun r1 r2 hr => by
    obtain ⟨h, hh⟩ := QuotientGroup.leftRel_apply.mp hr
    have : r2 = r1 * φ h := by rw [hh]; group
    rw [this, hF])

theorem liftTerm_mk (F : G → V) (hF : ∀ (r : G) (h : H), F (r * φ h) = F r) (r : G) :
    liftTerm φ V F hF (QuotientGroup.mk r) = F r := rfl


variable {V}

include hact in
/-- The `G`-equivariant lift of an `H`-equivariant simplex function: `σ ↦ (rK ↦ r · f(r⁻¹σ))`. -/
def indFun {n : ℕ} (f : equivariantFunctions H E (Rep.res φ V) n) (σ : SingularSimplex E n) :
    G ⧸ φ.range → V :=
  liftTerm φ V (fun r => V.ρ r (f.val (r⁻¹ • σ))) (fun r h => by
    have h1 : (r * φ h)⁻¹ • σ = h⁻¹ • (r⁻¹ • σ) := by
      rw [simplex_smul_hact φ hact, mul_inv_rev, map_inv, mul_smul]
    have h2 := f.property h⁻¹ (r⁻¹ • σ)
    change V.ρ (r * φ h) (f.val ((r * φ h)⁻¹ • σ)) = V.ρ r (f.val (r⁻¹ • σ))
    rw [h1, h2]
    change V.ρ (r * φ h) (V.ρ (φ h⁻¹) (f.val (r⁻¹ • σ))) = _
    rw [← Module.End.mul_apply, ← map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one])

theorem indFun_mk {n : ℕ} (f : equivariantFunctions H E (Rep.res φ V) n) (σ : SingularSimplex E n)
    (r : G) : indFun φ hact f σ (QuotientGroup.mk r) = V.ρ r (f.val (r⁻¹ • σ)) := rfl


variable (V)

/-- The induced (coinduced) representation `G ⧸ φ(H) → V`, `(γ w)(q) = γ · w(γ⁻¹ q)`. -/
def indRepresentation : Representation ℚ G ((G ⧸ φ.range) → V) where
  toFun γ :=
    { toFun := fun w q => V.ρ γ (w (γ⁻¹ • q))
      map_add' := fun w w' => by funext q; simp
      map_smul' := fun c w => by funext q; simp }
  map_one' := by
    apply LinearMap.ext
    intro w
    funext q
    simp
  map_mul' γ δ := by
    apply LinearMap.ext
    intro w
    funext q
    change V.ρ (γ * δ) (w ((γ * δ)⁻¹ • q)) = V.ρ γ (V.ρ δ (w (δ⁻¹ • γ⁻¹ • q)))
    rw [mul_inv_rev, mul_smul, map_mul]
    rfl

/-- The induced representation as an object of `Rep ℚ G`. -/
abbrev indRep : Rep.{0} ℚ G := Rep.of (indRepresentation φ V)

instance indRep_finiteDimensional [Finite (G ⧸ φ.range)] [FiniteDimensional ℚ V] :
    FiniteDimensional ℚ (indRep φ V) := by
  have := Fintype.ofFinite (G ⧸ φ.range)
  exact inferInstanceAs (FiniteDimensional ℚ ((G ⧸ φ.range) → V))

variable {V}

include hact in
theorem indFun_smul {n : ℕ} (f : equivariantFunctions H E (Rep.res φ V) n) (γ : G)
    (σ : SingularSimplex E n) :
    indFun φ hact f (γ • σ) = (indRep φ V).ρ γ (indFun φ hact f σ) := by
  funext q
  induction q using QuotientGroup.induction_on with
  | H r =>
    change V.ρ r (f.val (r⁻¹ • γ • σ)) = V.ρ γ (indFun φ hact f σ (γ⁻¹ • QuotientGroup.mk r))
    have : γ⁻¹ • (QuotientGroup.mk r : G ⧸ φ.range) = QuotientGroup.mk (γ⁻¹ * r) := rfl
    rw [this, indFun_mk]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left, mul_smul]


include hact in
/-- **Shapiro, in the function model.**  Vanishing for the induced coefficients on the larger group,
with respect to a `G`-invariant zero region `S`, gives vanishing for the subgroup with respect to
any zero region `S'` containing `S` (a cochain that vanishes ON the simplices subordinate to the
larger zero region `S'` vanishes, in particular, on the simplices subordinate to `S`). -/
theorem funVanish_res_of_ind (S S' : Set E) (hS : InvariantSet G E S) (hSS : S ⊆ S')
    (H' : FunVanish (G := G) (E := E) (indRep φ V) S) :
    FunVanish (G := H) (E := E) (Rep.res φ V) S' := by
  intro f' hcl hvan
  let fhat : equivariantFunctions G E (indRep φ V) 2 :=
    ⟨fun σ => indFun φ hact f' σ, fun γ σ => indFun_smul φ hact f' γ σ⟩
  obtain ⟨ĝ, hĝ⟩ := H' fhat (by
    intro τ
    funext q
    induction q using QuotientGroup.induction_on with
    | H r =>
      simp only [Finset.sum_apply, Pi.smul_apply]
      have h1 : ∀ i : Fin 4, indFun φ hact f' ((TopCat.toSSet.obj E).δ i τ) (QuotientGroup.mk r) =
          V.ρ r (f'.val ((TopCat.toSSet.obj E).δ i (r⁻¹ • τ))) := fun i => by
        rw [indFun_mk, face_smul]
      change ∑ x : Fin 4, (-1 : ℤ) ^ x.val • indFun φ hact f' ((TopCat.toSSet.obj E).δ x τ)
        (QuotientGroup.mk r) = (0 : (G ⧸ φ.range) → V) (QuotientGroup.mk r)
      simp only [h1]
      have h2 : ∑ x : Fin 4, (-1 : ℤ) ^ x.val • V.ρ r (f'.val ((TopCat.toSSet.obj E).δ x (r⁻¹ • τ))) =
          V.ρ r (∑ x : Fin 4, (-1 : ℤ) ^ x.val • f'.val ((TopCat.toSSet.obj E).δ x (r⁻¹ • τ))) := by
        simp only [map_sum, map_zsmul]
      rw [h2, hcl (r⁻¹ • τ), map_zero]
      rfl) (by
    intro σ hσ
    funext q
    induction q using QuotientGroup.induction_on with
    | H r =>
      change V.ρ r (f'.val (r⁻¹ • σ)) = 0
      rw [hvan (r⁻¹ • σ) ((subordinate_invariant G E S hS 2 r⁻¹ σ hσ).mono hSS), map_zero])
  refine ⟨⟨fun σ => ĝ.val σ (QuotientGroup.mk 1), fun h σ => ?_⟩, fun σ => ?_⟩
  · change ĝ.val (h • σ) (QuotientGroup.mk 1) = V.ρ (φ h) (ĝ.val σ (QuotientGroup.mk 1))
    rw [simplex_smul_hact φ hact, ĝ.property (φ h) σ]
    change V.ρ (φ h) (ĝ.val σ ((φ h)⁻¹ • QuotientGroup.mk 1)) = _
    have : (φ h)⁻¹ • (QuotientGroup.mk 1 : G ⧸ φ.range) = QuotientGroup.mk 1 := by
      change (QuotientGroup.mk ((φ h)⁻¹ * 1) : G ⧸ φ.range) = QuotientGroup.mk 1
      rw [QuotientGroup.eq]
      simp only [mul_one, inv_inv]
      exact ⟨h, rfl⟩
    rw [this]
  · have := congrFun (hĝ σ) (QuotientGroup.mk 1)
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    change V.ρ 1 (f'.val ((1 : G)⁻¹ • σ)) = _ at this
    simpa using this


include hact in
/-- **Restriction/transfer, in the function model.**  Vanishing for a finite-index subgroup `φ(H)`
gives vanishing for the larger group `G` (characteristic zero: average over the cosets). -/
theorem funVanish_of_res [Finite (G ⧸ φ.range)] (S : Set E)
    (H' : FunVanish (G := H) (E := E) (Rep.res φ V) S) : FunVanish (G := G) (E := E) V S := by
  classical
  have : Fintype (G ⧸ φ.range) := Fintype.ofFinite _
  intro f hcl hvan
  obtain ⟨g', hg'⟩ := H' (resEF φ hact V 2 f) hcl hvan
  have hn : (Fintype.card (G ⧸ φ.range) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨⟨fun σ => ((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, indFun φ hact g' σ q, fun γ σ => ?_⟩,
    fun σ => ?_⟩
  · change ((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, indFun φ hact g' (γ • σ) q =
      V.ρ γ (((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, indFun φ hact g' σ q)
    rw [map_smul, map_sum]
    congr 1
    simp only [indFun_smul φ hact]
    change ∑ q, V.ρ γ (indFun φ hact g' σ (γ⁻¹ • q)) = ∑ q, V.ρ γ (indFun φ hact g' σ q)
    exact Fintype.sum_equiv (MulAction.toPerm γ⁻¹) _ _ (fun q => rfl)
  · have key : ∀ q : G ⧸ φ.range, ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
        indFun φ hact g' ((TopCat.toSSet.obj E).δ i σ) q = f.val σ := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H r =>
        have e1 : ∀ i : Fin 3, indFun φ hact g' ((TopCat.toSSet.obj E).δ i σ) (QuotientGroup.mk r) =
            V.ρ r (g'.val ((TopCat.toSSet.obj E).δ i (r⁻¹ • σ))) := fun i => by
          rw [indFun_mk, face_smul]
        simp only [e1]
        have e2 : ∑ i : Fin 3, (-1 : ℤ) ^ i.val • V.ρ r (g'.val ((TopCat.toSSet.obj E).δ i (r⁻¹ • σ))) =
            V.ρ r (∑ i : Fin 3, (-1 : ℤ) ^ i.val • g'.val ((TopCat.toSSet.obj E).δ i (r⁻¹ • σ))) := by
          simp only [map_sum, map_zsmul]
        rw [e2, ← hg' (r⁻¹ • σ)]
        change V.ρ r (f.val (r⁻¹ • σ)) = f.val σ
        rw [f.property r⁻¹ σ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
    change f.val σ = ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
      (((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, indFun φ hact g' ((TopCat.toSSet.obj E).δ i σ) q)
    have hsw : ∑ x : Fin 3, (-1 : ℤ) ^ x.val •
        (((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, indFun φ hact g' ((TopCat.toSSet.obj E).δ x σ) q) =
        ((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹ • ∑ q, ∑ x : Fin 3, (-1 : ℤ) ^ x.val •
          indFun φ hact g' ((TopCat.toSSet.obj E).δ x σ) q := by
      simp only [smul_comm _ ((Fintype.card (G ⧸ φ.range) : ℚ))⁻¹, ← Finset.smul_sum]
      congr 1
      simp only [Finset.smul_sum]
      exact Finset.sum_comm
    rw [hsw]
    simp only [key, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul]

end Transfer

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
