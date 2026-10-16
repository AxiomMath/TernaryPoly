module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryCochainNormalization
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

abbrev faceP : Rep ℚ P := Rep.res P.subtype A
abbrev faceQ : Rep ℚ Q := Rep.res Q.subtype A
abbrev corner : Rep ℚ (P ⊓ Q : Subgroup G) := Rep.res (P ⊓ Q).subtype A
abbrev intoP : (P ⊓ Q : Subgroup G) →* P := Subgroup.inclusion inf_le_left
abbrev intoQ : (P ⊓ Q : Subgroup G) →* Q := Subgroup.inclusion inf_le_right

abbrev C0 := A × A
abbrev C1 := (P → A) × (Q → A) × A
abbrev C2 := (P × P → A) × (Q × Q → A) × ((P ⊓ Q : Subgroup G) → A)

/-- The degree-zero differential of the shifted restriction cone. -/
def d0 : C0 A →ₗ[ℚ] C1 A P Q where
  toFun v := (d₀₁ (faceP A P) v.1, d₀₁ (faceQ A Q) v.2, v.1 - v.2)
  map_add' v w := by simp only [map_add, Prod.fst_add, Prod.snd_add, add_sub_add_comm]; rfl
  map_smul' r v := by
    change (d₀₁ (faceP A P) (r • v.1), d₀₁ (faceQ A Q) (r • v.2),
      r • v.1-r • v.2) = (r • d₀₁ (faceP A P) v.1, r • d₀₁ (faceQ A Q) v.2, r • (v.1-v.2))
    simp only [map_smul, smul_sub]

/-- The degree-one differential, with corner component res AP - res AQ - d u. -/
def d1 : C1 A P Q →ₗ[ℚ] C2 A P Q where
  toFun c := (d₁₂ (faceP A P) c.1, d₁₂ (faceQ A Q) c.2.1,
    fun b => c.1 (intoP P Q b) - c.2.1 (intoQ P Q b) - d₀₁ (corner A P Q) c.2.2 b)
  map_add' c c' := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply,
      add_sub_add_comm]
  map_smul' r c := by
    dsimp
    ext <;> simp only [map_smul, Pi.smul_apply, smul_sub]

@[simp] theorem d1_d0 (v : C0 A) : d1 A P Q (d0 A P Q v) = 0 := by
  apply Prod.ext
  · exact d₀₁_comp_d₁₂_apply (faceP A P) v.1
  apply Prod.ext
  · exact d₀₁_comp_d₁₂_apply (faceQ A Q) v.2
  funext b
  change (A.ρ b.val v.1 - v.1) - (A.ρ b.val v.2 - v.2) -
    (A.ρ b.val (v.1-v.2) - (v.1-v.2)) = 0
  rw [map_sub]
  abel

/-- The actual three-term complex whose homology is cone H1. -/
def complex : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.moduleCatMk (d0 A P Q) (d1 A P Q) (by apply LinearMap.ext; intro v; exact d1_d0 A P Q v)

abbrev Z1 := LinearMap.ker (d1 A P Q)

theorem mem_Z1_iff (c : C1 A P Q) : c ∈ Z1 A P Q ↔
    c.1 ∈ cocycles₁ (faceP A P) ∧ c.2.1 ∈ cocycles₁ (faceQ A Q) ∧
    ∀ b, d₀₁ (corner A P Q) c.2.2 b = c.1 (intoP P Q b) - c.2.1 (intoQ P Q b) := by
  change d1 A P Q c = 0 ↔ _
  change (d₁₂ (faceP A P) c.1, d₁₂ (faceQ A Q) c.2.1,
    fun b => c.1 (intoP P Q b)-c.2.1 (intoQ P Q b)-d₀₁ (corner A P Q) c.2.2 b) =
      (0,0,0) ↔ _
  simp only [Prod.mk.injEq]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [funext_iff]
  apply forall_congr'
  intro b
  exact sub_eq_zero.trans eq_comm

def coboundary : C0 A →ₗ[ℚ] Z1 A P Q :=
  (d0 A P Q).codRestrict _ (d1_d0 A P Q)

abbrev boundaries := LinearMap.range (coboundary A P Q)
abbrev H1 := Z1 A P Q ⧸ boundaries A P Q

def classOf : Z1 A P Q →ₗ[ℚ] H1 A P Q := (boundaries A P Q).mkQ

/-- Identification with Mathlib's homology of the explicit cone complex. -/
def homologyIso : (complex A P Q).homology ≅ ModuleCat.of ℚ (H1 A P Q) :=
  (complex A P Q).moduleCatHomologyIso

/-- Gauge normalization is subtraction of the actual cone coboundary. -/
def gauge (c : Z1 A P Q) (v : C0 A) : Z1 A P Q := c - coboundary A P Q v

@[simp] theorem gauge_val (c : Z1 A P Q) (v : C0 A) :
    (gauge A P Q c v).val = (c.val.1-d₀₁ (faceP A P) v.1,
      c.val.2.1-d₀₁ (faceQ A Q) v.2, c.val.2.2-v.1+v.2) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  change c.val.2.2 - (v.1-v.2) = c.val.2.2-v.1+v.2
  abel

@[simp] theorem classOf_gauge (c : Z1 A P Q) (v : C0 A) :
    classOf A P Q (gauge A P Q c v) = classOf A P Q c := by
  change (boundaries A P Q).mkQ (c-coboundary A P Q v) = _
  have h : (boundaries A P Q).mkQ (coboundary A P Q v) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v,rfl⟩
  rw [map_sub, h, sub_zero]
  rfl

/-- Equality in H1 is precisely an actual gauge change. -/
theorem classOf_eq_iff (c c' : Z1 A P Q) :
    classOf A P Q c = classOf A P Q c' ↔ ∃ v, c = gauge A P Q c' v := by
  rw [← sub_eq_zero, ← map_sub]
  change (boundaries A P Q).mkQ (c-c') = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨-v,?_⟩
    dsimp [gauge]
    rw [map_neg, hv]
    abel
  · rintro ⟨v,rfl⟩
    refine ⟨-v,?_⟩
    rw [map_neg]
    dsimp [gauge]
    abel

end TernaryPoly.OrdinaryBoundaryCone
