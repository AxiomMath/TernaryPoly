module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Modules
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstruction

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeShapiroModules
open CategoryTheory CategoryTheory.Abelian
open RelativeOrbitStabilizers RelativeOrbitCosets RelativeOrbitModules
open RelativeExtObstructionSequences

/-- The actual untwisted permutation action on the literal coset Finsupp module. -/
def cosetAction (H : Subgroup K) : Representation ℚ K ((K ⧸ H) →₀ ℚ) where
  toFun g := (cosetLinear H g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single q r => simp [cosetLinear]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single q r => simp [cosetLinear, mul_smul]

/-- The genuine coset representation. -/
abbrev CosetRep (H : Subgroup K) : Rep ℚ K := Rep.of (cosetAction H)

lemma coset_action_eq (H : Subgroup K) (g : K) (c : (K ⧸ H) →₀ ℚ) :
    (CosetRep H).ρ g c = cosetLinear H g c := rfl

/-- A literal product representation, with the two component actions. -/
abbrev productRep (A B : Rep.{0} ℚ K) : Rep ℚ K := Rep.of (A.ρ.prod B.ρ)

/-- The coset vertex identification bundled as an isomorphism in Rep. -/
def verticesIso : productRep (CosetRep HL) (CosetRep HP) ≅ RelativeVerticesRep :=
  Rep.mkIso { relativeVertices with
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro c
      change relativeVertices ((CosetRep HL).ρ g c.1, (CosetRep HP).ρ g c.2) = _
      rw [coset_action_eq, coset_action_eq]
      exact relativeVertices_equivariant g c }

/-- The coset edge identification bundled as an isomorphism in Rep. -/
def edgesIso : productRep (CosetRep HBB) (CosetRep HBG) ≅ RelativeEdgesRep :=
  Rep.mkIso { relativeEdges with
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro c
      change relativeEdges ((CosetRep HBB).ρ g c.1, (CosetRep HBG).ρ g c.2) = _
      rw [coset_action_eq, coset_action_eq]
      exact relativeEdges_equivariant g c }

section Abstract
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Ext vanishing passes across an actual isomorphism in the first variable. -/
theorem ext_subsingleton_of_iso {A B E : C} (i : A ≅ B) (n : ℕ)
    [Subsingleton (Ext A E n)] : Subsingleton (Ext B E n) := by
  have hz (x : Ext B E n) : x = 0 := by
    have h : (Ext.mk₀ i.hom).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun y : Ext A E n => (Ext.mk₀ i.inv).comp y (zero_add n)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- A displayed binary splitting is enough for contravariant Ext vanishing in every degree. -/
theorem ext_subsingleton_of_split {A B P E : C} (iA : A ⟶ P) (iB : B ⟶ P)
    (pA : P ⟶ A) (pB : P ⟶ B) (h : pA ≫ iA + pB ≫ iB = 𝟙 P) (n : ℕ)
    [Subsingleton (Ext A E n)] [Subsingleton (Ext B E n)] :
    Subsingleton (Ext P E n) := by
  have hz (x : Ext P E n) : x = 0 := by
    have hA : (Ext.mk₀ iA).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    have hB : (Ext.mk₀ iB).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    calc
      x = (Ext.mk₀ (𝟙 P)).comp x (zero_add n) := (Ext.mk₀_id_comp x).symm
      _ = 0 := by
        rw [← h, Ext.mk₀_add, Ext.add_comp, ← Ext.mk₀_comp_mk₀_assoc,
          ← Ext.mk₀_comp_mk₀_assoc, hA, hB]
        simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
end Abstract

/-- Binary product splitting for actual representations. -/
theorem product_ext_subsingleton (A B E : Rep.{0} ℚ K) (n : ℕ)
    [Subsingleton (Ext.{1} A E n)] [Subsingleton (Ext.{1} B E n)] :
    Subsingleton (Ext.{1} (productRep A B) E n) := by
  let iA : A ⟶ productRep A B := Rep.ofHom ⟨LinearMap.inl ℚ A B, fun _ => by ext x <;> simp [Representation.prod]⟩
  let iB : B ⟶ productRep A B := Rep.ofHom ⟨LinearMap.inr ℚ A B, fun _ => by ext x <;> simp [Representation.prod]⟩
  let pA : productRep A B ⟶ A := Rep.ofHom ⟨LinearMap.fst ℚ A B, fun _ => rfl⟩
  let pB : productRep A B ⟶ B := Rep.ofHom ⟨LinearMap.snd ℚ A B, fun _ => rfl⟩
  apply ext_subsingleton_of_split iA iB pA pB _ n
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  change (c.1, 0) + (0, c.2) = c
  simp

/-- The two edge-coset Ext vanishings kill the actual relative edge term. -/
theorem relativeEdges_ext_subsingleton (E : Rep.{0} ℚ K)
    [Subsingleton (Ext.{1} (CosetRep HBB) E 1)]
    [Subsingleton (Ext.{1} (CosetRep HBG) E 1)] :
    Subsingleton (Ext.{1} RelativeEdgesRep E 1) := by
  let := product_ext_subsingleton (CosetRep HBB) (CosetRep HBG) E 1
  exact ext_subsingleton_of_iso edgesIso 1

/-- The two vertex-coset Ext vanishings kill the actual relative vertex term. -/
theorem relativeVertices_ext_subsingleton (E : Rep.{0} ℚ K)
    [Subsingleton (Ext.{1} (CosetRep HL) E 2)]
    [Subsingleton (Ext.{1} (CosetRep HP) E 2)] :
    Subsingleton (Ext.{1} RelativeVerticesRep E 2) := by
  let := product_ext_subsingleton (CosetRep HL) (CosetRep HP) E 2
  exact ext_subsingleton_of_iso verticesIso 2

end TernaryPoly.RelativeShapiroModules
