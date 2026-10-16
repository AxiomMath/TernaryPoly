module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction

@[expose] public section


/-!
# Shapiro cochain ("Step C" of `face_pairing_perfect`, part 1)

Given a subgroup `level`, a representation, and a point `q : X`, this file builds a degree-2
cochain for `level` on `functionRepresentation representation X` out of a local cochain for the
stabilizer `fixedPointLevel level q`: transport the local cochain to every point of the
`level`-orbit of `q`, and set it to `0` elsewhere (the standard Shapiro/coinduction construction).

Proved here: the construction is a genuine equivariant cochain (`shapiroCochain`), it reproduces
the local cochain exactly at `q` (`shapiroCochain_apply_self`), and it vanishes identically at
every point outside the orbit of `q` (`shapiroCochain_apply_outside`). The cocycle-ness of this
construction (needed for `cocycles`/`H2`) is proved in `ShapiroRealization.lean`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

/-- Package a group element that lies in `level` and fixes `q` as an element of the stabilizer
subgroup `fixedPointLevel level q`. -/
def toFixedPointLevel (level : Subgroup RationalGL3) (q : X) (g : RationalGL3)
    (hg : g ∈ level) (hfix : g • q = q) : fixedPointLevel level q :=
  ⟨g, Subgroup.mem_inf.mpr ⟨hg, MulAction.mem_stabilizer_iff.mpr hfix⟩⟩

theorem shapiro_rep_mul (representation : Representation ℂ RationalGL3 V)
    (a b : RationalGL3) (x : V) :
    representation (a * b) x = representation a (representation b x) := by
  rw [map_mul]
  rfl

/-- A chosen transport element carrying `q` to `point`, given that one exists in `level`. -/
def shapiroTransport (level : Subgroup RationalGL3) (q point : X)
    (h : ∃ g : level, g.val • q = point) : level :=
  Classical.choose h

theorem shapiroTransport_spec (level : Subgroup RationalGL3) (q point : X)
    (h : ∃ g : level, g.val • q = point) :
    (shapiroTransport level q point h).val • q = point :=
  Classical.choose_spec h

/-- The underlying function of the Shapiro cochain: transport the local cochain at `q` to every
point of its `level`-orbit, and set it to `0` elsewhere. -/
def shapiroCochainFun (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2) :
    (Fin 3 → RationalGL3) → X → V :=
  fun vertices point =>
    if h : ∃ g : level, g.val • q = point then
      representation (shapiroTransport level q point h).val
        (local_.val (fun i => (shapiroTransport level q point h).val⁻¹ * vertices i))
    else 0

theorem shapiroCochainFun_apply_pos (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2)
    (vertices : Fin 3 → RationalGL3) (point : X) (h : ∃ g : level, g.val • q = point) :
    shapiroCochainFun level representation q local_ vertices point =
      representation (shapiroTransport level q point h).val
        (local_.val (fun i => (shapiroTransport level q point h).val⁻¹ * vertices i)) := by
  unfold shapiroCochainFun
  rw [dite_eq_left h]

theorem shapiroCochainFun_apply_neg (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2)
    (vertices : Fin 3 → RationalGL3) (point : X) (h : ¬ ∃ g : level, g.val • q = point) :
    shapiroCochainFun level representation q local_ vertices point = 0 := by
  unfold shapiroCochainFun
  rw [dite_eq_right h]

/-- The Shapiro cochain is a valid degree-2 cochain for `level` acting on
`functionRepresentation representation X`. -/
def shapiroCochain (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2) :
    cochains level (functionRepresentation representation X) 2 :=
  ⟨shapiroCochainFun level representation q local_, by
    intro element vertices
    funext point
    show shapiroCochainFun level representation q local_ (fun i => element.val * vertices i) point
      = representation element.val
          (shapiroCochainFun level representation q local_ vertices (element.val⁻¹ • point))
    by_cases h : ∃ g : level, g.val • q = point
    · obtain ⟨g, hg⟩ := h
      have h' : ∃ g : level, g.val • q = element.val⁻¹ • point := by
        refine ⟨element⁻¹ * g, ?_⟩
        show (element⁻¹ * g).val • q = element.val⁻¹ • point
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hg]
      rw [shapiroCochainFun_apply_pos _ _ _ _ _ _ ⟨g, hg⟩,
        shapiroCochainFun_apply_pos _ _ _ _ _ _ h']
      set t := shapiroTransport level q point ⟨g, hg⟩ with ht_def
      set t' := shapiroTransport level q (element.val⁻¹ • point) h' with ht'_def
      have ht : t.val • q = point := shapiroTransport_spec level q point ⟨g, hg⟩
      have ht' : t'.val • q = element.val⁻¹ • point :=
        shapiroTransport_spec level q (element.val⁻¹ • point) h'
      have hmemlevel : (t.val⁻¹ * element.val * t'.val) ∈ level :=
        level.mul_mem (level.mul_mem (level.inv_mem t.property) element.property) t'.property
      have hfix : (t.val⁻¹ * element.val * t'.val) • q = q := by
        rw [mul_smul, mul_smul, ht', smul_inv_smul, ← ht, inv_smul_smul]
      have hlocal : local_.val (fun i => (t.val⁻¹ * element.val * t'.val) * (t'.val⁻¹ * vertices i))
          = representation (t.val⁻¹ * element.val * t'.val)
              (local_.val (fun i => t'.val⁻¹ * vertices i)) :=
        local_.property (toFixedPointLevel level q
          (t.val⁻¹ * element.val * t'.val) hmemlevel hfix) (fun i => t'.val⁻¹ * vertices i)
      have hcompose : (fun i => (t.val⁻¹ * element.val * t'.val) * (t'.val⁻¹ * vertices i))
          = (fun i => t.val⁻¹ * (element.val * vertices i)) := by
        funext i; group
      rw [hcompose] at hlocal
      show representation t.val (local_.val (fun i => t.val⁻¹ * (element.val * vertices i)))
        = representation element.val
            (representation t'.val (local_.val (fun i => t'.val⁻¹ * vertices i)))
      rw [hlocal, ← shapiro_rep_mul, ← shapiro_rep_mul]
      have hgroup : t.val * (t.val⁻¹ * element.val * t'.val) = element.val * t'.val := by group
      rw [hgroup]
    · have h' : ¬ ∃ g : level, g.val • q = element.val⁻¹ • point := by
        rintro ⟨g, hg⟩
        apply h
        refine ⟨element * g, ?_⟩
        show (element * g).val • q = point
        rw [Subgroup.coe_mul, mul_smul, hg, smul_inv_smul]
      rw [shapiroCochainFun_apply_neg _ _ _ _ _ _ h, shapiroCochainFun_apply_neg _ _ _ _ _ _ h',
        map_zero]⟩

theorem shapiroCochain_apply_self (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2)
    (vertices : Fin 3 → RationalGL3) :
    (shapiroCochain level representation q local_).val vertices q = local_.val vertices := by
  have h : ∃ g : level, g.val • q = q := ⟨1, by simp⟩
  show shapiroCochainFun level representation q local_ vertices q = local_.val vertices
  rw [shapiroCochainFun_apply_pos _ _ _ _ _ _ h]
  set t := shapiroTransport level q q h with ht_def
  have ht : t.val • q = q := shapiroTransport_spec level q q h
  have hlocal : local_.val (fun i => t.val * (t.val⁻¹ * vertices i)) =
      representation t.val (local_.val (fun i => t.val⁻¹ * vertices i)) :=
    local_.property (toFixedPointLevel level q t.val t.property ht)
      (fun i => t.val⁻¹ * vertices i)
  have hcompose : (fun i => t.val * (t.val⁻¹ * vertices i)) = vertices := by
    funext i; group
  rw [hcompose] at hlocal
  rw [← hlocal]

theorem shapiroCochain_apply_outside (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cochains (fixedPointLevel level q) representation 2)
    (vertices : Fin 3 → RationalGL3) (point : X) (h : ¬ ∃ g : level, g.val • q = point) :
    (shapiroCochain level representation q local_).val vertices point = 0 :=
  shapiroCochainFun_apply_neg level representation q local_ vertices point h

end TernaryPeriodPolynomials.Argument.FacePairing
