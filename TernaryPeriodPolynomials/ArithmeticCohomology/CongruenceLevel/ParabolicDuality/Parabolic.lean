module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Duality

@[expose] public section

/-!
# The pairing on the image of the NAIVE edge-identity map `j_comb : ker d_c → C¹/δC⁰`

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

Everything below is about the *naive* map `jmap : ker d_c → C¹/δC⁰` that is the
identity on edge cochains (a combinatorial "Hodge-type" map).  It is **not** the topological map `H¹_c → H¹` of the long exact sequence
of the compactified modular curve, and the pairing `parabolicPairing` on `Im jmap` is **not** the paper's cuspidal pairing:
* it is symmetric, whereas the cup product on `H¹` is skew;
* for trivial coefficients `dim Im jmap = 2g + c - 1`, whereas cuspidal cohomology has dimension `2g`;
* the true boundary classes (`d w` for a cusp function `w`) lie in `ker d_c` but are not killed by `jmap`.
The names `jmap`, `parabolicPairing`, ... keep their names because they are already pushed; the correctly named aliases are
`naiveJ`, `naiveParabolicPairing` (and `gammaN_naive_parabolic_pairing` in the export).

What *is* proved, and is the real content: `PDc_nondegenerate`/`PDq_nondegenerate`, i.e. the **perfect duality
`ker d_c(E) × C¹(E')/δC⁰(E') → ℂ`** (Poincaré-Lefschetz duality in the dual-tree model, `H¹_c(E) = ker d_c(E)` as the dual of
`H¹(E') = C¹(E')/δC⁰(E')`), via `annihilator_ker_dc`.  Abstractly, the `FacePD.Lefschetz.imagePairing` then gives a perfect pairing on
`Im jmap × Im jmap'` for ANY such transposed pair of maps; here the pair is the naive one.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD
open scoped Classical

variable {Γ : Subgroup IntegralGL}

section Parabolic

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  {ρ : Representation ℂ Γ E} {ρ' : Representation ℂ Γ E'}

/-- Compactly supported cohomology in degree one: `ker d_c`. -/
abbrev Hc (ρ : Representation ℂ Γ E) : Type := ↥(LinearMap.ker (dc ρ))

/-- Ordinary cohomology in degree one: `C¹ / δ C⁰`. -/
abbrev Hq (ρ : Representation ℂ Γ E) : Type := C1 ρ ⧸ LinearMap.range (delta ρ)

/-- The NAIVE map `ker d_c → C¹/δC⁰` (identity on edge cochains).  It is NOT the topological map `H¹_c → H¹` and its image is NOT the
cuspidal cohomology (see the module doc); the alias `naiveJ` is the preferred name. -/
def jmap (ρ : Representation ℂ Γ E) : Hc ρ →ₗ[ℂ] Hq ρ :=
  (LinearMap.range (delta ρ)).mkQ ∘ₗ (LinearMap.ker (dc ρ)).subtype

/-- The duality pairing `ker d_c(E) × C¹(E')/δC⁰(E') → ℂ` (Poincaré-Lefschetz duality in the dual-tree model). -/
def PDc (C : Coupling ρ ρ') (D : FareyData Γ) : Hc ρ →ₗ[ℂ] Hq ρ' →ₗ[ℂ] ℂ :=
  ((LinearMap.range (delta ρ')).liftQ ((pV C D).compl₁₂ (LinearMap.ker (dc ρ)).subtype LinearMap.id).flip (by
    rintro _ ⟨H', rfl⟩
    apply LinearMap.ext
    intro a
    have ha : dc ρ a.1 = 0 := LinearMap.mem_ker.mp a.2
    change pV C D a.1 (delta ρ' H') = 0
    rw [pV_delta, ha]
    simp [pW])).flip

/-- The duality pairing `C¹(E)/δC⁰(E) × ker d_c(E') → ℂ` (the same duality with the roles exchanged). -/
def PDq (C : Coupling ρ ρ') (D : FareyData Γ) : Hq ρ →ₗ[ℂ] Hc ρ' →ₗ[ℂ] ℂ :=
  (LinearMap.range (delta ρ)).liftQ ((pV C D).compl₂ (LinearMap.ker (dc ρ')).subtype) (by
    rintro _ ⟨H, rfl⟩
    apply LinearMap.ext
    intro b
    have hb : dc ρ' b.1 = 0 := LinearMap.mem_ker.mp b.2
    change pV C D (delta ρ H) b.1 = 0
    rw [pV_delta', hb]
    simp [pW])

theorem PDc_apply (C : Coupling ρ ρ') (D : FareyData Γ) (a : Hc ρ) (G : C1 ρ') :
    PDc C D a (Submodule.Quotient.mk G) = pV C D a.1 G := rfl

theorem PDq_apply (C : Coupling ρ ρ') (D : FareyData Γ) (F : C1 ρ) (b : Hc ρ') :
    PDq C D (Submodule.Quotient.mk F) b = pV C D F b.1 := rfl

/-- `j'` is the transpose of `j` for the two Poincaré-Lefschetz pairings. -/
theorem PD_transpose (C : Coupling ρ ρ') (D : FareyData Γ) (a : Hc ρ) (b : Hc ρ') :
    PDc C D a (jmap ρ' b) = PDq C D (jmap ρ a) b := rfl

section Fin

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']

/-- **Duality, first half**: a class of `C¹(E)/δC⁰(E)` killed by all of `ker d_c(E')` is zero. -/
theorem PDq_nondegenerate (C : Coupling ρ ρ') (D : FareyData Γ) (x : Hq ρ) (h : ∀ b, PDq C D x b = 0) : x = 0 := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have : F ∈ LinearMap.range (delta ρ) := by
    refine annihilator_ker_dc' C D F ?_
    intro G hG
    exact h ⟨G, LinearMap.mem_ker.mpr hG⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr this

/-- **Duality, second half**: a class of `C¹(E')/δC⁰(E')` killed by all of `ker d_c(E)` is zero. -/
theorem PDc_nondegenerate (C : Coupling ρ ρ') (D : FareyData Γ) (y : Hq ρ') (h : ∀ a, PDc C D a y = 0) : y = 0 := by
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : G ∈ LinearMap.range (delta ρ') := by
    refine annihilator_ker_dc C D G ?_
    intro F hF
    exact h ⟨F, LinearMap.mem_ker.mpr hF⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr this

/-- **The pairing on the images of the naive map `jmap`** (`Im jmap ⊆ C¹(E)/δC⁰(E)`, `Im jmap' ⊆ C¹(E')/δC⁰(E')`), well defined by the
Lefschetz transposition of the naive maps and nondegenerate in both arguments.  This is NOT the paper's parabolic/cuspidal pairing (the
naive `jmap` is not the topological `H¹_c → H¹`; see the module doc). -/
def parabolicPairing (C : Coupling ρ ρ') (D : FareyData Γ) :
    LinearMap.range (jmap ρ) →ₗ[ℂ] LinearMap.range (jmap ρ') →ₗ[ℂ] ℂ :=
  Lefschetz.imagePairing (Hc := Hc ρ) (Hc' := Hc ρ') (H := Hq ρ) (H' := Hq ρ') (PDc C D) (PDq C D) (jmap ρ) (jmap ρ')
    (PD_transpose C D)

omit [FiniteDimensional ℂ E'] in
theorem jmap_mk (b : Hc ρ') : jmap ρ' b = Submodule.Quotient.mk b.1 := rfl

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
theorem parabolicPairing_apply (C : Coupling ρ ρ') (D : FareyData Γ) (a : Hc ρ) (b : Hc ρ') :
    parabolicPairing C D ⟨jmap ρ a, LinearMap.mem_range_self _ a⟩ ⟨jmap ρ' b, LinearMap.mem_range_self _ b⟩ =
      pV C D a.1 b.1 := by
  have h := Lefschetz.imagePairing_apply (Hc := Hc ρ) (Hc' := Hc ρ') (H := Hq ρ) (H' := Hq ρ') (PDc C D) (PDq C D)
    (jmap ρ) (jmap ρ') (PD_transpose C D) a b
  exact h.trans (PDc_apply C D a b.1)

theorem parabolicPairing_left_nondegenerate (C : Coupling ρ ρ') (D : FareyData Γ) (x : LinearMap.range (jmap ρ))
    (h : ∀ y, parabolicPairing C D x y = 0) : x = 0 :=
  Lefschetz.imagePairing_left_nondegenerate (Hc := Hc ρ) (Hc' := Hc ρ') (H := Hq ρ) (H' := Hq ρ') (PDc C D) (PDq C D) (jmap ρ) (jmap ρ') (PD_transpose C D)
    (PDq_nondegenerate C D) x h

theorem parabolicPairing_right_nondegenerate (C : Coupling ρ ρ') (D : FareyData Γ) (y : LinearMap.range (jmap ρ'))
    (h : ∀ x, parabolicPairing C D x y = 0) : y = 0 :=
  Lefschetz.imagePairing_right_nondegenerate (Hc := Hc ρ) (Hc' := Hc ρ') (H := Hq ρ) (H' := Hq ρ') (PDc C D) (PDq C D) (jmap ρ) (jmap ρ') (PD_transpose C D)
    (PDc_nondegenerate C D) y h

/-- Alias making the nature of `jmap` explicit: the naive edge-identity map `ker d_c → C¹/δC⁰` (not the topological `H¹_c → H¹`). -/
abbrev naiveJ (ρ : Representation ℂ Γ E) : Hc ρ →ₗ[ℂ] Hq ρ := jmap ρ

/-- Alias of `parabolicPairing`: the pairing on the images of the NAIVE map `naiveJ` (not the paper's cuspidal pairing). -/
abbrev naiveParabolicPairing (C : Coupling ρ ρ') (D : FareyData Γ) :
    LinearMap.range (naiveJ ρ) →ₗ[ℂ] LinearMap.range (naiveJ ρ') →ₗ[ℂ] ℂ := parabolicPairing C D

end Fin

end Parabolic

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
