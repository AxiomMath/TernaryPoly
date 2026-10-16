module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange

@[expose] public section


/-!
# The faces of `Γ(N)` for the plane stabilizer, and independence of the representative

Formalized by Claude Sonnet 5.5.

The faces of the locally symmetric space of `Γ(N)` attached to the plane cusp `P`
are the `Γ(N)`-orbits of rational planes, i.e. the double cosets `P(ℚ) ∩ SL₃(ℤ) \ SL₃(ℤ) / Γ(N)`
(`PlaneFaces N`, finite for `N ≠ 0` since `Γ(N)` has finite index).  The mixed cuspidal group of a
face is defined at a chosen integral conjugator `h` (`faceCuspidalInH2 N h n`); this file proves

* `gammaN_finiteIndex`, `planeFaces_finite`: finiteness of the set of faces;
* `faceCuspidalInH2_orbit`: the choice of `h` inside a face is immaterial, the canonical isomorphisms
  of `FaceFrameChange` / `FaceConjugation` carry the cuspidal group onto the cuspidal group;
* `exists_face_rep`: every rational plane is covered by a face, with the plane group of the face's
  representative equal to the stabilizer of the plane in `Γ(N)`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

theorem gammaN_eq_ker (N : ℕ) :
    gammaN N = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) :
      SL(3, ℤ) →* SL(3, ZMod N)).ker := by
  ext γ
  rw [MonoidHom.mem_ker, mem_gammaN, Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (h i j)
    rw [Int.cast_sub, sub_eq_zero] at this
    simp [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.one_apply] at this ⊢
    exact this
  · intro h i j
    have h2 := h i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_one, eq_intCast] at h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    rw [h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]


instance gammaN_finiteIndex (N : ℕ) [NeZero N] : (gammaN N).FiniteIndex := by
  rw [gammaN_eq_ker]
  exact Subgroup.finiteIndex_ker _

/-- Two integral conjugators give the same face of the locally symmetric space of `Γ(N)` iff they
differ by `h ↦ q h γ` with `q ∈ P(ℚ) ∩ SL₃(ℤ)` and `γ ∈ Γ(N)`. -/
def planeFaceSetoid (N : ℕ) : Setoid SL(3, ℤ) where
  r h h' := ∃ q ∈ planeBorel, ∃ γ ∈ gammaN N, h' = q * h * γ
  iseqv := by
    refine ⟨fun h => ⟨1, planeBorel.one_mem, 1, (gammaN N).one_mem, by simp⟩, ?_, ?_⟩
    · rintro h h' ⟨q, hq, γ, hγ, rfl⟩
      exact ⟨q⁻¹, planeBorel.inv_mem hq, γ⁻¹, (gammaN N).inv_mem hγ, by group⟩
    · rintro h h' h'' ⟨q, hq, γ, hγ, rfl⟩ ⟨q', hq', γ', hγ', rfl⟩
      exact ⟨q' * q, planeBorel.mul_mem hq' hq, γ * γ', (gammaN N).mul_mem hγ hγ', by group⟩

/-- **The faces of type `P` of the locally symmetric space of `Γ(N)`**: `Γ(N)`-orbits of rational
planes, as the quotient of `SL₃(ℤ)` by `h ~ q h γ`. -/
def PlaneFaces (N : ℕ) : Type := Quotient (planeFaceSetoid N)

instance planeFaces_finite (N : ℕ) [NeZero N] : Finite (PlaneFaces N) := by
  let f : SL(3, ℤ) ⧸ gammaN N → PlaneFaces N :=
    Quotient.lift (fun h => (Quotient.mk (planeFaceSetoid N) h : PlaneFaces N)) (by
      intro a b hab
      apply Quotient.sound
      have : a⁻¹ * b ∈ gammaN N := (QuotientGroup.leftRel_apply).mp hab
      exact ⟨1, planeBorel.one_mem, a⁻¹ * b, this, by group⟩)
  have hf : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn with
    | h h => exact ⟨QuotientGroup.mk h, rfl⟩
  exact Finite.of_surjective f hf


section Orbit

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Independence of the conjugator within a face.** If `h' = q h γ` with `q ∈ P(ℚ) ∩ SL₃(ℤ)`
and `γ ∈ SL₃(ℤ)` (in particular for two representatives of the same `Γ(N)`-orbit of planes), the
canonical isomorphism `H²(Γ_{h⁻¹Ph}, E_n) → H²(Γ_{(qh)⁻¹P(qh)}, E_n) → H²(Γ_{h'⁻¹Ph'}, E_n)` (identity
of the equal plane groups, then conjugation by `γ`) maps the group of classes with edge in the mixed
cuspidal group of `h⁻¹Ph` onto that of `h'⁻¹Ph'`. -/
theorem faceCuspidalInH2_orbit (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel) :
    Submodule.map (EdgeNat.h2Map (conjGammaHom N (q * h) γ) (faceRep N (q * h) n)
        (faceRep N (q * h * γ) n) (faceConjT γ n) (faceConjT_intertwines N (q * h) γ n))
      (Submodule.map (EdgeNat.h2Map (frameHom N h q hq) (faceRep N h n) (faceRep N (q * h) n)
        (frameT n) (frameT_intertwines N h n q hq)) (faceCuspidalInH2 N h n)) =
      faceCuspidalInH2 N (q * h * γ) n := by
  rw [map_faceCuspidalInH2_frame, map_faceCuspidalInH2_conj]

/-- Every rational plane cusp of `Γ(N)`, `N ≥ 3`, is represented by a face of `PlaneFaces N`: there is
an integral conjugator `h` with the stabilizer of the plane `gPg⁻¹` in `Γ(N)` equal to the plane
group of `h⁻¹Ph`, and the chosen representative `i.out` of the face of `h` differs from `h` by
`q h γ`, `q ∈ P(ℚ) ∩ SL₃(ℤ)`, `γ ∈ Γ(N)`. -/
theorem exists_face_rep (hN : 3 ≤ N) (g : GL (Fin 3) ℚ) :
    ∃ (i : PlaneFaces N) (h : SL(3, ℤ)),
      (∀ p ∈ gammaN N,
        InPQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ gammaNPAt N h) ∧
      ∃ q ∈ planeBorel, ∃ γ ∈ gammaN N, (Quotient.out i : SL(3, ℤ)) = q * h * γ := by
  obtain ⟨h, h1, -⟩ := exists_face_of_rational_plane N hN g
  refine ⟨Quotient.mk (planeFaceSetoid N) h, h, h1, ?_⟩
  exact (planeFaceSetoid N).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid N) h)

end Orbit

end TernaryPeriodPolynomials.Argument.SeedC3S4c
