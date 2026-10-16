module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FStar

@[expose] public section


/-!
# Period cocycles of cusp forms on a subgroup of `SL₂(ℤ)` and Eichler--Shimura spanning

Paper: Lemma C.3
(`ar:lem:seed`), spanning clause; the mixed cuspidal group `𝒞_P`.

For a subgroup `Λ ⊆ SL₂(ℤ)` and a cusp form `f` of weight `n + 3` for the image `LamGL Λ` in
`GL₂(ℝ)`, `holCocycle f` is the cocycle `m ↦ ε_f(m)` of `Λ` with values in `Sym^{n+1} ⊗ det⁻¹`
(D's Eichler cocycle of the normalized moment primitives), and `antiholCocycle f` is its
coefficientwise conjugate. `parabolicH1 Λ n` is the parabolic cohomology (classes with a
representative that is a coboundary on every parabolic element). The proposition `ESSpan Λ n`
-- every parabolic class is a combination of holomorphic and antiholomorphic period classes -- is
a hypothesis, never an axiom: it is the single analytic input of the spanning clause of
Lemma C.3 at the level `Λ = Γ₂(N)`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Matrix MvPolynomial
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The library's action of `m ∈ SL₂(ℤ)` on `Sym^d ⊗ det⁻¹` is the substitution `invCoordPoly`. -/
theorem modularBinaryRep_coe (d : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (P : modularBinaryRep d (-1)) :
    bval d ((modularBinaryRep d (-1)).ρ m P) =
      bind₁ (invCoordPoly (SpecialLinearGroup.mapGL ℝ m)) (bval d P) := by
  have key : ∀ Q : Binary.HomogeneousPoly d,
      ((Binary.homogeneousAction d (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL m)) Q : Binary.HomogeneousPoly d) : MvPolynomial (Fin 2) ℂ) =
      bind₁ (invCoordPoly (SpecialLinearGroup.mapGL ℝ m)) (Q : MvPolynomial (Fin 2) ℂ) := by
    intro Q
    rw [Binary.homogeneousAction_coe, Binary.action_apply]
    have hdet0 : (m : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := m.det_coe
    rw [Matrix.det_fin_two] at hdet0
    have hdet : Binary.determinantCharacter (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ)
        (SpecialLinearGroup.toGL m)) = 1 := by
      simp only [Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
      have : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ)
          (SpecialLinearGroup.toGL m)) : ℂˣ) : ℂ) = 1 := by
        simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
        exact_mod_cast hdet0
      rw [this]; simp
    rw [hdet, one_smul]
    have hlin : Binary.linearForm
        (((GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL m))⁻¹ :
          Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) =
        invCoordPoly (SpecialLinearGroup.mapGL ℝ m) := by
      funext i
      have hc : ((m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) *
          ((m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) -
          ((m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) *
            ((m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
        exact_mod_cast hdet0
      have hM : (((GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL m))⁻¹ :
          Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ), -((m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ);
             -((m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ),
              ((m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ)] := by
        rw [Matrix.coe_units_inv]
        apply Matrix.inv_eq_right_inv
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hc
      rw [hM]
      fin_cases i
      · simp [Binary.linearForm, invCoordPoly, Fin.sum_univ_two, SpecialLinearGroup.mapGL]
        ring
      · simp [Binary.linearForm, invCoordPoly, Fin.sum_univ_two, SpecialLinearGroup.mapGL]
    show (bind₁ (Binary.linearForm _)) _ = _
    rw [hlin]
  exact key P

theorem map_conj_invCoordPoly (γ : GL (Fin 2) ℝ) (i : Fin 2) :
    MvPolynomial.map (starRingEnd ℂ) (invCoordPoly γ i) = invCoordPoly γ i := by
  fin_cases i <;> simp [invCoordPoly]

theorem map_conj_bind_invCoordPoly (γ : GL (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (bind₁ (invCoordPoly γ) P) =
      bind₁ (invCoordPoly γ) (MvPolynomial.map (starRingEnd ℂ) P) := by
  rw [MvPolynomial.map_bind₁]
  congr 2
  funext i
  exact map_conj_invCoordPoly γ i

/-! ### Period cocycles for a subgroup `Λ ⊂ SL₂(ℤ)` -/

section Period

open CategoryTheory groupCohomology UpperHalfPlane
open scoped MatrixGroups

variable (Λ : Subgroup SL(2, ℤ)) (n : ℕ)

/-- `Sym^{n+1} ⊗ det⁻¹` as a representation of `Λ`. -/
abbrev binRep : Rep ℂ Λ := Rep.res Λ.subtype (modularBinaryRep (n + 1) (-1))

/-- The image of `Λ` in `GL₂(ℝ)`. -/
abbrev LamGL : Subgroup (GL (Fin 2) ℝ) := Λ.map (SpecialLinearGroup.mapGL ℝ)

variable {Λ n}

/-- The polynomial underlying a value of `binRep`. -/
def bvalΛ (x : binRep Λ n) : MvPolynomial (Fin 2) ℂ := (x : Binary.HomogeneousPoly (n + 1)).1

variable (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ))

/-- The value of the Eichler cocycle of `f` at `m ∈ SL₂(ℤ)`, as a binary form. -/
def eichlerForm (m : SL(2, ℤ)) : Binary.HomogeneousPoly (n + 1) :=
  ⟨eichlerCocycle n (momentPrim (LamGL Λ) n f) (SpecialLinearGroup.mapGL ℝ m),
    (mem_homogeneousSubmodule _ _).mpr (eichlerCocycle_isHomogeneous n _ _)⟩

/-- The holomorphic period cocycle of `f` on `Λ`. -/
def holCocycle : cocycles₁ (binRep Λ n) :=
  ⟨fun m => eichlerForm f m.1, (mem_cocycles₁_iff _).2 (fun g h => by
    have hp := (momentPrim_spec (LamGL Λ) n f).2.2.2.1 (SpecialLinearGroup.mapGL ℝ g.1)
      ⟨g.1, g.2, rfl⟩ (SpecialLinearGroup.mapGL ℝ h.1) ⟨h.1, h.2, rfl⟩
    apply Subtype.ext
    have e1 : bvalΛ ((binRep Λ n).ρ g (eichlerForm f h)) =
        bind₁ (invCoordPoly (SpecialLinearGroup.mapGL ℝ g.1))
          (eichlerCocycle n (momentPrim (LamGL Λ) n f) (SpecialLinearGroup.mapGL ℝ h.1)) :=
      modularBinaryRep_coe (n + 1) g.1 (eichlerForm f h)
    change eichlerCocycle n (momentPrim (LamGL Λ) n f) (SpecialLinearGroup.mapGL ℝ (g.1 * h.1)) =
      bvalΛ ((binRep Λ n).ρ g (eichlerForm f h)) + eichlerCocycle n (momentPrim (LamGL Λ) n f)
          (SpecialLinearGroup.mapGL ℝ g.1)
    rw [e1, map_mul, hp, add_comm])⟩

/-- The antiholomorphic period cocycle of `f` on `Λ`: the coefficientwise conjugate of the Eichler
cocycle. -/
def antiholCocycle : cocycles₁ (binRep Λ n) :=
  ⟨fun m => ⟨MvPolynomial.map (starRingEnd ℂ) (eichlerForm f m.1).1,
    (mem_homogeneousSubmodule _ _).mpr
      (((mem_homogeneousSubmodule _ _).mp (eichlerForm f m.1).2).map _)⟩,
    (mem_cocycles₁_iff _).2 (fun g h => by
    have hp := (momentPrim_spec (LamGL Λ) n f).2.2.2.1 (SpecialLinearGroup.mapGL ℝ g.1)
      ⟨g.1, g.2, rfl⟩ (SpecialLinearGroup.mapGL ℝ h.1) ⟨h.1, h.2, rfl⟩
    apply Subtype.ext
    have e1 : bvalΛ ((binRep Λ n).ρ g
        (⟨MvPolynomial.map (starRingEnd ℂ) (eichlerForm f h.1).1,
          (mem_homogeneousSubmodule _ _).mpr
            (((mem_homogeneousSubmodule _ _).mp (eichlerForm f h.1).2).map _)⟩ :
          Binary.HomogeneousPoly (n + 1))) =
        bind₁ (invCoordPoly (SpecialLinearGroup.mapGL ℝ g.1))
          (MvPolynomial.map (starRingEnd ℂ) (eichlerForm f h.1).1) :=
      modularBinaryRep_coe (n + 1) g.1 _
    change MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n (momentPrim (LamGL Λ) n f)
        (SpecialLinearGroup.mapGL ℝ (g.1 * h.1))) =
      bvalΛ ((binRep Λ n).ρ g
        (⟨MvPolynomial.map (starRingEnd ℂ) (eichlerForm f h.1).1,
          (mem_homogeneousSubmodule _ _).mpr
            (((mem_homogeneousSubmodule _ _).mp (eichlerForm f h.1).2).map _)⟩ :
          Binary.HomogeneousPoly (n + 1))) +
        MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n (momentPrim (LamGL Λ) n f)
          (SpecialLinearGroup.mapGL ℝ g.1))
    rw [e1, map_mul, hp, map_add, map_conj_bind_invCoordPoly, add_comm]
    rfl)⟩

/-- Parabolic elements of `SL₂(ℤ)`: `±` conjugates of `T^k`. -/
def IsParabolicSL (γ : SL(2, ℤ)) : Prop :=
  ∃ (g : SL(2, ℤ)) (k : ℤ),
    γ = g * ModularGroup.T ^ k * g⁻¹ ∨ γ = -(g * ModularGroup.T ^ k * g⁻¹)

variable (Λ n) in
/-- The 1-cocycles of `Λ` that are coboundaries on every parabolic element of `Λ` (restriction
to every cusp stabilizer is trivial). -/
def parabolicCocycles : Submodule ℂ (cocycles₁ (binRep Λ n)) where
  carrier := {c | ∀ γ : Λ, IsParabolicSL γ.1 → ∃ u : binRep Λ n,
    c γ = (binRep Λ n).ρ γ u - u}
  zero_mem' := fun γ _ => ⟨0, by rw [map_zero, sub_zero]; rfl⟩
  add_mem' := by
    rintro a b ha hb γ hγ
    obtain ⟨u, hu⟩ := ha γ hγ
    obtain ⟨v, hv⟩ := hb γ hγ
    refine ⟨u + v, ?_⟩
    change a γ + b γ = _
    rw [hu, hv, map_add]
    abel
  smul_mem' := by
    rintro c a ha γ hγ
    obtain ⟨u, hu⟩ := ha γ hγ
    refine ⟨c • u, ?_⟩
    change c • a γ = _
    rw [hu, map_smul, smul_sub]

variable (Λ n) in
/-- **Parabolic cohomology** `H¹_par(Λ, Sym^{n+1} ⊗ det⁻¹)`: the classes with a representative
cocycle that is a coboundary at every cusp (the paper's mixed cuspidal group
`𝒞_P`). -/
def parabolicH1 : Submodule ℂ (H1 (binRep Λ n)) :=
  Submodule.map (H1π (binRep Λ n)).hom (parabolicCocycles Λ n)

variable (Λ n) in
/-- **Eichler–Shimura spanning** for `Λ` in weight `n + 3`: every parabolic class is a
combination of holomorphic and antiholomorphic period classes of cusp forms for `Λ`. This is the
one analytic input of the spanning clause of Lemma C.3. -/
def ESSpan : Prop :=
  parabolicH1 Λ n ≤ Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) => H1π (binRep Λ n) (holCocycle f)) ∪
      Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
        H1π (binRep Λ n) (antiholCocycle f)))

end Period

end TernaryPeriodPolynomials.Argument.SeedC3S4c
