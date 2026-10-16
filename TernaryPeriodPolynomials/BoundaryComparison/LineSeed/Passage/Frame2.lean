module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Frame1
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Inner

@[expose] public section


/-!
# Frame change of the seed combination: independence of the conjugator (Passage 11)

For `b ∈ lineBorel` (`SL₃(ℤ)` with first column `(±1, 0, 0)ᵗ`) the conjugation `x ↦ b x b⁻¹` normalizes `Q⁺(ℤ)`; `conjCocycle b β` is the transported cocycle `ρ(b⁻¹) β(b·b⁻¹, b·b⁻¹)`.

* `classFace_frame`: the class at the cusp frame `b h` equals the frame transport of the class at `h` of the conjugated cocycle.
* `conjCocycle_class`: for odd `n`, the class of `seedCombCocycle f` is fixed by every `b ∈ lineBorel`: inner automorphisms of `Q⁺(ℤ)` act trivially (`map_conj_H2`), and the reflection
  `κ = diag(-1, 1, -1)` fixes the cochain exactly (`seedComb_kappa`).
* `seedComb_frame`: hence the seed combination at the frame `b h` is the frame transport of the one at `h`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep fStar faceT frameT)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.KDaggerComparison (levelN)

variable {n : ℕ}

/-- The first diagonal entry of an element of `lineBorel` is `±1`. -/
theorem lineBorel_00 {b : SL(3, ℤ)} (hb : b ∈ lineBorel) :
    (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∨ (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = -1 := by
  have hdet : (b : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := b.2
  rw [Matrix.det_fin_three, hb.1, hb.2] at hdet
  have : (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 *
      ((b : Matrix (Fin 3) (Fin 3) ℤ) 1 1 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 2 -
        (b : Matrix (Fin 3) (Fin 3) ℤ) 1 2 * (b : Matrix (Fin 3) (Fin 3) ℤ) 2 1) = 1 := by
    linear_combination hdet
  exact Int.eq_one_or_neg_one_of_mul_eq_one this

/-- Conjugation by `b ∈ lineBorel` on `Q⁺(ℤ)`. -/
def conjB (b : SL(3, ℤ)) (hb : b ∈ lineBorel) : ↥lineStab →* ↥lineStab where
  toFun x := ⟨b * x.1 * b⁻¹, conj_mem_lineStab hb x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjB_T (b : SL(3, ℤ)) (hb : b ∈ lineBorel) (g : ↥lineStab) (v : lineStabRep n) :
    (ambRep n b⁻¹ : lineStabRep n →ₗ[ℂ] lineStabRep n) ((lineStabRep n).ρ (conjB b hb g) v) =
      (lineStabRep n).ρ g ((ambRep n b⁻¹ : lineStabRep n →ₗ[ℂ] lineStabRep n) v) := by
  change ambRep n b⁻¹ (ambRep n (b * g.1 * b⁻¹) v) = ambRep n g.1 (ambRep n b⁻¹ v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- The conjugated cocycle `ρ(b⁻¹) β(b·b⁻¹, b·b⁻¹)`. -/
def conjCocycle (b : SL(3, ℤ)) (hb : b ∈ lineBorel) (β : cocycles₂ (lineStabRep n)) : cocycles₂ (lineStabRep n) :=
  groupCohomology.mapCocycles₂ (conjB b hb)
    (SeedC3S4c.EdgeNat.comparison (conjB b hb) (lineStabRep n) (lineStabRep n)
      (ambRep n b⁻¹ : lineStabRep n →ₗ[ℂ] lineStabRep n) (conjB_T b hb)) β

theorem conjCocycle_apply (b : SL(3, ℤ)) (hb : b ∈ lineBorel) (β : cocycles₂ (lineStabRep n)) (x y : ↥lineStab) :
    (conjCocycle b hb β).1 (x, y) = ambRep n b⁻¹ (β.1 (conjB b hb x, conjB b hb y)) := rfl

section Frame

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem conjB_psi (h b : SL(3, ℤ)) (hb : b ∈ lineBorel) (p : ↥(gammaNQAt N (b * h))) :
    conjB b hb (psiHom N h (frameHomQ N h b hb p)) = psiHom N (b * h) p := by
  apply Subtype.ext
  change b * (h * (frameHomQ N h b hb p).1 * h⁻¹) * b⁻¹ = (b * h) * p.1 * (b * h)⁻¹
  rw [coe_frameHomQ]
  group

/-- **Frame change for pulled-back cocycle classes**: the class at the frame `b h` of `β` is the frame transport of the class at `h` of the conjugated cocycle. -/
theorem classFace_frame (h b : SL(3, ℤ)) (hb : b ∈ lineBorel) (β : cocycles₂ (lineStabRep n)) :
    SeedC3S4c.EdgeNat.h2Map (psiHom N (b * h)) (lineStabRep n) (lineFaceRep N (b * h) n)
        (faceT (b * h) n).toLinearMap (psiHom_T N (b * h)) (H2π (lineStabRep n) β) =
      SeedC3S4c.EdgeNat.h2Map (frameHomQ N h b hb) (lineFaceRep N h n) (lineFaceRep N (b * h) n) (frameT n)
        (frameTQ_intertwines N h n b hb)
        (SeedC3S4c.EdgeNat.h2Map (psiHom N h) (lineStabRep n) (lineFaceRep N h n) (faceT h n).toLinearMap
          (psiHom_T N h) (H2π (lineStabRep n) (conjCocycle b hb β))) := by
  have eL := SeedC3S4c.EdgeNat.h2Map_π (psiHom N (b * h)) (lineStabRep n) (lineFaceRep N (b * h) n)
    (faceT (b * h) n).toLinearMap (psiHom_T N (b * h)) β
  have eI := SeedC3S4c.EdgeNat.h2Map_π (psiHom N h) (lineStabRep n) (lineFaceRep N h n) (faceT h n).toLinearMap
    (psiHom_T N h) (conjCocycle b hb β)
  have eF := SeedC3S4c.EdgeNat.h2Map_π (frameHomQ N h b hb) (lineFaceRep N h n) (lineFaceRep N (b * h) n) (frameT n)
    (frameTQ_intertwines N h n b hb)
    (groupCohomology.mapCocycles₂ (psiHom N h)
      (SeedC3S4c.EdgeNat.comparison (psiHom N h) (lineStabRep n) (lineFaceRep N h n) (faceT h n).toLinearMap
        (psiHom_T N h)) (conjCocycle b hb β))
  refine eL.trans (Eq.trans ?_ (eF.symm.trans (congrArg _ eI.symm)))
  refine congrArg ((groupCohomology.H2π (lineFaceRep N (b * h) n)).hom) ?_
  apply Subtype.ext
  funext p
  have hT : ∀ v : GeneralEisenstein.HomogeneousPoly n, faceT (b * h) n v = faceT h n (ambRep n b⁻¹ v) := fun v => by
    change ambRep n (b * h)⁻¹ v = ambRep n h⁻¹ (ambRep n b⁻¹ v)
    rw [_root_.mul_inv_rev, map_mul]
    rfl
  have e1 : conjB b hb (psiHom N h (frameHomQ N h b hb p.1)) = psiHom N (b * h) p.1 := conjB_psi N h b hb p.1
  have e2 : conjB b hb (psiHom N h (frameHomQ N h b hb p.2)) = psiHom N (b * h) p.2 := conjB_psi N h b hb p.2
  change faceT (b * h) n (β.1 (psiHom N (b * h) p.1, psiHom N (b * h) p.2)) =
    faceT h n (ambRep n b⁻¹ (β.1 (conjB b hb (psiHom N h (frameHomQ N h b hb p.1)),
      conjB b hb (psiHom N h (frameHomQ N h b hb p.2)))))
  rw [e1, e2, hT]

/-- The class of the seed combination is fixed by the conjugation by `b ∈ lineStab` (inner automorphism of `Q⁺(ℤ)`). -/
theorem conjCocycle_class_stab (b : SL(3, ℤ)) (hbs : b ∈ lineStab) (hb : b ∈ lineBorel) (β : cocycles₂ (lineStabRep n)) :
    H2π (lineStabRep n) (conjCocycle b hb β) = H2π (lineStabRep n) β := by
  let c : ↥lineStab := ⟨b⁻¹, lineStab.inv_mem hbs⟩
  have h1 := map_conj_H2 (lineStabRep n) c (H2π (lineStabRep n) β)
  rw [groupCohomology.H2π_comp_map_apply] at h1
  refine Eq.trans ?_ h1
  refine congrArg ((groupCohomology.H2π (lineStabRep n)).hom) ?_
  apply Subtype.ext
  funext p
  have e1 : conjB b hb p.1 = conjInv c p.1 := Subtype.ext (by simp [conjB, conjInv, c])
  have e2 : conjB b hb p.2 = conjInv c p.2 := Subtype.ext (by simp [conjB, conjInv, c])
  change ambRep n b⁻¹ (β.1 (conjB b hb p.1, conjB b hb p.2)) = (lineStabRep n).ρ c (β.1 (conjInv c p.1, conjInv c p.2))
  rw [e1, e2]
  rfl

end Frame

section Kappa

/-- `ρ(κ)` on polynomials is `ρ` of the real matrix `diag(-1, 1, -1)`. -/
theorem toPoly_ambRep_kap (v : GeneralEisenstein.HomogeneousPoly n) :
    Coef.toPoly (ambRep n kapSL v) = rho Kmat (Coef.toPoly v) := by
  have h1 : ((Matrix.SpecialLinearGroup.mapGL (n := Fin 3) (R := ℤ) ℝ kapSL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      Kmat := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    ext i j
    have := congrFun (congrFun realMat_kapSL i) j
    simpa [realMat] using this
  have := realCoefficient_coe n (Matrix.SpecialLinearGroup.mapGL (n := Fin 3) (R := ℤ) ℝ kapSL) v
  rw [h1] at this
  exact this

theorem seedCombR_kappa (hn : Odd n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥lineStab) :
    seedCombR f (kapConj x) (kapConj y) = ambRep n kapSL (seedCombR f x y) := by
  apply Coef.toPoly_injective
  rw [toPoly_ambRep_kap]
  exact seedComb_kappa hn f x y

theorem kapSL_inv : kapSL⁻¹ = kapSL := inv_eq_of_mul_eq_one_right kapSL_mul_self

end Kappa

section Frame2

variable (N : ℕ) [NeZero N]

theorem mem_lineStab_of_neg (b : SL(3, ℤ)) (hb : b ∈ lineBorel) (h1 : (b : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = -1) :
    kapSL * b ∈ lineStab := by
  have e : ∀ a : Fin 3, ((kapSL * b : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) a 0 =
      kapSign a * (b : Matrix (Fin 3) (Fin 3) ℤ) a 0 := fun a => by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (Matrix.diagonal kapSign * (b : Matrix (Fin 3) (Fin 3) ℤ)) a 0 = _
    rw [Matrix.diagonal_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [e, h1]; simp [kapSign]
  · rw [e, hb.1]; simp
  · rw [e, hb.2]; simp

/-- **The class of the seed combination is invariant under every `b ∈ lineBorel`** (odd `n`). -/
theorem conjCocycle_class (hn : Odd n) (b : SL(3, ℤ)) (hb : b ∈ lineBorel) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    H2π (lineStabRep n) (conjCocycle b hb (seedCombCocycle f)) = H2π (lineStabRep n) (seedCombCocycle f) := by
  rcases lineBorel_00 hb with h1 | h1
  · exact conjCocycle_class_stab b ⟨h1, hb.1, hb.2⟩ hb _
  · have hs := mem_lineStab_of_neg b hb h1
    have hbp : kapSL * b ∈ lineBorel := mem_lineBorel_of_mem_lineStab hs
    have key : conjCocycle b hb (seedCombCocycle f) = conjCocycle (kapSL * b) hbp (seedCombCocycle f) := by
      apply Subtype.ext
      funext p
      have hx : ∀ x : ↥lineStab, conjB b hb x = kapConj (conjB (kapSL * b) hbp x) := fun x => by
        apply Subtype.ext
        change b * x.1 * b⁻¹ = kapSL * ((kapSL * b) * x.1 * (kapSL * b)⁻¹) * kapSL
        rw [_root_.mul_inv_rev, kapSL_inv]
        have e : kapSL * (kapSL * b * x.1 * (b⁻¹ * kapSL)) * kapSL = (kapSL * kapSL) * b * x.1 * b⁻¹ * (kapSL * kapSL) := by
          group
        rw [e, kapSL_mul_self]
        group
      have hk : ∀ w : lineStabRep n, ambRep n b⁻¹ (ambRep n kapSL w) = ambRep n (kapSL * b)⁻¹ w := fun w => by
        rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, kapSL_inv]
      change ambRep n b⁻¹ ((seedCombCocycle f).1 (conjB b hb p.1, conjB b hb p.2)) =
        ambRep n (kapSL * b)⁻¹ ((seedCombCocycle f).1 (conjB (kapSL * b) hbp p.1, conjB (kapSL * b) hbp p.2))
      rw [hx, hx]
      have hK : (seedCombCocycle f).1 (kapConj (conjB (kapSL * b) hbp p.1), kapConj (conjB (kapSL * b) hbp p.2)) =
          ambRep n kapSL ((seedCombCocycle f).1 (conjB (kapSL * b) hbp p.1, conjB (kapSL * b) hbp p.2)) :=
        seedCombR_kappa hn f _ _
      rw [hK, hk]
    rw [key]
    exact conjCocycle_class_stab (kapSL * b) hs hbp _

/-- **Frame change of the seed combination** (odd `n`): the combination of the line seed classes of `f|Γ₂(N)` and `f^*|Γ₂(N)` at the frame `b h` is the frame transport of the one at `h`, for every
`b ∈ lineBorel`.  (The sign `(-1)ⁿ` is the `ε = +1` combination `σ_f - \overline{σ_{f^*}}` for odd `n`.) -/
theorem seedComb_frame (hn : Odd n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (h b : SL(3, ℤ)) (hb : b ∈ lineBorel) :
    (lineFaceSeedKerClass N n (b * h) (levelN N f)).1 +
        (((-1 : ℝ) ^ n : ℝ) : ℂ) • (lineFaceSeedConjKerClass N n (b * h) (levelN N (fStar f))).1 =
      SeedC3S4c.EdgeNat.h2Map (frameHomQ N h b hb) (lineFaceRep N h n) (lineFaceRep N (b * h) n) (frameT n)
        (frameTQ_intertwines N h n b hb)
        ((lineFaceSeedKerClass N n h (levelN N f)).1 +
          (((-1 : ℝ) ^ n : ℝ) : ℂ) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  rw [seedComb_face N (b * h) f, seedComb_face N h f, classFace_frame N h b hb (seedCombCocycle f), conjCocycle_class hn b hb f]

end Frame2
end TernaryPeriodPolynomials.Argument.LineSeed
