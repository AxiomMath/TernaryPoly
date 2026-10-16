module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.FiveFrame

@[expose] public section



/-! Basepoint `formPairing` at degrees 5 and 4, collapsed from the generic sum over all
`Fin k → Fin 5` (`formPairing_basepoint_frame`) down to a sum over permutations / sectors.
Degree 5: every non-bijective `I : Fin 5 → Fin 5` contributes zero (repeated argument), so the
sum collapses to a sum over `Equiv.Perm (Fin 5)`, and then to the single `baseFrame` term since
all signs cancel in pairs. Degree 4: every non-injective `I : Fin 4 → Fin 5` contributes zero,
and each injective `I` is `sectorFrame i0 ∘ τ` for a unique missing index `i0` and a unique
`τ : Equiv.Perm (Fin 4)`, so the sum collapses to a sum over `i0` (with the `τ`-sum again
cancelling via signs). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- `factorialPairing_sign_smul_self` generalized to a mixed pairing of two (possibly different)
values, for a permutation of any finite index type. -/
theorem factorialPairing_sign_smul_sign_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (x y : Poly) :
    factorialPairing (Equiv.Perm.sign σ • x) (Equiv.Perm.sign σ • y) = factorialPairing x y := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Degree-5 basepoint `formPairing` collapses to the bare `baseFrame` pairing: every
non-bijective `I : Fin 5 → Fin 5` contributes zero, and every bijective one gives the same
value as `baseFrame` itself (its sign cancels against itself in the mixed pairing). -/
theorem formPairing_basepoint_five (n : ℕ) (a b : FormValue n 5) :
    formPairing n 5 (coordinateChart basepoint) a b =
      (∏ j : Fin 5, tangentWeight j) * factorialPairing (a baseFrame).val (b baseFrame).val := by
  rw [formPairing_basepoint_frame]
  set F : (Fin 5 → Fin 5) → ℝ := fun I => (∏ r, tangentWeight (I r)) *
    factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val
    with hF
  have hzero : ∀ I : Fin 5 → Fin 5, ¬ Function.Injective I → F I = 0 := by
    intro I hI
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hI
    have hval : (fun r => baseFrame (I r)) i = (fun r => baseFrame (I r)) j := by
      simp only [hij]
    have ha0 : a (fun r => baseFrame (I r)) = 0 :=
      AlternatingMap.map_eq_zero_of_eq a.toAlternatingMap _ hval hne
    simp [hF, ha0]
  have hbij : ∀ I : Fin 5 → Fin 5, Function.Injective I → Function.Bijective I :=
    fun I hI => (Fintype.bijective_iff_injective_and_card I).mpr ⟨hI, rfl⟩
  have hcoeinj : Set.InjOn (fun σ : Equiv.Perm (Fin 5) => (σ : Fin 5 → Fin 5))
      (↑(Finset.univ : Finset (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) := by
    intro σ₁ _ σ₂ _ h
    apply Equiv.ext
    intro x
    exact congrFun h x
  have hS : (∑ I : Fin 5 → Fin 5, F I) =
      ∑ I ∈ Finset.image (fun σ : Equiv.Perm (Fin 5) => (σ : Fin 5 → Fin 5)) Finset.univ, F I := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro I _ hnotmem
    apply hzero
    intro hinj
    exact hnotmem (Finset.mem_image.mpr ⟨Equiv.ofBijective I (hbij I hinj), Finset.mem_univ _, rfl⟩)
  rw [hF] at hS ⊢
  rw [hS, Finset.sum_image hcoeinj]
  have hterm : ∀ σ : Equiv.Perm (Fin 5),
      (∏ r, tangentWeight ((σ : Fin 5 → Fin 5) r)) *
        factorialPairing (a (fun r => baseFrame ((σ : Fin 5 → Fin 5) r))).val
          (b (fun r => baseFrame ((σ : Fin 5 → Fin 5) r))).val =
      (∏ j : Fin 5, tangentWeight j) * factorialPairing (a baseFrame).val (b baseFrame).val := by
    intro σ
    have hprod : (∏ r, tangentWeight ((σ : Fin 5 → Fin 5) r)) = ∏ j : Fin 5, tangentWeight j :=
      Equiv.prod_comp σ tangentWeight
    have hcompa : (fun r => baseFrame ((σ : Fin 5 → Fin 5) r)) = baseFrame ∘ σ := rfl
    have hA : a (baseFrame ∘ σ) = Equiv.Perm.sign σ • a baseFrame := by
      have := AlternatingMap.map_perm a.toAlternatingMap baseFrame σ
      simpa using this
    have hB : b (baseFrame ∘ σ) = Equiv.Perm.sign σ • b baseFrame := by
      have := AlternatingMap.map_perm b.toAlternatingMap baseFrame σ
      simpa using this
    rw [hprod, hcompa, hA, hB]
    congr 1
    have hvA : (Equiv.Perm.sign σ • a baseFrame).val = Equiv.Perm.sign σ • (a baseFrame).val := by
      simp
    have hvB : (Equiv.Perm.sign σ • b baseFrame).val = Equiv.Perm.sign σ • (b baseFrame).val := by
      simp
    rw [hvA, hvB, factorialPairing_sign_smul_sign_smul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [show (Nat.factorial 5 : ℝ) = ((5 : ℕ).factorial : ℝ) from rfl]
  field_simp

/-- The index-level sector frame at `i0`: the four slots of `Fin 5` other than `i0`, in the
order used by `sectorFrame`. -/
def sectorFrameIndex (i0 : Fin 5) : Fin 4 → Fin 5 := fun r => moveFrontEquiv i0 r.succ

theorem sectorFrame_eq_sectorFrameIndex (i0 : Fin 5) :
    sectorFrame i0 = fun r => baseFrame (sectorFrameIndex i0 r) := rfl

theorem moveFrontEquiv_zero (i0 : Fin 5) : moveFrontEquiv i0 0 = i0 :=
  (moveFrontEquiv_apply i0 0).trans (moveFrontTable_zero i0)

theorem sectorFrameIndex_injective (i0 : Fin 5) : Function.Injective (sectorFrameIndex i0) :=
  fun _ _ h => Fin.succ_injective 4 ((moveFrontEquiv i0).injective h)

theorem sectorFrameIndex_ne (i0 : Fin 5) (r : Fin 4) : sectorFrameIndex i0 r ≠ i0 := by
  show moveFrontEquiv i0 r.succ ≠ i0
  intro h
  exact Fin.succ_ne_zero r
    ((moveFrontEquiv i0).injective (h.trans (moveFrontEquiv_zero i0).symm))

theorem sectorFrameIndex_image (i0 : Fin 5) :
    Finset.image (sectorFrameIndex i0) Finset.univ = Finset.univ.erase i0 := by
  apply Finset.ext
  intro j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨sectorFrameIndex_ne i0 r, trivial⟩
  · rintro ⟨hne, -⟩
    have hne0 : (moveFrontEquiv i0).symm j ≠ 0 := by
      intro h
      apply hne
      rw [← moveFrontEquiv_zero i0, ← h, Equiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := Fin.eq_succ_of_ne_zero hne0
    exact ⟨r, by show moveFrontEquiv i0 r.succ = j; rw [← hr, Equiv.apply_symm_apply]⟩

/-- Every injective `Fin 4 → Fin 5` is `sectorFrameIndex i0 ∘ τ` for the index `i0` missing from
its range and a (unique) `τ : Equiv.Perm (Fin 4)`. -/
theorem exists_sectorFrameIndex_comp (I : Fin 4 → Fin 5) (hI : Function.Injective I) :
    ∃ (i0 : Fin 5) (τ : Equiv.Perm (Fin 4)), I = fun r => sectorFrameIndex i0 (τ r) := by
  have hcard : (Finset.image I Finset.univ).card = 4 := by
    rw [Finset.card_image_of_injective _ hI, Finset.card_univ, Fintype.card_fin]
  have hcompl : (Finset.image I Finset.univ)ᶜ.card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hcompl
  have hi0mem : i0 ∈ (Finset.image I Finset.univ)ᶜ := hi0 ▸ Finset.mem_singleton_self i0
  have hi0notmem : i0 ∉ Finset.image I Finset.univ := Finset.mem_compl.mp hi0mem
  have hne : ∀ r : Fin 4, I r ≠ i0 := by
    intro r hr
    exact hi0notmem (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩)
  have hne0 : ∀ r : Fin 4, (moveFrontEquiv i0).symm (I r) ≠ 0 := by
    intro r h
    apply hne r
    rw [← moveFrontEquiv_zero i0, ← h, Equiv.apply_symm_apply]
  set τ : Fin 4 → Fin 4 := fun r => ((moveFrontEquiv i0).symm (I r)).pred (hne0 r) with hτdef
  have hτsucc : ∀ r, (τ r).succ = (moveFrontEquiv i0).symm (I r) := by
    intro r; simp [hτdef, Fin.succ_pred]
  have hτinj : Function.Injective τ := by
    intro r r' h
    apply hI
    apply (moveFrontEquiv i0).symm.injective
    rw [← hτsucc r, ← hτsucc r', h]
  have hτbij : Function.Bijective τ := (Fintype.bijective_iff_injective_and_card τ).mpr ⟨hτinj, rfl⟩
  refine ⟨i0, Equiv.ofBijective τ hτbij, ?_⟩
  funext r
  show I r = sectorFrameIndex i0 (τ r)
  show I r = moveFrontEquiv i0 (τ r).succ
  rw [hτsucc, Equiv.apply_symm_apply]

/-- Degree-4 basepoint `formPairing` collapses to a sum, over the missing index `i0`, of the
`sectorFrame i0` pairing weighted by the product of `tangentWeight` over the sector. -/
theorem formPairing_basepoint_four (n : ℕ) (a b : FormValue n 4) :
    formPairing n 4 (coordinateChart basepoint) a b =
      ∑ i0 : Fin 5, (∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r)) *
        factorialPairing (a (sectorFrame i0)).val (b (sectorFrame i0)).val := by
  rw [formPairing_basepoint_frame]
  set F : (Fin 4 → Fin 5) → ℝ := fun I => (∏ r, tangentWeight (I r)) *
    factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val
    with hF
  have hzero : ∀ I : Fin 4 → Fin 5, ¬ Function.Injective I → F I = 0 := by
    intro I hI
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hI
    have hval : (fun r => baseFrame (I r)) i = (fun r => baseFrame (I r)) j := by
      simp only [hij]
    have ha0 : a (fun r => baseFrame (I r)) = 0 :=
      AlternatingMap.map_eq_zero_of_eq a.toAlternatingMap _ hval hne
    simp [hF, ha0]
  set G : Fin 5 × Equiv.Perm (Fin 4) → (Fin 4 → Fin 5) :=
    fun p => fun r => sectorFrameIndex p.1 (p.2 r) with hG
  have hcoeinj : Set.InjOn G (↑(Finset.univ : Finset (Fin 5 × Equiv.Perm (Fin 4))) :
      Set (Fin 5 × Equiv.Perm (Fin 4))) := by
    intro p _ q _ h
    have hGp : G p = sectorFrameIndex p.1 ∘ (p.2 : Fin 4 → Fin 4) := by rw [hG]; rfl
    have hGq : G q = sectorFrameIndex q.1 ∘ (q.2 : Fin 4 → Fin 4) := by rw [hG]; rfl
    have himg : Finset.image (sectorFrameIndex p.1) Finset.univ =
        Finset.image (sectorFrameIndex q.1) Finset.univ := by
      have hp : Finset.image (sectorFrameIndex p.1) Finset.univ = Finset.image (G p) Finset.univ := by
        rw [hGp, ← Finset.image_image, Finset.image_univ_of_surjective p.2.surjective]
      have hq : Finset.image (sectorFrameIndex q.1) Finset.univ = Finset.image (G q) Finset.univ := by
        rw [hGq, ← Finset.image_image, Finset.image_univ_of_surjective q.2.surjective]
      rw [hp, hq, h]
    rw [sectorFrameIndex_image, sectorFrameIndex_image] at himg
    have hp1q1 : p.1 = q.1 := by
      by_contra hne
      have hmem : q.1 ∈ Finset.univ.erase p.1 :=
        Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩
      rw [himg] at hmem
      simp [Finset.mem_erase] at hmem
    have hp2q2 : p.2 = q.2 := by
      apply Equiv.ext
      intro r
      have hcf : G p r = G q r := congrFun h r
      rw [hG] at hcf
      simp only at hcf
      rw [hp1q1] at hcf
      exact sectorFrameIndex_injective q.1 hcf
    exact Prod.ext hp1q1 hp2q2
  have hS : (∑ I : Fin 4 → Fin 5, F I) =
      ∑ I ∈ Finset.image G Finset.univ, F I := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro I _ hnotmem
    apply hzero
    intro hinj
    obtain ⟨i0, τ, hI⟩ := exists_sectorFrameIndex_comp I hinj
    have hGi0τ : G (i0, τ) = I := by rw [hG]; exact hI.symm
    exact hnotmem (Finset.mem_image.mpr ⟨(i0, τ), Finset.mem_univ _, hGi0τ⟩)
  rw [hF] at hS ⊢
  rw [hS, Finset.sum_image hcoeinj]
  have hterm : ∀ p : Fin 5 × Equiv.Perm (Fin 4),
      (∏ r, tangentWeight (G p r)) *
        factorialPairing (a (fun r => baseFrame (G p r))).val
          (b (fun r => baseFrame (G p r))).val =
      (∏ r : Fin 4, tangentWeight (sectorFrameIndex p.1 r)) *
        factorialPairing (a (sectorFrame p.1)).val (b (sectorFrame p.1)).val := by
    intro p
    obtain ⟨i0, τ⟩ := p
    have hprod : (∏ r, tangentWeight (G (i0, τ) r)) =
        ∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r) := by
      rw [hG]
      exact Equiv.prod_comp τ (fun r => tangentWeight (sectorFrameIndex i0 r))
    have hcompa : (fun r => baseFrame (G (i0, τ) r)) = sectorFrame i0 ∘ (τ : Fin 4 → Fin 4) := by
      rw [hG, sectorFrame_eq_sectorFrameIndex]
      rfl
    have hA : a (sectorFrame i0 ∘ (τ : Fin 4 → Fin 4)) = Equiv.Perm.sign τ • a (sectorFrame i0) := by
      have := AlternatingMap.map_perm a.toAlternatingMap (sectorFrame i0) τ
      simpa using this
    have hB : b (sectorFrame i0 ∘ (τ : Fin 4 → Fin 4)) = Equiv.Perm.sign τ • b (sectorFrame i0) := by
      have := AlternatingMap.map_perm b.toAlternatingMap (sectorFrame i0) τ
      simpa using this
    show (∏ r, tangentWeight (G (i0, τ) r)) *
      factorialPairing (a (fun r => baseFrame (G (i0, τ) r))).val
        (b (fun r => baseFrame (G (i0, τ) r))).val =
      (∏ r : Fin 4, tangentWeight (sectorFrameIndex i0 r)) *
        factorialPairing (a (sectorFrame i0)).val (b (sectorFrame i0)).val
    rw [hprod, hcompa, hA, hB]
    congr 1
    have hvA : (Equiv.Perm.sign τ • a (sectorFrame i0)).val =
        Equiv.Perm.sign τ • (a (sectorFrame i0)).val := by simp
    have hvB : (Equiv.Perm.sign τ • b (sectorFrame i0)).val =
        Equiv.Perm.sign τ • (b (sectorFrame i0)).val := by simp
    rw [hvA, hvB, factorialPairing_sign_smul_sign_smul]
  simp only [hterm]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [show (Nat.factorial 4 : ℝ) = ((4 : ℕ).factorial : ℝ) from rfl, ← Finset.mul_sum]
  field_simp

end TernaryPeriodPolynomials.Argument.Coercivity
