import Erdos302.Core
import Erdos302.SmoothSeries

/-! Finite maxima and the exact smooth-prefix series. No assertion connecting
the series to the large-N extremal density is made without proof. -/

namespace Erdos302

open Finset

noncomputable def maximumCard (good : Finset ℕ → Prop) (S : Finset ℕ) : ℕ := by
  classical
  exact (S.powerset.filter good).sup Finset.card

theorem card_le_maximumCard {good : Finset ℕ → Prop} {S A : Finset ℕ}
    (hAS : A ⊆ S) (hgood : good A) : A.card ≤ maximumCard good S := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simp [hAS, hgood])

theorem exists_maximumCard {good : Finset ℕ → Prop} (hzero : good ∅) (S : Finset ℕ) :
    ∃ A ⊆ S, good A ∧ A.card = maximumCard good S := by
  classical
  have hne : (S.powerset.filter good).Nonempty := ⟨∅, by simp [hzero]⟩
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup (S.powerset.filter good) hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hcard.symm⟩

theorem maximumCard_mono {good : Finset ℕ → Prop} (hzero : good ∅)
    {S T : Finset ℕ} (hST : S ⊆ T) : maximumCard good S ≤ maximumCard good T := by
  obtain ⟨A, hAS, hgood, hcard⟩ := exists_maximumCard hzero S
  rw [← hcard]
  exact card_le_maximumCard (hAS.trans hST) hgood

theorem maximumCard_insert_le {good : Finset ℕ → Prop} (hzero : good ∅)
    (hmono : ∀ A B : Finset ℕ, A ⊆ B → good B → good A)
    (S : Finset ℕ) (a : ℕ) : maximumCard good (insert a S) ≤ maximumCard good S + 1 := by
  classical
  obtain ⟨A, hAS, hgood, hcard⟩ := exists_maximumCard hzero (insert a S)
  have herase : A.erase a ⊆ S := by
    intro x hx
    obtain ⟨hxa, hxA⟩ := Finset.mem_erase.mp hx
    simpa [hxa] using hAS hxA
  have hfree : good (A.erase a) := hmono _ _ (Finset.erase_subset _ _) hgood
  have hbound := card_le_maximumCard herase hfree
  have hcardErase := Finset.pred_card_le_card_erase (s := A) (a := a)
  omega

noncomputable def smoothVertices (P : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (· ∈ Nat.factoredNumbers P)

theorem mem_smoothVertices {P : Finset ℕ} {N n : ℕ} :
    n ∈ smoothVertices P N ↔ 1 ≤ n ∧ n ≤ N ∧ n ∈ Nat.factoredNumbers P := by
  classical
  simp only [smoothVertices, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def smoothAlpha (P : Finset ℕ) (N : ℕ) : ℕ :=
  maximumCard NoUnitFractionTriple (smoothVertices P N)

theorem smoothVertices_mono (P : Finset ℕ) : Monotone (smoothVertices P) := by
  intro N M hNM n hn
  obtain ⟨hpos, hbound, hsmooth⟩ := mem_smoothVertices.mp hn
  exact mem_smoothVertices.mpr ⟨hpos, hbound.trans hNM, hsmooth⟩

theorem smoothAlpha_mono (P : Finset ℕ) : Monotone (smoothAlpha P) := by
  intro N M hNM
  exact maximumCard_mono noUnitFractionTriple_empty (smoothVertices_mono P hNM)

theorem smoothAlpha_succ_le (P : Finset ℕ) (N : ℕ) :
    smoothAlpha P (N + 1) ≤ smoothAlpha P N + 1 := by
  classical
  have hsub : smoothVertices P (N + 1) ⊆ insert (N + 1) (smoothVertices P N) := by
    intro n hn
    obtain ⟨hpos, hbound, hsmooth⟩ := mem_smoothVertices.mp hn
    by_cases heq : n = N + 1
    · simp [heq]
    · exact Finset.mem_insert_of_mem (mem_smoothVertices.mpr ⟨hpos, by omega, hsmooth⟩)
  exact (maximumCard_mono noUnitFractionTriple_empty hsub).trans
    (maximumCard_insert_le noUnitFractionTriple_empty
      (fun _ _ hAB hB => noUnitFractionTriple_mono hAB hB) _ _)

theorem smoothAlpha_zero (P : Finset ℕ) : smoothAlpha P 0 = 0 := by
  classical
  simp [smoothAlpha, smoothVertices, maximumCard]

noncomputable def smoothIncrement (P : Finset ℕ) (n : ℕ) : ℕ :=
  smoothAlpha P n - smoothAlpha P (n - 1)

theorem smoothIncrement_le_one (P : Finset ℕ) (n : ℕ) : smoothIncrement P n ≤ 1 := by
  cases n with
  | zero => simp [smoothIncrement]
  | succ n =>
    have h := smoothAlpha_succ_le P n
    simpa only [smoothIncrement, Nat.add_sub_cancel] using Nat.sub_le_iff_le_add.mpr
      (show smoothAlpha P (n + 1) ≤ 1 + smoothAlpha P n by omega)

noncomputable def primeDensity (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)

noncomputable def smoothUpperValue (P : Finset ℕ) : ℝ :=
  primeDensity P * ∑' n : Nat.factoredNumbers P,
    (smoothIncrement P n : ℝ) / (n : ℕ)

theorem smoothUpperValue_series_summable (P : Finset ℕ) :
    Summable (fun n : Nat.factoredNumbers P => (smoothIncrement P n : ℝ) / (n : ℕ)) := by
  apply smooth_weighted_summable
  · intro n
    positivity
  · intro n
    exact_mod_cast smoothIncrement_le_one P n

theorem primeDensity_pos (P : Finset ℕ) : 0 < primeDensity P := by
  apply Finset.prod_pos
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hpPrime.one_lt
  linarith

theorem smoothUpperValue_nonneg (P : Finset ℕ) : 0 ≤ smoothUpperValue P := by
  apply mul_nonneg (primeDensity_pos P).le
  exact tsum_nonneg (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem smoothUpperValue_le_one (P : Finset ℕ) : smoothUpperValue P ≤ 1 := by
  have hsum := smooth_weighted_sum_le P
    (fun n => (smoothIncrement P n : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun n => by exact_mod_cast smoothIncrement_le_one P n)
  have hprod : (∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹) = (primeDensity P)⁻¹ := by
    simp [primeDensity]
  rw [hprod] at hsum
  unfold smoothUpperValue
  exact (mul_le_mul_of_nonneg_left hsum (primeDensity_pos P).le).trans_eq
    (mul_inv_cancel₀ (primeDensity_pos P).ne')

end Erdos302
