import Erdos302.ResidueLines

namespace Erdos302

def lineChoiceWeight (w : ℝ) (b : Bool) : ℝ := if b = true then 1 - w else w

noncomputable def selectionWeight (w : ℝ) (s : ResidueLine → Bool) : ℝ :=
  ∏ l, lineChoiceWeight w (s l)

noncomputable def lineSurvival {p : ℕ} (l : ResidueLine) (b : Bool) (r : ZMod p × ZMod p) : ℝ := by
  classical
  exact if b = true ∧ lineCondition l r then 0 else 1

noncomputable def selectedSurvival {p : ℕ} (s : ResidueLine → Bool) (r : ZMod p × ZMod p) : ℝ := by
  classical
  exact if r ∈ selectedResidues p s then 0 else 1

noncomputable def lineFactor {p : ℕ} (w : ℝ) (l : ResidueLine) (r : ZMod p × ZMod p) : ℝ := by
  classical
  exact if lineCondition l r then w else 1

theorem selectionWeight_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (s : ResidueLine → Bool) :
    0 ≤ selectionWeight w s := by
  apply Finset.prod_nonneg
  intro l hl
  unfold lineChoiceWeight
  split_ifs <;> linarith

theorem selectionWeight_sum (w : ℝ) : (∑ s : ResidueLine → Bool, selectionWeight w s) = 1 := by
  unfold selectionWeight
  rw [← Fintype.prod_sum]
  simp [lineChoiceWeight, Fintype.sum_bool]

theorem selectedSurvival_product {p : ℕ} (hp : 0 < p) (s : ResidueLine → Bool)
    (r : ZMod p × ZMod p) : selectedSurvival s r = ∏ l, lineSurvival l (s l) r := by
  classical
  by_cases h : r ∈ selectedResidues p s
  · obtain ⟨l, hl, hcond⟩ := (mem_selectedResidues hp s r).mp h
    have hzero : lineSurvival l (s l) r = 0 := by simp [lineSurvival, hl, hcond]
    have hprod : (∏ k, lineSurvival k (s k) r) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ l) hzero
    simp only [selectedSurvival, ite_eq_left h, hprod]
  · have hprod : (∏ l, lineSurvival l (s l) r) = 1 := by
      apply Finset.prod_eq_one
      intro l hl
      have hnot : ¬ (s l = true ∧ lineCondition l r) := by
        intro hc
        exact h ((mem_selectedResidues hp s r).mpr ⟨l, hc⟩)
      simp only [lineSurvival, ite_eq_right hnot]
    simp only [selectedSurvival, ite_eq_right h, hprod]

theorem selectedSurvival_average {p : ℕ} (hp : 0 < p) (w : ℝ) (r : ZMod p × ZMod p) :
    (∑ s : ResidueLine → Bool, selectionWeight w s * selectedSurvival s r) =
      ∏ l : ResidueLine, lineFactor w l r := by
  classical
  simp only [selectedSurvival_product hp, selectionWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (l : ResidueLine) (b : Bool) => lineChoiceWeight w b * lineSurvival l b r)]
  apply Finset.prod_congr rfl
  intro l hl
  by_cases hc : lineCondition l r
  · simp [lineChoiceWeight, lineSurvival, lineFactor, Fintype.sum_bool, hc]
  · simp [lineChoiceWeight, lineSurvival, lineFactor, Fintype.sum_bool, hc]

theorem prod_residueLine (f : ResidueLine → ℝ) :
    (∏ l, f l) = f .leftZero * f .rightZero * f .sumZero := by
  have huniv : (Finset.univ : Finset ResidueLine) = {.leftZero, .rightZero, .sumZero} := by
    ext l
    cases l <;> simp
  rw [huniv]
  simp [mul_assoc]

end Erdos302
