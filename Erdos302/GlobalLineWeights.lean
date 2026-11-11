import Erdos302.PrimeSupportWeight

namespace Erdos302

abbrev PrimeSelection (P : Finset ℕ) := ∀ _ : P, ResidueLine → Bool

noncomputable def globalSelectionWeight (P : Finset ℕ) (w : ℝ) (s : PrimeSelection P) : ℝ :=
  ∏ p : P, selectionWeight w (s p)

noncomputable def selectedPrimeResidues (P : Finset ℕ) (s : PrimeSelection P)
    (p : ℕ) : Finset (ZMod p × ZMod p) := by
  classical
  exact if hp : p ∈ P then selectedResidues p (s ⟨p, hp⟩) else ∅

theorem selectedPrimeResidues_of_mem (P : Finset ℕ) (s : PrimeSelection P)
    {p : ℕ} (hp : p ∈ P) : selectedPrimeResidues P s p = selectedResidues p (s ⟨p, hp⟩) := by
  simp only [selectedPrimeResidues, dite_eq_left hp]

theorem globalSelectionWeight_nonneg (P : Finset ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (s : PrimeSelection P) : 0 ≤ globalSelectionWeight P w s := by
  exact Finset.prod_nonneg (fun p hp => selectionWeight_nonneg hw0 hw1 (s p))

theorem globalSelectionWeight_sum (P : Finset ℕ) (w : ℝ) :
    (∑ s : PrimeSelection P, globalSelectionWeight P w s) = 1 := by
  unfold globalSelectionWeight
  rw [← Fintype.prod_sum (fun (_ : P) (s : ResidueLine → Bool) => selectionWeight w s)]
  simp only [selectionWeight_sum, Finset.prod_const_one]

theorem globalDensity_average (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : ℝ) :
    (∑ s : PrimeSelection P, globalSelectionWeight P w s *
      ∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) =
      ∏ p ∈ P, (1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2) := by
  classical
  have hprod (s : PrimeSelection P) :
      (∏ p ∈ P, (1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)) =
        ∏ p : P, (1 - (selectedResidues (p : ℕ) (s p)).card / ((p : ℕ) : ℝ) ^ 2) := by
    rw [← P.prod_coe_sort (fun p : ℕ => 1 - (selectedPrimeResidues P s p).card / (p : ℝ) ^ 2)]
    apply Finset.prod_congr rfl
    intro p hp
    rw [selectedPrimeResidues_of_mem P s p.property]
  simp only [hprod, globalSelectionWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (p : P) (s : ResidueLine → Bool) =>
    selectionWeight w s * (1 - (selectedResidues (p : ℕ) s).card / ((p : ℕ) : ℝ) ^ 2))]
  rw [← P.prod_coe_sort (fun p : ℕ =>
    1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2)]
  apply Finset.prod_congr rfl
  intro p hp
  letI : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  exact selection_density_average w

noncomputable def globalSurvival (P : Finset ℕ) (s : PrimeSelection P) (t : ℕ × ℕ) : ℝ :=
  ∏ p : P, selectedSurvival (s p) ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ)))

theorem globalSurvival_average (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : ℝ) (t : ℕ × ℕ) :
    (∑ s : PrimeSelection P, globalSelectionWeight P w s * globalSurvival P s t) =
      ∏ p : P, ∏ l : ResidueLine, lineFactor w l ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ))) := by
  simp only [globalSelectionWeight, globalSurvival, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (p : P) (s : ResidueLine → Bool) =>
    selectionWeight w s * selectedSurvival s ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ))))]
  apply Finset.prod_congr rfl
  intro p hp
  exact selectedSurvival_average (hP p p.property).pos w _

theorem sum_globalSurvival (P : Finset ℕ) (M : ℕ) (s : PrimeSelection P) :
    (∑ t ∈ integerBox M, globalSurvival P s t) =
      (avoidingPrimes P M (selectedPrimeResidues P s)).card := by
  classical
  let G := avoidingPrimes P M (selectedPrimeResidues P s)
  have hpoint (t : ℕ × ℕ) (ht : t ∈ integerBox M) :
      globalSurvival P s t = if t ∈ G then 1 else 0 := by
    unfold globalSurvival
    by_cases hG : t ∈ G
    · rw [ite_eq_left hG]
      apply Finset.prod_eq_one
      intro p hp
      have hnot := (Finset.mem_filter.mp hG).2 p p.property
      rw [selectedPrimeResidues_of_mem P s p.property] at hnot
      exact ite_eq_right hnot
    · rw [ite_eq_right hG]
      have hbad : ∃ p ∈ P, ((t.1 : ZMod p), (t.2 : ZMod p)) ∈ selectedPrimeResidues P s p := by
        by_contra h
        push Not at h
        exact hG (Finset.mem_filter.mpr ⟨ht, h⟩)
      obtain ⟨p, hp, hbad⟩ := hbad
      rw [selectedPrimeResidues_of_mem P s hp] at hbad
      have hz : selectedSurvival (s ⟨p, hp⟩) ((t.1 : ZMod p), (t.2 : ZMod p)) = 0 := by
        simp only [selectedSurvival, ite_eq_left hbad]
      exact Finset.prod_eq_zero (f := fun p : P =>
        selectedSurvival (s p) ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ))))
        (Finset.mem_univ (⟨p, hp⟩ : P)) hz
  rw [Finset.sum_congr rfl hpoint, ← Finset.sum_filter]
  have hset : (integerBox M).filter (fun t => t ∈ G) = G := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
  rw [hset]
  simp [G]

theorem globalCard_average (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) (w : ℝ) :
    (∑ s : PrimeSelection P, globalSelectionWeight P w s *
      (avoidingPrimes P M (selectedPrimeResidues P s)).card) =
      ∑ t ∈ integerBox M, ∏ p : P, ∏ l : ResidueLine,
        lineFactor w l ((t.1 : ZMod (p : ℕ)), (t.2 : ZMod (p : ℕ))) := by
  simp only [← sum_globalSurvival P M, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  exact globalSurvival_average P hP w t

end Erdos302
