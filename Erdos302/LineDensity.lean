import Erdos302.LineWeights

namespace Erdos302

noncomputable def lineHit {p : ℕ} (l : ResidueLine) (r : ZMod p × ZMod p) : ℝ := by
  classical
  exact if lineCondition l r then 1 else 0

noncomputable def originHit {p : ℕ} (r : ZMod p × ZMod p) : ℝ := by
  classical
  exact if r = (0, 0) then 1 else 0

theorem lineFactor_product_expansion {p : ℕ} (w : ℝ) (r : ZMod p × ZMod p) :
    (∏ l, lineFactor w l r) =
      1 - (1 - w) * (lineHit .leftZero r + lineHit .rightZero r + lineHit .sumZero r) +
        (2 - 3 * w + w ^ 3) * originHit r := by
  classical
  rw [prod_residueLine]
  by_cases ha : r.1 = 0 <;> by_cases hb : r.2 = 0 <;> by_cases hc : r.1 + r.2 = 0 <;>
    simp_all [lineFactor, lineHit, originHit, lineCondition, Prod.ext_iff] <;> ring

theorem sum_lineHit {p : ℕ} [NeZero p] (l : ResidueLine) :
    (∑ r : ZMod p × ZMod p, lineHit l r) = (p : ℝ) := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hset : (Finset.univ.filter (lineCondition l) : Finset (ZMod p × ZMod p)) = lineResidues p l := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_lineResidues hp]
  simp only [lineHit, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hset, card_lineResidues]

theorem sum_originHit {p : ℕ} [NeZero p] : (∑ r : ZMod p × ZMod p, originHit r) = 1 := by
  classical
  simp [originHit]

theorem sum_lineFactor_product {p : ℕ} [NeZero p] (w : ℝ) :
    (∑ r : ZMod p × ZMod p, ∏ l, lineFactor w l r) =
      (p : ℝ) ^ 2 - 3 * (1 - w) * p + (2 - 3 * w + w ^ 3) := by
  simp only [lineFactor_product_expansion, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_lineHit, sum_originHit, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, ZMod.card, Nat.cast_mul, nsmul_eq_mul]
  ring

theorem sum_selectedSurvival {p : ℕ} [NeZero p] (s : ResidueLine → Bool) :
    (∑ r : ZMod p × ZMod p, selectedSurvival s r) =
      (p : ℝ) ^ 2 - (selectedResidues p s).card := by
  classical
  have hpoint (r : ZMod p × ZMod p) : selectedSurvival s r =
      1 - (if r ∈ selectedResidues p s then (1 : ℝ) else 0) := by
    unfold selectedSurvival
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun r hr => hpoint r), Finset.sum_sub_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ, Fintype.card_prod, ZMod.card, Nat.cast_mul, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  ring

theorem selection_density_average {p : ℕ} [NeZero p] (w : ℝ) :
    (∑ s : ResidueLine → Bool, selectionWeight w s *
      (1 - (selectedResidues p s).card / (p : ℝ) ^ 2)) =
      1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2 := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hfrac (s : ResidueLine → Bool) :
      1 - (selectedResidues p s).card / (p : ℝ) ^ 2 =
        (∑ r : ZMod p × ZMod p, selectedSurvival s r) / (p : ℝ) ^ 2 := by
    rw [sum_selectedSurvival]
    field_simp
  calc
    (∑ s : ResidueLine → Bool, selectionWeight w s *
        (1 - (selectedResidues p s).card / (p : ℝ) ^ 2)) =
      (∑ s : ResidueLine → Bool, ∑ r : ZMod p × ZMod p,
        selectionWeight w s * selectedSurvival s r) / (p : ℝ) ^ 2 := by
      simp only [hfrac, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (∑ r : ZMod p × ZMod p, ∑ s : ResidueLine → Bool,
        selectionWeight w s * selectedSurvival s r) / (p : ℝ) ^ 2 := by rw [Finset.sum_comm]
    _ = (∑ r : ZMod p × ZMod p, ∏ l, lineFactor w l r) / (p : ℝ) ^ 2 := by
      simp only [selectedSurvival_average hp]
    _ = ((p : ℝ) ^ 2 - 3 * (1 - w) * p + (2 - 3 * w + w ^ 3)) / (p : ℝ) ^ 2 := by
      rw [sum_lineFactor_product]
    _ = 1 - (3 * (1 - w)) / p + (2 - 3 * w + w ^ 3) / (p : ℝ) ^ 2 := by
      field_simp
      <;> ring

end Erdos302
