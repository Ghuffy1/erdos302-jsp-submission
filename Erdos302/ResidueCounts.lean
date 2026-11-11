import Erdos302.SelbergUpperBound
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.ZMod.QuotientRing

namespace Erdos302

noncomputable def residueCount (q M : ℕ) (r : ZMod q) : ℕ := by
  classical
  exact ((Finset.Icc 1 M).filter (fun n : ℕ => (n : ZMod q) = r)).card

theorem residue_count_one_period {q : ℕ} (hq : 0 < q) (r : ZMod q) (t : ℕ) :
    ((Finset.Ico t (t + q)).filter (fun n : ℕ => (n : ZMod q) = r)).card = 1 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hperiod : Function.Periodic (fun n : ℕ => (n : ZMod q) = r) q := by
    intro n
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [Nat.filter_Ico_card_eq_of_periodic t q _ hperiod, Nat.count_eq_card_filter_range]
  have hset : (Finset.range q).filter (fun n : ℕ => (n : ZMod q) = r) = {r.val} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hnq, hn⟩
      have h := congrArg ZMod.val hn
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hnq] using h
    · intro hn
      subst n
      exact ⟨ZMod.val_lt r, ZMod.natCast_zmod_val r⟩
  rw [hset, Finset.card_singleton]

theorem residue_count_blocks {q : ℕ} (hq : 0 < q) (r : ZMod q) (k t : ℕ) :
    ((Finset.Ico t (t + q * k)).filter (fun n : ℕ => (n : ZMod q) = r)).card = k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Ico t (t + q * (k + 1)) =
        Finset.Ico t (t + q * k) ∪ Finset.Ico (t + q * k) (t + q * k + q) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1
      ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [ih, residue_count_one_period hq r]
    · exact (Finset.Ico_disjoint_Ico_consecutive t (t + q * k) (t + q * k + q)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem residueCount_bounds {q : ℕ} (hq : 0 < q) (M : ℕ) (r : ZMod q) :
    M / q ≤ residueCount q M r ∧ residueCount q M r ≤ M / q + 1 := by
  classical
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold residueCount
  rw [hIcc]
  constructor
  · rw [← residue_count_blocks hq r (M / q) 1]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico le_rfl
    have h := Nat.div_mul_le_self M q
    nlinarith
  · rw [← residue_count_blocks hq r (M / q + 1) 1]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico le_rfl
    have hm := Nat.mod_add_div M q
    have hr := Nat.mod_lt M hq
    nlinarith

theorem residueCount_error {q : ℕ} (hq : 0 < q) (M : ℕ) (r : ZMod q) :
    |(residueCount q M r : ℝ) - (M : ℝ) / q| ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hl, hu⟩ := residueCount_bounds hq M r
  have hlR : ((M / q : ℕ) : ℝ) ≤ residueCount q M r := by exact_mod_cast hl
  have huR : (residueCount q M r : ℝ) ≤ (M / q : ℕ) + 1 := by exact_mod_cast hu
  have hdiv : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q := Nat.cast_div_le
  have hdivUpper : (M : ℝ) / q ≤ ((M / q : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hqR).mpr
    have hnat : M ≤ (M / q + 1) * q := by
      have hm := Nat.mod_add_div M q
      have hr := Nat.mod_lt M hq
      nlinarith
    exact_mod_cast hnat
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def integerBox (M : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 M ×ˢ Finset.Icc 1 M

noncomputable def residueBoxCount (q M : ℕ) (U : Finset (ZMod q × ZMod q)) : ℕ := by
  classical
  exact ((integerBox M).filter (fun t : ℕ × ℕ => ((t.1 : ZMod q), (t.2 : ZMod q)) ∈ U)).card

theorem residueBoxCount_fibers (q M : ℕ) (U : Finset (ZMod q × ZMod q)) :
    residueBoxCount q M U = ∑ r ∈ U, residueCount q M r.1 * residueCount q M r.2 := by
  classical
  unfold residueBoxCount
  rw [← Finset.sum_card_fiberwise_eq_card_filter (integerBox M) U
    (fun t : ℕ × ℕ => ((t.1 : ZMod q), (t.2 : ZMod q)))]
  apply Finset.sum_congr rfl
  intro r hr
  have hset : (integerBox M).filter (fun t : ℕ × ℕ => ((t.1 : ZMod q), (t.2 : ZMod q)) = r) =
      ((Finset.Icc 1 M).filter (fun n : ℕ => (n : ZMod q) = r.1)) ×ˢ
        ((Finset.Icc 1 M).filter (fun n : ℕ => (n : ZMod q) = r.2)) := by
    ext t
    simp only [integerBox, Finset.mem_filter, Finset.mem_product, Prod.ext_iff]
    tauto
  rw [hset, Finset.card_product]
  rfl

theorem product_error_of_unit_errors {a b x : ℝ} (hx : 0 ≤ x)
    (ha : |a - x| ≤ 1) (hb : |b - x| ≤ 1) : |a * b - x ^ 2| ≤ 2 * x + 1 := by
  have hab : |(a - x) * (b - x)| ≤ 1 := by
    rw [abs_mul]
    have h := mul_le_mul ha hb (abs_nonneg (b - x)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hxa : |x * (a - x)| ≤ x := by
    rw [abs_mul, abs_of_nonneg hx]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha hx
  have hxb : |x * (b - x)| ≤ x := by
    rw [abs_mul, abs_of_nonneg hx]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hx
  calc
    |a * b - x ^ 2| = |(a - x) * (b - x) + x * (a - x) + x * (b - x)| := by congr 1; ring
    _ ≤ |(a - x) * (b - x)| + |x * (a - x)| + |x * (b - x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * x + 1 := by linarith

theorem residueBoxCount_error_sharp {q : ℕ} (hq : 0 < q) (M : ℕ)
    (U : Finset (ZMod q × ZMod q)) :
    |(residueBoxCount q M U : ℝ) - (U.card : ℝ) * ((M : ℝ) / q) ^ 2| ≤
      (U.card : ℝ) * (2 * (M : ℝ) / q + 1) := by
  rw [residueBoxCount_fibers, Nat.cast_sum]
  simp only [Nat.cast_mul]
  have heq : (∑ r ∈ U, (residueCount q M r.1 : ℝ) * residueCount q M r.2) -
      (U.card : ℝ) * ((M : ℝ) / q) ^ 2 =
      ∑ r ∈ U, ((residueCount q M r.1 : ℝ) * residueCount q M r.2 - ((M : ℝ) / q) ^ 2) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    |∑ r ∈ U, ((residueCount q M r.1 : ℝ) * residueCount q M r.2 - ((M : ℝ) / q) ^ 2)| ≤
        ∑ r ∈ U, |(residueCount q M r.1 : ℝ) * residueCount q M r.2 - ((M : ℝ) / q) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ U, (2 * (M : ℝ) / q + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := product_error_of_unit_errors (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg q))
        (residueCount_error hq M r.1) (residueCount_error hq M r.2)
      simpa only [mul_div_assoc] using h
    _ = (U.card : ℝ) * (2 * (M : ℝ) / q + 1) := by simp; ring

theorem residueBoxCount_error {q : ℕ} (hq : 0 < q) (M : ℕ)
    (U : Finset (ZMod q × ZMod q)) :
    |(residueBoxCount q M U : ℝ) - (M : ℝ) ^ 2 * ((U.card : ℝ) / (q : ℝ) ^ 2)| ≤
      2 * M * q + (q : ℝ) ^ 2 := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : (U.card : ℝ) ≤ (q : ℝ) ^ 2 := by
    have h : U.card ≤ q ^ 2 := by simpa [pow_two] using U.card_le_univ
    exact_mod_cast h
  have heq : (U.card : ℝ) * ((M : ℝ) / q) ^ 2 =
      (M : ℝ) ^ 2 * ((U.card : ℝ) / (q : ℝ) ^ 2) := by ring
  rw [← heq]
  calc
    |(residueBoxCount q M U : ℝ) - (U.card : ℝ) * ((M : ℝ) / q) ^ 2| ≤
        (U.card : ℝ) * (2 * (M : ℝ) / q + 1) := residueBoxCount_error_sharp hq M U
    _ ≤ (q : ℝ) ^ 2 * (2 * (M : ℝ) / q + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * M * q + (q : ℝ) ^ 2 := by field_simp

end Erdos302
