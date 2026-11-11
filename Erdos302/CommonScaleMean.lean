import Erdos302.WeightedEuler

namespace Erdos302

open scoped ArithmeticFunction.vonMangoldt

theorem Icc_div_eq_filter_mul (N d : ℕ) (hd : 0 < d) :
    Finset.Icc 1 (N / d) = (Finset.Icc 1 N).filter (fun m => d * m ≤ N) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨hm1, hmd⟩
    have hmul : d * m ≤ N := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmd
    have hmN : m ≤ N := (Nat.le_mul_of_pos_left m hd).trans hmul
    exact ⟨⟨hm1, hmN⟩, hmul⟩
  · rintro ⟨⟨hm1, hmN⟩, hmul⟩
    exact ⟨hm1, (Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using hmul)⟩

theorem sum_div_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), f d m) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / m), f d m := by
  calc
    (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), f d m) =
        ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, if d * m ≤ N then f d m else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Icc_div_eq_filter_mul N d (by have := (Finset.mem_Icc.mp hd).1; omega),
        Finset.sum_filter]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d * m ≤ N then f d m else 0 :=
      Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / m), f d m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Icc_div_eq_filter_mul N m (by have := (Finset.mem_Icc.mp hm).1; omega),
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      rw [mul_comm m d]

theorem divisors_eq_filter_Icc {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdvd, hn0⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    exact ⟨⟨hd0, (Nat.le_of_dvd hn hdvd).trans hnN⟩, hdvd⟩
  · rintro ⟨⟨hd1, hdN⟩, hdvd⟩
    exact ⟨hdvd, hn.ne'⟩

theorem weight_sum_multiples (t : ℝ) (X N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), t ^ smallOmega n X) =
      t ^ smallOmega d X * ∑ m ∈ Finset.Icc 1 (N / d), t ^ smallOmega m X := by
  rw [multiples_Icc_image hd, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [smallOmega_mul hd.ne' hm0, pow_add]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab

theorem log_weighted_sum_identity (t : ℝ) (X N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n) =
      ∑ d ∈ Finset.Icc 1 N, (Λ d * t ^ smallOmega d X) *
        ∑ m ∈ Finset.Icc 1 (N / d), t ^ smallOmega m X := by
  have hn (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      t ^ smallOmega n X * Real.log n =
        ∑ d ∈ Finset.Icc 1 N, if d ∣ n then t ^ smallOmega n X * Λ d else 0 := by
    rw [← ArithmeticFunction.vonMangoldt_sum, Finset.mul_sum,
      divisors_eq_filter_Icc (by have := (Finset.mem_Icc.mp hn).1; omega)
        (Finset.mem_Icc.mp hn).2, Finset.sum_filter]
  rw [Finset.sum_congr rfl hn, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  calc
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then t ^ smallOmega n X * Λ d else 0) =
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), t ^ smallOmega n X) * Λ d := by
      rw [Finset.sum_mul, Finset.sum_filter]
    _ = (Λ d * t ^ smallOmega d X) *
        ∑ m ∈ Finset.Icc 1 (N / d), t ^ smallOmega m X := by
      rw [weight_sum_multiples t X N d hd0]
      ring

theorem log_weighted_sum_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (X N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n) ≤
      4 * N * ∑ m ∈ Finset.Icc 1 N, t ^ smallOmega m X / m := by
  rw [log_weighted_sum_identity]
  calc
    (∑ d ∈ Finset.Icc 1 N, (Λ d * t ^ smallOmega d X) *
        ∑ m ∈ Finset.Icc 1 (N / d), t ^ smallOmega m X) ≤
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), Λ d * t ^ smallOmega m X := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← Finset.mul_sum]
      have hW : t ^ smallOmega d X ≤ 1 := pow_le_one₀ ht0 ht1
      have hLambda : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      have hS : 0 ≤ ∑ m ∈ Finset.Icc 1 (N / d), t ^ smallOmega m X :=
        Finset.sum_nonneg (fun m hm => pow_nonneg ht0 _)
      nlinarith [mul_le_mul_of_nonneg_left hW hLambda]
    _ = ∑ m ∈ Finset.Icc 1 N, (t ^ smallOmega m X) *
        ∑ d ∈ Finset.Icc 1 (N / m), Λ d := by
      rw [sum_div_swap]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (t ^ smallOmega m X) * (4 * (N : ℝ) / m) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht0 _)
      have hpsi : (∑ d ∈ Finset.Icc 1 (N / m), Λ d) = Chebyshev.psi (N / m : ℕ) := by
        simp only [Chebyshev.psi, Nat.floor_natCast]
        congr 1
      rw [hpsi]
      have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
      have hp := psi_le_four_mul (Nat.cast_nonneg (N / m))
      exact hp.trans (by simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 4))
    _ = 4 * N * ∑ m ∈ Finset.Icc 1 N, t ^ smallOmega m X / m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

theorem weight_sum_sqrt_split {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤ Real.sqrt N +
      (2 / Real.log N) * ∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n := by
  classical
  let M := ⌊Real.sqrt N⌋₊
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      t ^ smallOmega n X ≤ (if n ≤ M then 1 else 0) +
        (2 / Real.log N) * (t ^ smallOmega n X * Real.log n) := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hW0 : 0 ≤ t ^ smallOmega n X := pow_nonneg ht0 _
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    by_cases hnM : n ≤ M
    · rw [ite_eq_left hnM]
      have hW1 : t ^ smallOmega n X ≤ 1 := pow_le_one₀ ht0 ht1
      have he : 0 ≤ (2 / Real.log N) * (t ^ smallOmega n X * Real.log n) := by positivity
      linarith
    · rw [ite_eq_right hnM, zero_add]
      have hsqrtn : Real.sqrt N < (n : ℝ) := by
        by_contra hnot
        have hle : n ≤ M := Nat.le_floor (le_of_not_gt hnot)
        exact hnM hle
      have hlogn' : Real.log N / 2 ≤ Real.log n := by
        have h := Real.log_le_log (Real.sqrt_pos.mpr hNR) hsqrtn.le
        rwa [Real.log_sqrt hNR.le] at h
      have hratio : (1 : ℝ) ≤ 2 * Real.log n / Real.log N :=
        (le_div_iff₀ hlogN).mpr (by linarith)
      have h := mul_le_mul_of_nonneg_right hratio hW0
      calc
        t ^ smallOmega n X = 1 * t ^ smallOmega n X := by ring
        _ ≤ (2 * Real.log n / Real.log N) * t ^ smallOmega n X := h
        _ = (2 / Real.log N) * (t ^ smallOmega n X * Real.log n) := by ring
  have hsmall : (∑ n ∈ Finset.Icc 1 N, if n ≤ M then (1 : ℝ) else 0) ≤ Real.sqrt N := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.Icc 1 N).filter (fun n => n ≤ M) ⊆ Finset.Icc 1 M := by
      intro n hn
      obtain ⟨hnI, hnM⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, hnM⟩
    have hc : ((Finset.Icc 1 N).filter (fun n => n ≤ M)).card ≤ M := by
      simpa using Finset.card_le_card hsub
    exact (show ((((Finset.Icc 1 N).filter (fun n => n ≤ M)).card : ℕ) : ℝ) ≤ M by
      exact_mod_cast hc).trans (Nat.floor_le (Real.sqrt_nonneg N))
  calc
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤
        ∑ n ∈ Finset.Icc 1 N, ((if n ≤ M then 1 else 0) +
          (2 / Real.log N) * (t ^ smallOmega n X * Real.log n)) := Finset.sum_le_sum hpoint
    _ = (∑ n ∈ Finset.Icc 1 N, if n ≤ M then (1 : ℝ) else 0) +
        (2 / Real.log N) * ∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.sqrt N + (2 / Real.log N) *
        ∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n := add_le_add hsmall le_rfl

theorem weight_sum_harmonic_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X N : ℕ) (hX : 2 ≤ X) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤
      Real.sqrt N + 8 * Real.exp 13 * N * (Real.log (min N X)) ^ (t - 1) := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤ Real.sqrt N +
        (2 / Real.log N) * ∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X * Real.log n :=
      weight_sum_sqrt_split ht0 ht1 X N hN
    _ ≤ Real.sqrt N + (2 / Real.log N) *
        (4 * N * ∑ m ∈ Finset.Icc 1 N, t ^ smallOmega m X / m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (log_weighted_sum_bound ht0 ht1 X N) (by positivity))
    _ ≤ Real.sqrt N + (2 / Real.log N) *
        (4 * N * (Real.exp 13 * Real.log N * (Real.log (min N X)) ^ (t - 1))) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (weighted_harmonic_sum_bound ht0 ht1 N X hN hX) (by positivity)
    _ = Real.sqrt N + 8 * Real.exp 13 * N * (Real.log (min N X)) ^ (t - 1) := by
      field_simp
      <;> ring

theorem log_power_double_bound {x e : ℝ} (hx : 2 ≤ x) (he0 : e ≤ 0) (he1 : -1 ≤ e) :
    (Real.log x) ^ e ≤ 2 * (Real.log (2 * x)) ^ e := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hM : 0 < Real.log (2 * x) := Real.log_pos (by nlinarith)
  have hLM : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have h := Real.log_le_log (by norm_num) hx
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hM hLM he0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL.le] at hpow
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ e := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he1
    simpa only [Real.rpow_neg_one, one_div] using h
  have hLpow : 0 ≤ (Real.log x) ^ e := Real.rpow_nonneg hL.le _
  nlinarith [mul_le_mul_of_nonneg_right htwo hLpow]

theorem sqrt_le_log_power {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : -1 ≤ e) :
    Real.sqrt N ≤ 2 * N * (Real.log (2 * (N : ℝ))) ^ e := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqrt0 := Real.sqrt_nonneg (N : ℝ)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
    simpa using h
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) hNR.ne'
  have hL1 : 1 ≤ Real.log (2 * (N : ℝ)) := by rw [hlogmul]; linarith [log_two_lower]
  have hL : Real.log (2 * (N : ℝ)) ≤ 2 * Real.sqrt N := by
    rw [hlogmul]
    linarith [log_le_sqrt_of_one_le (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))]
  have hLpos : 0 < Real.log (2 * (N : ℝ)) := by linarith
  have hsq := Real.mul_self_sqrt hNR.le
  have hbase : Real.sqrt N ≤ 2 * N / Real.log (2 * (N : ℝ)) := by
    apply (le_div_iff₀ hLpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL hsqrt0]
  have hp : (Real.log (2 * (N : ℝ)))⁻¹ ≤ (Real.log (2 * (N : ℝ))) ^ e := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hL1 he
  exact hbase.trans (by
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * (N : ℝ)))

theorem common_scale_numerical_coefficient : 2 + 16 * Real.exp 13 ≤ 2 * (10 : ℝ) ^ 9 := by
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_lower]
  have he1 : Real.exp 1 ≤ 4 := by
    calc
      Real.exp 1 ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hlog4
      _ = 4 := Real.exp_log (by norm_num)
  have he13 : Real.exp 13 ≤ (4 : ℝ) ^ 13 := by
    calc
      Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 4 ^ 13 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 13
  norm_num at he13 ⊢
  linarith

theorem common_scale_mean_nat_large {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X N : ℕ) (hX : 2 ≤ X) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤
      2 * (10 : ℝ) ^ 9 * N *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by
  have he0 : t - 1 ≤ 0 := by linarith
  have he1 : -1 ≤ t - 1 := by linarith
  have hXlog : 0 < Real.log (2 * (X : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hNlog : 0 < Real.log (2 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * N by omega))
  have hXp : 0 ≤ (Real.log (2 * (X : ℝ))) ^ (t - 1) := Real.rpow_nonneg hXlog.le _
  have hNp : 0 ≤ (Real.log (2 * (N : ℝ))) ^ (t - 1) := Real.rpow_nonneg hNlog.le _
  have hmin : (Real.log (min (N : ℝ) (X : ℝ))) ^ (t - 1) ≤
      2 * ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by
    rcases le_total (N : ℝ) (X : ℝ) with hNX | hXN
    · rw [min_eq_left hNX]
      have h := log_power_double_bound (x := (N : ℝ)) (by exact_mod_cast hN) he0 he1
      linarith
    · rw [min_eq_right hXN]
      have h := log_power_double_bound (x := (X : ℝ)) (by exact_mod_cast hX) he0 he1
      linarith
  have hbase := weight_sum_harmonic_bound ht0 ht1 X N hX hN
  have hsqrt := sqrt_le_log_power hN he1
  have hnonneg : 0 ≤ (N : ℝ) *
      ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by positivity
  calc
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤
        Real.sqrt N + 8 * Real.exp 13 * N * (Real.log (min (N : ℝ) (X : ℝ))) ^ (t - 1) := hbase
    _ ≤ (2 + 16 * Real.exp 13) * N *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by
      have hm := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 8 * Real.exp 13 * (N : ℝ))
      have hx := mul_nonneg (show (0 : ℝ) ≤ 2 * N by positivity) hXp
      nlinarith
    _ ≤ 2 * (10 : ℝ) ^ 9 * N *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right common_scale_numerical_coefficient hnonneg

theorem common_scale_mean_nat {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X N : ℕ) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 N, t ^ smallOmega n X) ≤
      2 * (10 : ℝ) ^ 9 * N *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (N : ℝ))) ^ (t - 1)) := by
  by_cases hN : 2 ≤ N
  · exact common_scale_mean_nat_large ht0 ht1 X N hX hN
  have h0 : 0 < Real.log 2 := by linarith [log_two_lower]
  have h1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith : t - 1 ≤ 0)
  have hXlog : 0 < Real.log (2 * (X : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hXp : 0 ≤ (Real.log (2 * (X : ℝ))) ^ (t - 1) := Real.rpow_nonneg hXlog.le _
  interval_cases N
  · simp
  · simp only [Finset.Icc_self, Finset.sum_singleton, smallOmega, Nat.factorization_one,
      Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero, pow_zero, Nat.cast_one, mul_one]
    norm_num
    nlinarith

theorem common_scale_mean {t Y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hY : 1 ≤ Y)
    (X : ℕ) (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, t ^ smallOmega n X) ≤
      (10 : ℝ) ^ 10 * Y *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
  let M := ⌈Y⌉₊
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hMY : (M : ℝ) ≤ 2 * Y := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ Y by linarith)
    dsimp [M]
    linarith
  have hYlog : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hXlog : 0 < Real.log (2 * (X : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hXp : 0 ≤ (Real.log (2 * (X : ℝ))) ^ (t - 1) := Real.rpow_nonneg hXlog.le _
  have hYp : 0 ≤ (Real.log (2 * Y)) ^ (t - 1) := Real.rpow_nonneg hYlog.le _
  have hp : (Real.log (2 * (M : ℝ))) ^ (t - 1) ≤ (Real.log (2 * Y)) ^ (t - 1) := by
    apply Real.rpow_le_rpow_of_nonpos hYlog
    · exact Real.log_le_log (by linarith) (by linarith)
    · linarith
  calc
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, t ^ smallOmega n X) ≤
        ∑ n ∈ Finset.Icc 1 M, t ^ smallOmega n X := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_le_ceil Y))
      intro n hn hnot
      exact pow_nonneg ht0 _
    _ ≤ 2 * (10 : ℝ) ^ 9 * M *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * (M : ℝ))) ^ (t - 1)) :=
      common_scale_mean_nat ht0 ht1 X M hX
    _ ≤ 4 * (10 : ℝ) ^ 9 * Y *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
      calc
        _ ≤ 2 * (10 : ℝ) ^ 9 * M *
            ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) (by positivity)
        _ ≤ 4 * (10 : ℝ) ^ 9 * Y *
            ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
          have h := mul_le_mul_of_nonneg_right hMY (add_nonneg hXp hYp)
          nlinarith
    _ ≤ (10 : ℝ) ^ 10 * Y *
        ((Real.log (2 * (X : ℝ))) ^ (t - 1) + (Real.log (2 * Y)) ^ (t - 1)) := by
      have hnonneg := mul_nonneg (show 0 ≤ Y by linarith) (add_nonneg hXp hYp)
      nlinarith

end Erdos302
