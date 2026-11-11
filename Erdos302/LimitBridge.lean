import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
A conditional analytic bridge. The assumptions in this module are explicit
arguments, not established facts about Erdős 302. The finite-prime limits and
uniform approximation must still be proved before this bridge can be applied.
-/

namespace Erdos302

open Filter
open scoped Topology

theorem tendsto_of_uniform_approximations
    (f : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (U : ℕ → ℝ) (C : ℝ)
    (hF : ∀ V, Tendsto (F V) atTop (𝓝 (U V)))
    (hU : Tendsto U atTop (𝓝 C))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ V₀ : ℕ, ∀ V ≥ V₀,
      ∀ᶠ N : ℕ in atTop, |f N - F V N| < ε) :
    Tendsto f atTop (𝓝 C) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨V₀, hV₀⟩ := happrox (ε / 3) he
  obtain ⟨V₁, hV₁⟩ := Metric.tendsto_atTop.mp hU (ε / 3) he
  let V := max V₀ V₁
  have hVC : dist (U V) C < ε / 3 := hV₁ V (le_max_right _ _)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hV₀ V (le_max_left _ _))
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hF V) (ε / 3) he
  refine ⟨max N₀ N₁, ?_⟩
  intro N hN
  have hNF := hN₀ N (le_trans (le_max_left _ _) hN)
  have hFU := hN₁ N (le_trans (le_max_right _ _) hN)
  have htriangle := dist_triangle (f N) (F V N) C
  have htriangle' := dist_triangle (F V N) (U V) C
  simp only [Real.dist_eq] at htriangle htriangle' hVC hFU ⊢
  linarith

end Erdos302
