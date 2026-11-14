/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Examples 2.1 and 2.2: the hypotheses H3 and H2 cannot be dropped

* **Example 2.1** (asymptotic stability requires the eigenvalue condition). In `ℝ²` take
  `P(t) = diag((t+1)⁻², (t+1)⁻¹)` and `f(x₁, x₂) = 4 - (x₁ - 1)² - (x₂ - 1)²`.
  Theorem 2.1(i) applies, so `x̄ = (1, 1)` is uniformly stable, but (EC) fails for every lower
  bound on `λ₁(P(t))`, and `x̄` is not asymptotically stable: the solutions
  `x(t) = (1 + c₁ e^{2/(t+1)}, 1)` stay at distance at least `|c₁|` from `x̄`.
* **Example 2.2** (asymptotic stability requires an isolated critical point). The paper builds
  a `C¹` function with an isolated maximum at `x̄` and circles of critical points accumulating at
  `x̄`. What makes the example work is that each critical point `y` is an equilibrium of (E),
  so the constant solution `x(t) ≡ y` never approaches `x̄`. We prove this mechanism in general
  (`not_asympStable_of_crit_accum`); the spline itself is not formalized.
-/
import ContinuousStability.Stability
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped RealInnerProductSpace Topology
open Set Metric Filter

namespace ContinuousStability

/-! ### Example 2.2: critical points accumulating at `x̄` -/

section Example22

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {g : E → E} {xbar : E} {P : ℝ → E →L[ℝ] E}

/-- Every critical point `y` of `f` gives the constant (equilibrium) solution `x(t) ≡ y`. -/
theorem isSolution_const {y : E} (hy : g y = 0) (t₀ : ℝ) :
    IsSolution P g t₀ (fun _ => y) := by
  intro t _
  simp only [hy, map_zero]
  exact hasDerivWithinAt_const _ _ _

/-- **The mechanism of Example 2.2.** If there are critical points `y ≠ x̄` arbitrarily close to
`x̄` (so H2 fails), then `x̄` is not uniformly asymptotically stable, whatever `P(t)` is. -/
theorem not_asympStable_of_crit_accum
    (hcrit : ∀ δ > 0, ∃ y, y ≠ xbar ∧ dist y xbar < δ ∧ g y = 0) :
    ¬ UniformlyAsympStable P g xbar := by
  rintro ⟨-, δ, hδ, h⟩
  obtain ⟨y, hne, hyd, hy⟩ := hcrit δ hδ
  have := h 0 le_rfl (fun _ => y) (isSolution_const hy 0) hyd
  exact hne (tendsto_nhds_unique tendsto_const_nhds this)

end Example22

/-! ### Example 2.1: a too-small eigenvalue destroys asymptotic stability -/

namespace Example21

/-- The plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The standard basis vectors `e₀ = (1, 0)` and `e₁ = (0, 1)`. -/
noncomputable abbrev e (i : Fin 2) : E2 := EuclideanSpace.single i 1

/-- The coordinate projection `u ↦ uᵢ eᵢ`. -/
noncomputable def proj (i : Fin 2) : E2 →L[ℝ] E2 := (EuclideanSpace.proj i).smulRight (e i)

/-- `P(t) = diag((t+1)⁻², (t+1)⁻¹)`. -/
noncomputable def P (t : ℝ) : E2 →L[ℝ] E2 := ((t + 1) ^ 2)⁻¹ • proj 0 + (t + 1)⁻¹ • proj 1

/-- The smallest eigenvalue `λ₁(P(t)) = (t+1)⁻²`. -/
noncomputable def lam (t : ℝ) : ℝ := ((t + 1) ^ 2)⁻¹

/-- The maximizer `x̄ = (1, 1)`. -/
noncomputable def xbar : E2 := e 0 + e 1

/-- `f(x) = 4 - |x - x̄|²`. -/
noncomputable def f (x : E2) : ℝ := 4 - ‖x - xbar‖ ^ 2

/-- `∇f(x) = -2 (x - x̄)`. -/
noncomputable def g (x : E2) : E2 := (-2 : ℝ) • (x - xbar)

@[simp] theorem xbar_apply (i : Fin 2) : xbar i = 1 := by
  fin_cases i <;> simp [xbar]

/-- `f` is the paper's `f(x₁, x₂) = 4 - (x₁ - 1)² - (x₂ - 1)²`. -/
theorem f_eq (x : E2) : f x = 4 - (x 0 - 1) ^ 2 - (x 1 - 1) ^ 2 := by
  simp [f, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

theorem P_apply (t : ℝ) (u : E2) :
    P t u = ((t + 1) ^ 2)⁻¹ • (u 0 • e 0) + (t + 1)⁻¹ • (u 1 • e 1) := by
  simp [P, proj]

theorem inner_P (t : ℝ) (u : E2) :
    ⟪P t u, u⟫ = ((t + 1) ^ 2)⁻¹ * u 0 ^ 2 + (t + 1)⁻¹ * u 1 ^ 2 := by
  rw [P_apply]
  simp only [inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp
  ring

theorem norm_sq_coord (u : E2) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- `λ₁(P(t)) = (t+1)⁻²` is a lower bound for `P(t)` when `t ≥ 0`. -/
theorem eigBound {t : ℝ} (ht : 0 ≤ t) : EigBound (P t) (lam t) where
  lo_nonneg := by unfold lam; positivity
  lower u := by
    rw [inner_P, norm_sq_coord, lam]
    have h1 : 1 ≤ t + 1 := by linarith
    have h2 : ((t + 1) ^ 2)⁻¹ ≤ (t + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith)
    nlinarith [sq_nonneg (u 1)]

/-- ... and it is the best one: no lower bound for `P(t)` exceeds `(t+1)⁻²`. -/
theorem eigBound_le {t l : ℝ} (h : EigBound (P t) l) : l ≤ lam t := by
  have := h.lower (e 0)
  rw [inner_P, norm_sq_coord] at this
  simpa [lam] using this

theorem hasFDerivAt_f (z : E2) : HasFDerivAt f (innerSL ℝ (g z)) z := by
  have h : HasFDerivAt f _ z :=
    HasFDerivAt.const_sub (HasFDerivAt.norm_sq ((hasFDerivAt_id z).sub_const xbar)) 4
  convert h using 1
  ext v
  simp [g]

theorem continuous_g : Continuous g := by
  unfold g; fun_prop

/-- H1: `f` has an isolated (indeed global, strict) maximum at `x̄`. -/
theorem isolatedMax : IsolatedMax f xbar := by
  refine ⟨1, one_pos, fun x hx _ => ?_⟩
  have : 0 < ‖x - xbar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  simp only [f, sub_self, norm_zero]
  nlinarith

/-- **Example 2.1, stability.** Theorem 2.1(i) applies: `x̄ = (1, 1)` is uniformly stable. -/
theorem stable : UniformlyStable P g xbar :=
  ContinuousStability.stable (r₀ := 1) (lo := lam)
    ⟨one_pos, fun z _ => hasFDerivAt_f z, continuous_g.continuousOn⟩
    (fun _ ht => eigBound ht) isolatedMax

/-- `∫₀ᵀ (t+1)⁻² dt = 1 - (T+1)⁻¹` for `T ≥ 0`. -/
theorem integral_lam {T : ℝ} (hT : 0 ≤ T) : ∫ t in (0 : ℝ)..T, lam t = 1 - (T + 1)⁻¹ := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) T, 0 < t + 1 := fun t ht => by
    rw [uIcc_of_le hT] at ht; linarith [ht.1]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t : ℝ => -(t + 1)⁻¹) (lam t) t := by
    intro t ht
    have := HasDerivAt.inv ((hasDerivAt_id t).add_const 1) (hpos t ht).ne'
    exact this.neg.congr_deriv (by simp only [lam, id]; ring)
  have hint : IntervalIntegrable lam MeasureTheory.volume 0 T := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    exact ((continuousAt_id.add continuousAt_const).pow 2).inv₀
      (pow_ne_zero _ (hpos t ht).ne') |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  ring

/-- **Example 2.1, (EC) fails**: `∫₀^∞ λ₁(P(t)) dt = 1 < ∞`. By `eigBound_le`, (EC) then fails
for every lower bound on `λ₁(P(t))`, so Theorem 2.1(ii) cannot be applied. -/
theorem not_eigenvalueCondition : ¬ EigenvalueCondition lam := by
  intro h
  obtain ⟨T, hT1, hT0⟩ := ((h.eventually_gt_atTop 1).and (eventually_ge_atTop 0)).exists
  rw [integral_lam hT0] at hT1
  have : 0 < (T + 1)⁻¹ := by positivity
  linarith

/-- The solutions `x(t) = (1 + c₁ e^{2/(t+1)}, 1)` of (E). -/
noncomputable def sol (c : ℝ) (t : ℝ) : E2 := xbar + (c * Real.exp (2 / (t + 1))) • e 0

theorem isSolution_sol (c : ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : IsSolution P g t₀ (sol c) := by
  intro t ht
  have ht1 : t + 1 ≠ 0 := by linarith [show t₀ ≤ t from ht]
  have hd : HasDerivAt (fun t : ℝ => 2 / (t + 1)) (-(2 * ((t + 1) ^ 2)⁻¹)) t := by
    have := (HasDerivAt.inv ((hasDerivAt_id t).add_const 1) ht1).const_mul 2
    simpa [div_eq_mul_inv] using this
  have hx := ((hd.exp.const_mul c).smul_const (e 0)).const_add xbar
  refine (hx.congr_deriv ?_).hasDerivWithinAt
  show _ = P t (g (sol c t))
  rw [g, P_apply]
  ext i
  fin_cases i <;> simp [sol]
  ring

theorem dist_sol (c : ℝ) {t : ℝ} (ht : 0 ≤ t) : |c| ≤ dist (sol c t) xbar := by
  rw [dist_eq_norm, sol, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have : 1 ≤ Real.exp (2 / (t + 1)) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg c]

/-- **Example 2.1, no asymptotic stability.** `x̄ = (1, 1)` is not (uniformly) asymptotically
stable: arbitrarily close to `x̄` there are solutions that stay a fixed distance away. -/
theorem not_asympStable : ¬ UniformlyAsympStable P g xbar := by
  rintro ⟨-, δ, hδ, h⟩
  set c := δ / (2 * Real.exp 2) with hc
  have hcpos : 0 < c := by positivity
  have h0 : dist (sol c 0) xbar < δ := by
    rw [dist_eq_norm, sol, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one,
      mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc]; norm_num
    field_simp
    linarith
  have hlim := h 0 le_rfl (sol c) (isSolution_sol c le_rfl) h0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim c hcpos
  have := hN (max N 0) (le_max_left _ _)
  have := dist_sol c (le_max_right N 0)
  rw [abs_of_pos hcpos] at this
  linarith

end Example21

end ContinuousStability
