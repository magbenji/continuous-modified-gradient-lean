/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Stability and asymptotic stability (Section 2): Theorem 2.1
-/
module

public import ContinuousStability.Lyapunov
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open scoped RealInnerProductSpace Topology
open Set Metric Filter

namespace ContinuousStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **H0** (on the ball `B̄_{r₀}(x̄)`): `f` has gradient `g` there and `g` is continuous there.
(The rest of H0, the smoothness of `f`, `∇f` and `P` that gives existence and uniqueness of
solutions, is not used by the proofs below.) -/
structure LocalHyp (f : E → ℝ) (g : E → E) (xbar : E) (r₀ : ℝ) : Prop where
  r₀_pos : 0 < r₀
  grad : ∀ z ∈ closedBall xbar r₀, HasFDerivAt f (innerSL ℝ (g z)) z
  cont : ContinuousOn g (closedBall xbar r₀)

/-- **H1**: `x̄` is an isolated (strict) local maximum of `f`. -/
def IsolatedMax (f : E → ℝ) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → f x < f xbar

/-- **H2**: `x̄` is an isolated critical point of `f` (gradient `g`). -/
def IsolatedCrit (g : E → E) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → g x ≠ 0

/-- **H3**, the eigenvalue condition (EC): `∫₀^∞ λ₁(P(t)) dt = ∞`, stated for the lower bounds
`lo t ≤ λ₁(P(t))`. -/
def EigenvalueCondition (lo : ℝ → ℝ) : Prop :=
  Tendsto (fun T => ∫ t in (0 : ℝ)..T, lo t) atTop atTop

/-- Uniform stability of `x̄` for (E) (Hartman's definition with `t_ε = 0`): `δ` does not depend
on the starting time `t₀ ≥ 0`. -/
def UniformlyStable (P : ℝ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ ≥ (0 : ℝ), ∀ x : ℝ → E, IsSolution P g t₀ x →
    dist (x t₀) xbar < δ → ∀ t ≥ t₀, dist (x t) xbar < ε

/-- Uniform asymptotic stability: uniform stability plus a uniform `δ` of attraction. -/
def UniformlyAsympStable (P : ℝ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  UniformlyStable P g xbar ∧
    ∃ δ > 0, ∀ t₀ ≥ (0 : ℝ), ∀ x : ℝ → E, IsSolution P g t₀ x →
      dist (x t₀) xbar < δ → Tendsto x atTop (𝓝 xbar)

variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ : ℝ} {P : ℝ → E →L[ℝ] E} {lo : ℝ → ℝ}

theorem LocalHyp.continuousOn_f (hH : LocalHyp f g xbar r₀) : ContinuousOn f (closedBall xbar r₀) :=
  fun z hz => (hH.grad z hz).continuousAt.continuousWithinAt

variable [FiniteDimensional ℝ E]

/-- The barrier construction in the proof of Theorem 2.1(i): for every `R > 0` there are
`0 < ρ ≤ R` and `δ > 0` such that every solution started in `B_δ(x̄)` at a time `t₀ ≥ 0` stays in
`B_ρ(x̄)` for as long as it exists. The time set `I` is any interval starting at `t₀`, for
example `[t₀, ∞)` or `[t₀, ω)`. -/
theorem trap (hH : LocalHyp f g xbar r₀) (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t))
    (hH1 : IsolatedMax f xbar) {R : ℝ} (hR : 0 < R) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ r₀ ∧ (∀ y, y ≠ xbar → dist y xbar ≤ ρ → f y < f xbar) ∧
      ∃ δ > 0, ∀ t₀ ≥ (0 : ℝ), ∀ (I : Set ℝ) (x : ℝ → E), Convex ℝ I → t₀ ∈ I → I ⊆ Ici t₀ →
        IsSolutionOn P g I x → dist (x t₀) xbar < δ → ∀ t ∈ I, dist (x t) xbar < ρ := by
  obtain ⟨r₁, hr₁, hmax⟩ := hH1
  set ρ := min R (min r₀ r₁) with hρdef
  have hρ : 0 < ρ := lt_min hR (lt_min hH.r₀_pos hr₁)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρr₀ : ρ ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρr₁ : ρ ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  -- the sphere `A = B̄_ρ \ B_ρ` and `m = min_A V > 0`
  have hA : IsCompact (closedBall xbar ρ \ ball xbar ρ) :=
    (isCompact_closedBall xbar ρ).diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (closedBall xbar ρ \ ball xbar ρ) :=
    continuousOn_const.sub (hH.continuousOn_f.mono
      (sdiff_subset.trans (closedBall_subset_closedBall hρr₀)))
  have hVpos : ∀ y ∈ closedBall xbar ρ \ ball xbar ρ, 0 < f xbar - f y := by
    intro y hy
    have hy1 : dist y xbar ≤ ρ := mem_closedBall.mp hy.1
    have hy2 : ρ ≤ dist y xbar := not_lt.mp (fun h => hy.2 (mem_ball.mpr h))
    have hne : y ≠ xbar := by
      intro h; rw [h, dist_self] at hy2; linarith
    linarith [hmax y hne (hy1.trans hρr₁)]
  obtain ⟨m, hm, hmA⟩ := exists_pos_lower_bound hA hVc hVpos
  -- `δ` with `V < m` on `B_δ`
  have hfc : ContinuousAt f xbar :=
    (hH.grad xbar (mem_closedBall_self hH.r₀_pos.le)).continuousAt
  obtain ⟨δ', hδ', hδ'f⟩ := Metric.continuousAt_iff.mp hfc m hm
  refine ⟨ρ, hρ, hρR, hρr₀, fun y hy hyd => hmax y hy (hyd.trans hρr₁), min δ' ρ,
    lt_min hδ' hρ, ?_⟩
  intro t₀ ht₀ I x hI ht₀I hIt₀ hx hx0 t ht
  by_contra hout
  have htt₀ : t₀ ≤ t := hIt₀ ht
  have hIcc : Icc t₀ t ⊆ I := hI.ordConnected.out ht₀I ht
  have hxc : ContinuousOn x (Icc t₀ t) := (hx.continuousOn).mono hIcc
  obtain ⟨s, hs, hsU, hscl, hbefore⟩ :=
    first_exit isOpen_ball htt₀ hxc (mem_ball.mpr (hx0.trans_le (min_le_right _ _)))
      (fun h => hout (mem_ball.mp h))
  have hsA : x s ∈ closedBall xbar ρ \ ball xbar ρ := ⟨closure_ball_subset_closedBall hscl, hsU⟩
  -- on `[t₀, s]` the solution stays in `B̄_ρ ⊆ B̄_{r₀}`, so `f ∘ x` is nondecreasing there
  have hsub : Icc t₀ s ⊆ I := (Icc_subset_Icc_right hs.2).trans hIcc
  have hmono := ascent (S := closedBall xbar r₀) (lo := lo) (convex_Icc t₀ s) (hx.mono hsub)
    (fun τ hτ => by
      rcases hτ.2.lt_or_eq with h | h
      · exact closedBall_subset_closedBall hρr₀ (ball_subset_closedBall (hbefore τ ⟨hτ.1, h⟩))
      · rw [h]; exact closedBall_subset_closedBall hρr₀ hsA.1)
    hH.grad (fun τ hτ => hP τ (ht₀.trans hτ.1))
  have hle : f (x t₀) ≤ f (x s) :=
    hmono ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1.le
  have h0 := hδ'f (hx0.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at h0
  have := hmA _ hsA
  linarith [neg_abs_le (f (x t₀) - f xbar)]

/-- **Theorem 2.1(i), on any interval.** Under H0 and H1 (and `P(t)` positive semi-definite),
for every `ε > 0` there is `δ > 0` such that every solution started in `B_δ(x̄)` at any time
`t₀ ≥ 0` stays in `B_ε(x̄)` on its whole interval of existence `I`. This is the a priori bound
that, together with the continuation theorem (Hartman, Thm. II.3.1), gives existence for all
`t ≥ t₀`. -/
theorem stable_on (hH : LocalHyp f g xbar r₀) (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t))
    (hH1 : IsolatedMax f xbar) :
    ∀ ε > 0, ∃ δ > 0, ∀ t₀ ≥ (0 : ℝ), ∀ (I : Set ℝ) (x : ℝ → E), Convex ℝ I → t₀ ∈ I →
      I ⊆ Ici t₀ → IsSolutionOn P g I x → dist (x t₀) xbar < δ →
        ∀ t ∈ I, dist (x t) xbar < ε := by
  intro ε hε
  obtain ⟨ρ, -, hρε, -, -, δ, hδ, htrap⟩ := trap hH hP hH1 hε
  exact ⟨δ, hδ, fun t₀ ht₀ I x hI ht₀I hIt₀ hx hx0 t ht =>
    (htrap t₀ ht₀ I x hI ht₀I hIt₀ hx hx0 t ht).trans_le hρε⟩

/-- **Theorem 2.1(i).** Under H0 and H1 (and `P(t)` positive semi-definite), `x̄` is a uniformly
stable equilibrium of (E). -/
theorem stable (hH : LocalHyp f g xbar r₀) (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t))
    (hH1 : IsolatedMax f xbar) :
    UniformlyStable P g xbar := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := stable_on hH hP hH1 ε hε
  exact ⟨δ, hδ, fun t₀ ht₀ x hx hx0 t ht =>
    h t₀ ht₀ (Ici t₀) x (convex_Ici t₀) self_mem_Ici subset_rfl hx hx0 t ht⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The convergence half of the proofs of Theorem 2.1(ii) and Theorem 3.1: if a path stays in a
compact set `T` on which `x̄` is the unique maximizer of `f` and the unique zero of `g`, and
`(f ∘ x)' ≥ w(t) ‖g(x(t))‖²` with `w ≥ 0` and `∫^∞ w = ∞` (expressed by an antiderivative `W`
of `w` with `W → ∞`), then `x(t) → x̄`. -/
theorem tendsto_of_weighted_ascent {T : Set E} (hT : IsCompact T) (hxbarT : xbar ∈ T)
    (hf : ContinuousOn f T) (hg : ContinuousOn g T)
    (hflt : ∀ y ∈ T, y ≠ xbar → f y < f xbar) (hgne : ∀ y ∈ T, y ≠ xbar → g y ≠ 0)
    {t₀ : ℝ} {w W : ℝ → ℝ} (hw0 : ∀ t ≥ t₀, 0 ≤ w t)
    (hW' : ∀ t ≥ t₀, HasDerivWithinAt W (w t) (Ici t₀) t) (hW : Tendsto W atTop atTop)
    {x : ℝ → E} (hxT : ∀ t ≥ t₀, x t ∈ T) {D : ℝ → ℝ}
    (hD : ∀ t ≥ t₀, HasDerivWithinAt (fun s => f (x s)) (D t) (Ici t₀) t)
    (hDge : ∀ t ≥ t₀, w t * ‖g (x t)‖ ^ 2 ≤ D t) :
    Tendsto x atTop (𝓝 xbar) := by
  have hfle : ∀ y ∈ T, f y ≤ f xbar := by
    intro y hy
    by_cases h : y = xbar
    · rw [h]
    · exact (hflt y hy h).le
  -- `V_x(t) = f x̄ - f (x t)` is nonincreasing
  have hmono : MonotoneOn (fun s => f (x s)) (Ici t₀) :=
    monotoneOn_of_deriv_nonneg' (convex_Ici t₀) hD
      (fun t ht => (mul_nonneg (hw0 t ht) (sq_nonneg _)).trans (hDge t ht))
  -- `V_x(t)` gets arbitrarily small
  have hsmall : ∀ c > 0, ∃ t ≥ t₀, f xbar - f (x t) < c := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨δ₁, hδ₁, hδ₁f⟩ := Metric.continuousWithinAt_iff.mp (hf xbar hxbarT) c hc
    have hfar : ∀ t ≥ t₀, δ₁ ≤ dist (x t) xbar := by
      intro t ht
      by_contra h
      push Not at h
      have := hδ₁f (hxT t ht) h
      rw [Real.dist_eq] at this
      have := hcon t ht
      linarith [neg_abs_le (f (x t) - f xbar)]
    have hK : IsCompact (T \ ball xbar δ₁) := hT.diff isOpen_ball
    have hgc : ContinuousOn (fun y => ‖g y‖ ^ 2) (T \ ball xbar δ₁) :=
      ((hg.mono sdiff_subset).norm).pow 2
    have hgpos : ∀ y ∈ T \ ball xbar δ₁, 0 < ‖g y‖ ^ 2 := by
      intro y hy
      have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hδ₁)
      have := norm_pos_iff.mpr (hgne y hy.1 hne)
      positivity
    obtain ⟨m₁, hm₁, hm₁K⟩ := exists_pos_lower_bound hK hgc hgpos
    have hm₁x : ∀ t ≥ t₀, m₁ ≤ ‖g (x t)‖ ^ 2 := fun t ht =>
      hm₁K _ ⟨hxT t ht, fun h => by have := hfar t ht; rw [mem_ball] at h; linarith⟩
    -- `f (x t) - m₁ W t` is nondecreasing, so `f (x t) → ∞`
    have hmono' : MonotoneOn (fun s => f (x s) - m₁ * W s) (Ici t₀) := by
      refine monotoneOn_of_deriv_nonneg' (convex_Ici t₀)
        (fun t ht => (hD t ht).sub ((hW' t ht).const_mul m₁)) (fun t ht => ?_)
      have h1 := hDge t ht
      have h2 := mul_le_mul_of_nonneg_left (hm₁x t ht) (hw0 t ht)
      linarith
    obtain ⟨t, htW, htt₀⟩ :=
      ((hW.eventually_gt_atTop (W t₀ + (f xbar - f (x t₀) + 1) / m₁)).and
        (eventually_ge_atTop t₀)).exists
    have h1 := hmono' (self_mem_Ici) (show t ∈ Ici t₀ from htt₀) htt₀
    have h2 := hfle _ (hxT t htt₀)
    have h3 : f xbar - f (x t₀) + 1 < m₁ * (W t - W t₀) :=
      (div_lt_iff₀' hm₁).mp (by linarith)
    simp only at h1
    linarith
  -- conclude `x t → x̄`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (T \ ball xbar ε) := hT.diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (T \ ball xbar ε) :=
    continuousOn_const.sub (hf.mono sdiff_subset)
  have hVpos : ∀ y ∈ T \ ball xbar ε, 0 < f xbar - f y := by
    intro y hy
    have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hε)
    linarith [hflt y hy.1 hne]
  obtain ⟨m', hm', hm'K⟩ := exists_pos_lower_bound hK hVc hVpos
  obtain ⟨t₁, ht₁, hvt₁⟩ := hsmall m' hm'
  refine ⟨t₁, fun t ht => ?_⟩
  by_contra hcon
  have hmem : x t ∈ T \ ball xbar ε :=
    ⟨hxT t (ht₁.trans ht), fun h => hcon (mem_ball.mp h)⟩
  have := hm'K _ hmem
  have := hmono (show t₁ ∈ Ici t₀ from ht₁) (show t ∈ Ici t₀ from ht₁.trans ht) ht
  simp only at this
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `W(t) = ∫₀ᵗ lo` is an antiderivative of a continuous `lo`. -/
theorem hasDerivWithinAt_integral {lo : ℝ → ℝ} (hlo : Continuous lo) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun T => ∫ τ in (0 : ℝ)..T, lo τ) (lo t) s t :=
  (hlo.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt

/-- **Theorem 2.1(ii).** Under H0, H1, H2 and H3 (the eigenvalue condition (EC)), `x̄` is a
uniformly asymptotically stable equilibrium of (E). (H3 is stated for continuous lower bounds
`lo t ≤ λ₁(P(t))`; taking `lo t = λ₁(P(t))` gives the paper's `∫₀^∞ λ₁(P(t)) dt = ∞`.) -/
theorem asympStable (hH : LocalHyp f g xbar r₀) (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t))
    (hlo : Continuous lo) (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hH3 : EigenvalueCondition lo) :
    UniformlyAsympStable P g xbar := by
  refine ⟨stable hH hP hH1, ?_⟩
  obtain ⟨r₂, hr₂, hcrit⟩ := hH2
  obtain ⟨ρ, hρ, hρR, hρr₀, hρmax, δ, hδ, htrap⟩ := trap hH hP hH1 hr₂
  refine ⟨δ, hδ, fun t₀ ht₀ x hx hx0 => ?_⟩
  have hin : ∀ t ≥ t₀, x t ∈ closedBall xbar ρ := fun t ht =>
    mem_closedBall.mpr (htrap t₀ ht₀ (Ici t₀) x (convex_Ici t₀) self_mem_Ici subset_rfl hx hx0
      t ht).le
  refine tendsto_of_weighted_ascent (T := closedBall xbar ρ) (isCompact_closedBall xbar ρ)
    (mem_closedBall_self hρ.le)
    (hH.continuousOn_f.mono (closedBall_subset_closedBall hρr₀))
    (hH.cont.mono (closedBall_subset_closedBall hρr₀))
    (fun y hy hne => hρmax y hne (mem_closedBall.mp hy))
    (fun y hy hne => hcrit y hne ((mem_closedBall.mp hy).trans hρR))
    (w := lo) (fun t ht => (hP t (ht₀.trans ht)).lo_nonneg)
    (fun t _ => hasDerivWithinAt_integral hlo _ t) hH3 hin
    (fun t ht => trajectory_deriv hx ht
      (hH.grad _ (closedBall_subset_closedBall hρr₀ (hin t ht))))
    (fun t ht => trajectory_deriv_ge (hP t (ht₀.trans ht)))

end ContinuousStability
