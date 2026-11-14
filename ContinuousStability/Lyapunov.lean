/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# The Lyapunov function `V = M - f` along solutions (Section 2)

The paper uses `V(x) = M - f(x)` with `M = f(x̄)` and the trajectory derivative
`V_x'(t) = -∇f(x(t)) · P(t) ∇f(x(t))` (TD). We work with `f` directly, so (TD) reads
`(f ∘ x)'(t) = ⟪∇f(x(t)), P(t) ∇f(x(t))⟫ ≥ 0`, and `V` is nonincreasing exactly when `f ∘ x`
is nondecreasing.
-/
module

public import ContinuousStability.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

open scoped RealInnerProductSpace
open Set

namespace ContinuousStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {g : E → E} {P : ℝ → E →L[ℝ] E} {lo : ℝ → ℝ} {I : Set ℝ} {x : ℝ → E}

/-- **(TD), the trajectory derivative.** Along a solution of (E),
`(f ∘ x)'(t) = ⟪∇f(x(t)), P(t) ∇f(x(t))⟫`, i.e. `V_x'(t) = -∇f · P(t) ∇f`. -/
theorem trajectory_deriv (hx : IsSolutionOn P g I x) {t : ℝ} (ht : t ∈ I)
    (hf : HasFDerivAt f (innerSL ℝ (g (x t))) (x t)) :
    HasDerivWithinAt (fun s => f (x s)) ⟪g (x t), P t (g (x t))⟫ I t := by
  have := hf.comp_hasDerivWithinAt t (hx t ht)
  simpa [Function.comp_def, innerSL_apply_apply] using this

/-- The lower bound `λ₁(P(t)) ‖∇f‖² ≤ (f ∘ x)'(t)` that follows from (TD). -/
theorem trajectory_deriv_ge {t : ℝ} (hP : EigBound (P t) (lo t)) :
    lo t * ‖g (x t)‖ ^ 2 ≤ ⟪g (x t), P t (g (x t))⟫ := by
  rw [real_inner_comm]; exact hP.lower _

/-- **`V` is a Lyapunov function along solutions.** If a solution stays, on a time interval `I`,
in a set `S` where `f` has gradient `g`, and `P(t)` is positive semi-definite on `I`, then
`f ∘ x` is nondecreasing on `I` (equivalently, `V_x(t) = M - f(x(t))` is nonincreasing). -/
theorem ascent {S : Set E} (hI : Convex ℝ I) (hx : IsSolutionOn P g I x)
    (hxS : ∀ t ∈ I, x t ∈ S) (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hP : ∀ t ∈ I, EigBound (P t) (lo t)) :
    MonotoneOn (fun t => f (x t)) I :=
  monotoneOn_of_deriv_nonneg' hI
    (fun t ht => trajectory_deriv hx ht (hgrad _ (hxS t ht)))
    (fun t ht => by rw [real_inner_comm]; exact (hP t ht).psd _)

/-- **Weighted ascent.** If in addition `m ≤ ‖∇f(x(t))‖²` on `I` and `W' = λ₁(P(t))` on `I`,
then `f(x(t)) - m W(t)` is nondecreasing on `I`. Integrating `V_x' ≤ -m λ₁(P(t))` in the proof
of Theorem 2.1(ii) is the special case `W(t) = ∫_{t₀}^t λ₁(P(s)) ds`. -/
theorem ascent_weighted {S : Set E} (hI : Convex ℝ I) (hx : IsSolutionOn P g I x)
    (hxS : ∀ t ∈ I, x t ∈ S) (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hP : ∀ t ∈ I, EigBound (P t) (lo t)) {W : ℝ → ℝ}
    (hW : ∀ t ∈ I, HasDerivWithinAt W (lo t) I t) {m : ℝ}
    (hm : ∀ t ∈ I, m ≤ ‖g (x t)‖ ^ 2) :
    MonotoneOn (fun t => f (x t) - m * W t) I := by
  refine monotoneOn_of_deriv_nonneg' hI
    (fun t ht => (trajectory_deriv hx ht (hgrad _ (hxS t ht))).sub ((hW t ht).const_mul m))
    (fun t ht => ?_)
  have h1 := trajectory_deriv_ge (g := g) (x := x) (hP t ht)
  have h2 := mul_le_mul_of_nonneg_left (hm t ht) (hP t ht).lo_nonneg
  linarith

end ContinuousStability
