/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Setting and hypotheses (Section 2)

We work in a real inner product space `E` (finite-dimensional where compactness is needed,
e.g. `EuclideanSpace ℝ (Fin n)`). The objective is `f : E → ℝ` with gradient `g : E → E`,
expressed as `HasFDerivAt f (innerSL ℝ (g z)) z`, i.e. `Df(z) h = ⟪g z, h⟫`.

The matrices `P(t)` are continuous linear maps `P t : E →L[ℝ] E`. Instead of eigenvalues we use
a lower Loewner bound: `EigBound P lo` says that `lo ‖u‖² ≤ ⟪P u, u⟫` for all `u`, with
`0 ≤ lo`. For a symmetric matrix this is exactly `lo ≤ λ₁(P)`, so taking `lo t = λ₁(P(t))`
recovers the paper's hypotheses; any weaker lower bound also works. `EigBound P 0` says that
`P` is positive semi-definite.

A solution of the modified-gradient system (E), `x' = P(t) ∇f(x)`, on a time interval `I` is
Mathlib's `IsIntegralCurveOn x (fun t z => P t (g z)) I`: for every `t ∈ I`,
`HasDerivWithinAt x (P t (g (x t))) I t`.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.ODE.Basic

@[expose] public section

open scoped RealInnerProductSpace
open Set

namespace ContinuousStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `EigBound P lo`: `lo • I ⪯ P` with `0 ≤ lo`, i.e. `lo ‖u‖² ≤ ⟪P u, u⟫` for all `u`.
For a symmetric matrix this means `lo ≤ λ₁(P)`. -/
structure EigBound (P : E →L[ℝ] E) (lo : ℝ) : Prop where
  lo_nonneg : 0 ≤ lo
  lower : ∀ u, lo * ‖u‖ ^ 2 ≤ ⟪P u, u⟫

/-- The modified-gradient system (E) on the time set `I`: `x' = P(t) ∇f(x)` for `t ∈ I`. -/
def IsSolutionOn (P : ℝ → E →L[ℝ] E) (g : E → E) (I : Set ℝ) (x : ℝ → E) : Prop :=
  IsIntegralCurveOn x (fun t z => P t (g z)) I

/-- A solution of (E) that starts at time `t₀` and exists for all `t ≥ t₀`. -/
def IsSolution (P : ℝ → E →L[ℝ] E) (g : E → E) (t₀ : ℝ) (x : ℝ → E) : Prop :=
  IsSolutionOn P g (Ici t₀) x

namespace EigBound

variable {P : E →L[ℝ] E} {lo : ℝ}

/-- `P` is positive semi-definite. -/
theorem psd (h : EigBound P lo) (u : E) : 0 ≤ ⟪P u, u⟫ :=
  le_trans (mul_nonneg h.lo_nonneg (sq_nonneg _)) (h.lower u)

end EigBound

omit [InnerProductSpace ℝ E] in
/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_lower_bound {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {φ : X → ℝ} (hc : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn h hc
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

/-- A real function with a nonnegative derivative (within `I`) on a convex set `I` is
monotone on `I`. -/
theorem monotoneOn_of_deriv_nonneg' {I : Set ℝ} (hI : Convex ℝ I) {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ I, HasDerivWithinAt φ (φ' t) I t) (hφ' : ∀ t ∈ I, 0 ≤ φ' t) :
    MonotoneOn φ I :=
  monotoneOn_of_hasDerivWithinAt_nonneg hI (fun t ht => (hφ t ht).continuousWithinAt)
    (fun t ht => ((hφ t (interior_subset ht)).mono interior_subset))
    (fun t ht => hφ' t (interior_subset ht))

omit [InnerProductSpace ℝ E] in
/-- **First exit.** If a path `x`, continuous on `[a, b]`, starts in an open set `U` and is
outside `U` at time `b`, then there is a first time `s ∈ (a, b]` at which `x s ∉ U`; at that
time `x s ∈ closure U`, and `x τ ∈ U` for all `τ ∈ [a, s)`. -/
theorem first_exit {x : ℝ → E} {U : Set E} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (ha : x a ∈ U) (hb : x b ∉ U) :
    ∃ s ∈ Ioc a b, x s ∉ U ∧ x s ∈ closure U ∧ ∀ τ ∈ Ico a s, x τ ∈ U := by
  set S := Icc a b ∩ x ⁻¹' Uᶜ with hS
  have hSc : IsClosed S := hx.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have hSne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hSbdd : BddBelow S := ⟨a, fun s hs => hs.1.1⟩
  set s := sInf S with hs
  have hsS : s ∈ S := hSc.csInf_mem hSne hSbdd
  have hbefore : ∀ τ ∈ Ico a s, x τ ∈ U := by
    intro τ hτ
    by_contra hτU
    have : s ≤ τ := csInf_le hSbdd ⟨⟨hτ.1, hτ.2.le.trans hsS.1.2⟩, hτU⟩
    linarith [hτ.2]
  have has : a < s := by
    rcases hsS.1.1.eq_or_lt with h | h
    · exact absurd (h ▸ ha) hsS.2
    · exact h
  refine ⟨s, ⟨has, hsS.1.2⟩, hsS.2, ?_, hbefore⟩
  have h1 : s ∈ closure (Ico a s) := by
    rw [closure_Ico has.ne]; exact ⟨has.le, le_rfl⟩
  have h2 := ((hx s hsS.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hsS.1.2)))
    |>.mem_closure_image h1
  refine closure_mono ?_ h2
  rintro _ ⟨τ, hτ, rfl⟩
  exact hbefore τ hτ

end ContinuousStability
