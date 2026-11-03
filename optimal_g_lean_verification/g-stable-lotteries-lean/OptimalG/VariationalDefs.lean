import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# The variational problem in Section 4 and Appendix B

These definitions retain measurable low-rank functions and the essential
infimum over the full three-dimensional control domain. In particular,
`Feasible` asks for an actual solution of (4.3) satisfying all terminal tests;
it does not encode existence or the shape of a minimizing solution as an axiom.
-/

namespace OptimalG.Variational

open MeasureTheory Set

noncomputable section

def lambdaLo : ℝ := 562325 / 1000000
def lambdaHi : ℝ := 562330 / 1000000
def pLo : ℝ := 1 / 4
def ell : ℝ := 28 / 100
def xLo : ℝ := 285 / 1000
def pHi : ℝ := 36 / 100
def xHi : ℝ := 38 / 100
def tEnd : ℝ := 385 / 1000
def zStart : ℝ := 775 / 1000
def zTest : ℝ := 84 / 100
def zEnd : ℝ := 875 / 1000
def qLo : ℝ := 26 / 100
def qHi : ℝ := 28 / 100

def quadratic (lam r : ℝ) : ℝ := lam * r - r ^ 2 / 2
def cap (lam S r : ℝ) : ℝ :=
  lam ^ 2 - lam / 2 + lam * r / 2 - lam * S / (1 - r)
def slackUpper (lam : ℝ) : ℝ :=
  266503148804352 / 10000000000000000 - (lambdaHi - lam) / 2

structure LowRankData where
  S : ℝ
  phi : ℝ → ℝ

def lowPrimitive (lam : ℝ) (d : LowRankData) (r : ℝ) : ℝ :=
  cap lam d.S ell + ∫ u in ell..r, d.phi u

/-- The piecewise primitive on [pLo,zStart], as in Appendix B, page 24. -/
def primitive (lam : ℝ) (d : LowRankData) (r : ℝ) : ℝ :=
  if r ≤ ell then cap lam d.S r
  else if r ≤ tEnd then lowPrimitive lam d r
  else quadratic lam r - d.S

/-- Membership in K_lambda. `MemLp ... infinity` expresses exactly the
essential boundedness used before the regularity proof. -/
def Admissible (lam : ℝ) (d : LowRankData) : Prop :=
  lam ∈ Icc lambdaLo lambdaHi ∧
  d.S ≤ slackUpper lam ∧
  MemLp d.phi ⊤ (volume.restrict (Icc ell tEnd)) ∧
  (∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ d.phi r ∧ d.phi r ≤ lam - r) ∧
  lowPrimitive lam d tEnd = quadratic lam tEnd - d.S ∧
  (∀ r ∈ Icc ell tEnd, lowPrimitive lam d r ≤ cap lam d.S r)

abbrev Control := ℝ × ℝ × ℝ

/-- U from page 24, including its boundary faces. -/
def controlDomain : Set Control :=
  {c | c.1 ∈ Icc pLo pHi ∧ c.2.1 ∈ Icc xLo xHi ∧
    c.2.2 ∈ Icc (max xLo c.1) xHi}

def controlMeasure : Measure Control := volume.restrict controlDomain

def controlDeterminant (lam : ℝ) (d : LowRankData) (c : Control) : ℝ :=
  (2 * lam - c.2.1) * primitive lam d c.1 -
    (c.1 + c.2.2 - lam) * (quadratic lam (1 - c.1) - d.S)

/-- The full rational control in (4.2). -/
def controlH (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) : ℝ :=
  -((z - lam) *
      (primitive lam d c.1 * d.phi c.2.1 +
        (quadratic lam (1 - c.1) - d.S) * d.phi c.2.2) +
      (quadratic lam (z - c.1) - d.S - u) *
      ((c.1 + c.2.2 - lam) * d.phi c.2.1 +
        (2 * lam - c.2.1) * d.phi c.2.2)) /
    controlDeterminant lam d c

/-- The right side of ODE (4.3), with the correct essential infimum. -/
def vectorField (lam : ℝ) (d : LowRankData) (z u : ℝ) : ℝ :=
  min (lam - z) (essInf (controlH lam d z u) controlMeasure)

def terminalBound (lam S z q : ℝ) : ℝ :=
  z * (quadratic lam (1 - z + q) - S - cap lam S q) / (lam - q)

/-- A differentiable solution on the closed continuation interval, using
one-sided derivatives at its endpoints. -/
def IsContinuation (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ) : Prop :=
  Y zStart = quadratic lam zStart - d.S ∧
  ∀ z ∈ Icc zStart zEnd,
    HasDerivWithinAt Y (vectorField lam d z (Y z)) (Icc zStart zEnd) z

def PassesTerminalTests (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ) : Prop :=
  ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
    terminalBound lam d.S z q ≤ Y z

def Feasible (lam : ℝ) : Prop :=
  ∃ d : LowRankData, Admissible lam d ∧
    ∃ Y : ℝ → ℝ, IsContinuation lam d Y ∧ PassesTerminalTests lam d Y

/-- The exact parameter (4.5); nonemptiness and attainment are separate
mathematical obligations. -/
def lambdaStar : ℝ := sInf {lam | Feasible lam}

theorem feasible_parameter_bounds {lam : ℝ} (h : Feasible lam) :
    lam ∈ Icc lambdaLo lambdaHi := by
  obtain ⟨d, hd, _⟩ := h
  exact hd.1

theorem feasible_parameters_bddBelow : BddBelow {lam | Feasible lam} := by
  refine ⟨lambdaLo, ?_⟩
  intro lam hlam
  exact (feasible_parameter_bounds hlam).1

theorem lambdaStar_le_feasible {lam : ℝ} (h : Feasible lam) :
    lambdaStar ≤ lam :=
  csInf_le feasible_parameters_bddBelow h

theorem lambdaLo_le_lambdaStar (hne : ∃ lam, Feasible lam) :
    lambdaLo ≤ lambdaStar := by
  apply le_csInf hne
  intro lam hlam
  exact (feasible_parameter_bounds hlam).1

theorem primitive_at_ell (lam : ℝ) (d : LowRankData) :
    primitive lam d ell = cap lam d.S ell := by
  simp [primitive]

theorem lowPrimitive_at_ell (lam : ℝ) (d : LowRankData) :
    lowPrimitive lam d ell = cap lam d.S ell := by
  simp [lowPrimitive]

theorem vectorField_le_line (lam : ℝ) (d : LowRankData) (z u : ℝ) :
    vectorField lam d z u ≤ lam - z := min_le_left _ _

theorem continuation_continuous {lam : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (h : IsContinuation lam d Y) : ContinuousOn Y (Icc zStart zEnd) :=
  fun z hz => (h.2 z hz).continuousWithinAt

end
end OptimalG.Variational
