import OptimalG.Certificates.IntegerLogCurvature
import OptimalG.Certificates.IntegerSlabCover
import OptimalG.Certificates.CapCubic

/-! The fixed-low-rank terminal logarithmic barrier under the actual affine
high-rank warp. Its numerical curvature is checked on a finite scalar cover. -/
namespace OptimalG.Certificates.Transport
open RatExpr Set

structure TerminalParameters where
  lam : ℚ
  slack : ℚ
  level : ℚ
  highRank : ℚ
  lowRank : ℚ

namespace TerminalParameters
abbrev E := RatExpr 1
def zExpr (d : TerminalParameters) : E := .const d.highRank-(.var 0-.const d.slack)
def Qexpr (d : TerminalParameters) (x : E) : E := .const d.lam*x-.const (1/2)*x*x
def lowPrimitiveExpr (d : TerminalParameters) : E :=
  .const (d.lam*d.lam-d.lam/2)+.const (d.lam/2*d.lowRank)-
    .const d.lam*.var 0/.const (1-d.lowRank)
def deficitExpr (d : TerminalParameters) : E :=
  .const d.level-.var 0-d.zExpr*(d.Qexpr (1-d.zExpr+.const d.lowRank)-
    .var 0-d.lowPrimitiveExpr)/.const (d.lam-d.lowRank)

noncomputable def terminalDeficit (d : TerminalParameters) (S : ℝ) : ℝ :=
  let z := (d.highRank:ℝ)-(S-d.slack)
  (d.level:ℝ)-S-z*(quadratic d.lam (1-z+d.lowRank)-S-cap d.lam S d.lowRank)/
    ((d.lam:ℝ)-d.lowRank)

theorem deficitExpr_eval (d : TerminalParameters) (S : ℝ) :
    d.deficitExpr.evalOne S=d.terminalDeficit S := by
  simp only [deficitExpr,zExpr,Qexpr,lowPrimitiveExpr,evalOne,eval_subNotation,
    eval_addNotation,eval_mulNotation,eval_divNotation,eval_natNotation,eval,
    terminalDeficit,quadratic,cap,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,
    Rat.cast_one,Rat.cast_ofNat]
  ring

def curvatureCheck (scale : ℕ) (curvature : ℚ) (d : TerminalParameters)
    (slabs : List IntegerInterval) : Bool :=
  slabs.all (fun box => d.deficitExpr.negativeLogCurvatureCheck scale box curvature)

theorem checked_terminal_taylor {scale : ℕ} (hs : 0<scale)
    (d : TerminalParameters) (curvature : ℚ) {start finish : ℤ}
    {slabs : List IntegerInterval} (horder : start<finish)
    (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : d.curvatureCheck scale curvature slabs=true) (ds : ℝ)
    (hpath : ∀ t∈Icc (0:ℝ) 1,
      (⟨start,finish⟩:IntegerInterval).Contains scale ((d.slack:ℝ)+t*ds)) :
    -Real.log (d.terminalDeficit d.slack)-
      (logPartial 0 d.deficitExpr).evalOne d.slack*ds+(curvature:ℝ)*ds^2/2≤
        -Real.log (d.terminalDeficit ((d.slack:ℝ)+ds)) := by
  have h := negativeLogCurvature_taylor hs d.deficitExpr curvature d.slack ds (by
    intro t ht
    obtain ⟨box,hmem,hbox⟩ := integerSlabCoverCheck_sound horder hslabs (hpath t ht)
    exact ⟨box,hbox,List.all_eq_true.mp hc box hmem⟩)
  simpa only [d.deficitExpr_eval] using h

end TerminalParameters
end OptimalG.Certificates.Transport
