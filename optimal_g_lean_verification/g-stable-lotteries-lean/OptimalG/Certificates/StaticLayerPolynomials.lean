import OptimalG.Certificates.AutomaticBernstein
import OptimalG.Certificates.StaticLowRational

/-! Polynomial acceptance conditions for supports on complete layer intervals.
All low-profile pieces are read from the already checked exact trial data. -/
namespace OptimalG.Certificates.StaticSupport
open RationalPolynomial
open StaticLow (lam slack leftContact rightContact)

inductive PrimitiveBranch where
  | cap
  | piece (index : ℕ)
  | tail
  deriving DecidableEq, Repr

abbrev profilePiece := StaticLow.profilePiece
abbrev piece0 := StaticLow.profilePiece 0
theorem piece0_lo : piece0.lo=leftContact := UpperProfileData.endpoint_data.1

structure ContinuousLayerCell where
  lo : ℚ
  hi : ℚ
  a0 : ℚ
  a1 : ℚ
  left : LayerNode
  right : LayerNode
  pinned : Bool
  bIsA : Bool
  rBranch : PrimitiveBranch
  aPiece : ℕ
  bPiece : ℕ
  deriving Repr

namespace ContinuousLayerCell

def pPoly (c : ContinuousLayerCell) : RationalPolynomial := [c.lo,c.hi-c.lo]
def aPoly (c : ContinuousLayerCell) : RationalPolynomial := [c.a0,c.a1-c.a0]
def bPoly (c : ContinuousLayerCell) : RationalPolynomial := if c.bIsA then c.aPoly else c.pPoly

def scorePoly (i : ℕ) (r : RationalPolynomial) : RationalPolynomial :=
  if i<242 then
    let p:=profilePiece i
    compose [p.a0,p.a1,p.a2,p.a3] (add r [-p.lo])
  else add [lam] (scale (-1) r)

def slopePoly (i : ℕ) (r : RationalPolynomial) : RationalPolynomial :=
  if i<242 then
    let p:=profilePiece i
    compose [p.a1,2*p.a2,3*p.a3] (add r [-p.lo])
  else [-1]

def A (c : ContinuousLayerCell) : RationalPolynomial := scorePoly c.aPiece c.aPoly
def B (c : ContinuousLayerCell) : RationalPolynomial := scorePoly c.bPiece c.bPoly

def Rden (c : ContinuousLayerCell) : RationalPolynomial :=
  match c.rBranch with
  | .cap => add [1] (scale (-1) c.pPoly)
  | _ => [1]

def Rnum (c : ContinuousLayerCell) : RationalPolynomial :=
  match c.rBranch with
  | .cap => add (mul c.Rden (add [lam^2-lam/2] (scale (lam/2) c.pPoly))) [-lam*slack]
  | .piece i =>
    let p:=profilePiece i
    compose [p.f0,p.a0,p.a1/2,p.a2/3,p.a3/4] (add c.pPoly [-p.lo])
  | .tail => add (add (scale lam c.pPoly) (scale (-1/2) (pow c.pPoly 2))) [-slack]

def P (c : ContinuousLayerCell) : RationalPolynomial :=
  let r:=add [1] (scale (-1) c.pPoly)
  add (add (scale lam r) (scale (-1/2) (pow r 2))) [-slack]

def k (c : ContinuousLayerCell) : RationalPolynomial := add (add c.pPoly c.bPoly) [-lam]
def h (c : ContinuousLayerCell) : RationalPolynomial := add [2*lam] (scale (-1) c.aPoly)
def D (c : ContinuousLayerCell) : RationalPolynomial :=
  add (mul c.h c.Rnum) (scale (-1) (mul (mul c.k c.P) c.Rden))
def N (c : ContinuousLayerCell) : RationalPolynomial :=
  add (mul c.Rnum c.A) (mul (mul c.P c.B) c.Rden)

def Cnum (c : ContinuousLayerCell) : RationalPolynomial :=
  if c.pinned then c.N else scale (-1) (slopePoly c.aPiece c.aPoly)
def Cden (c : ContinuousLayerCell) : RationalPolynomial := if c.pinned then c.D else [1]

def nodeWeight (c : ContinuousLayerCell) : RationalPolynomial :=
  scale (1/(c.right.p-c.left.p)) (add c.pPoly [-c.left.p])
def Cu (c : ContinuousLayerCell) : RationalPolynomial :=
  add [c.left.Cu+1/200000000] (scale (c.right.Cu-c.left.Cu) c.nodeWeight)
def alphau (c : ContinuousLayerCell) : RationalPolynomial :=
  add [c.left.alphau+1/200000000] (scale (c.right.alphau-c.left.alphau) c.nodeWeight)

def balancePolynomial (c : ContinuousLayerCell) : RationalPolynomial :=
  add (mul c.Cnum c.D) (scale (-1) (mul c.N c.Cden))
def coefficientPolynomial (c : ContinuousLayerCell) : RationalPolynomial :=
  add (mul c.Cu c.Cden) (scale (-1) c.Cnum)
def alphaPolynomial (c : ContinuousLayerCell) : RationalPolynomial :=
  add (mul (mul c.alphau c.Cden) c.Rnum)
    (scale (-1) (mul c.Rden (add (mul c.B c.Cden) (mul c.Cnum c.k))))

def pinLowerPolynomial (c : ContinuousLayerCell) : RationalPolynomial :=
  add c.Cnum (scale (-1/10) c.Cden)
def pinUpperPolynomial (c : ContinuousLayerCell) : RationalPolynomial :=
  add (scale (-StaticLow.slopeQ leftContact) c.Cden) (scale (-1) c.Cnum)

def numericPolynomials (c : ContinuousLayerCell) : List RationalPolynomial :=
  [add c.Rnum [-1/100],add c.Rden [-1/2],add c.Cden [-1/100],
    c.balancePolynomial,c.coefficientPolynomial,c.alphaPolynomial] ++
      (if c.pinned then [c.pinLowerPolynomial,c.pinUpperPolynomial] else [])

def numericCheck (c : ContinuousLayerCell) : Bool := c.numericPolynomials.all automaticCheck

theorem numericCheck_nonnegative {c : ContinuousLayerCell} (hc : c.numericCheck=true)
    {p : RationalPolynomial} (hp : p∈c.numericPolynomials) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0≤p.eval t := automaticCheck_sound (List.all_eq_true.mp hc p hp) ht

end ContinuousLayerCell
end OptimalG.Certificates.StaticSupport
