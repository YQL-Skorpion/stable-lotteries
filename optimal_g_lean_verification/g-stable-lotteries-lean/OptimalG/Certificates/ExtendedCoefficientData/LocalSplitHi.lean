import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.LocalSplitHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (-9769/12500), (59/50), (-1/2)], [(-9/25), -1]], [[(1/2), (50229/26350)], [2, (387040000/127049687)]], [[(-109/500), (-1967/527)]], [[(-4527/1054)], [(-9676000000/1143447183)]], [[(4000/527)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-475980001123755606997/731806197120000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 457378873200000000000000000
def numeratorCertificate : DenseBernstein3 := [[[2316882556384678178030625, 4952461977885523299091875, 3071365278156212064091875, 433956341162566943030625], [2176264648188723289373125, 4534757321033393833119375, 2657809689039817798119375, 297487500702347254373125]], [[9268998273398590384062375, 19814150413348606974187125, 12289661972658242796187125, 1737191770737026206062375], [8706519467922342163595875, 18143310356493414952787625, 10635418275376603414787625, 1191309324834330625595875]], [[13905699542133307306666500, 29727679552615925407399500, 18440794428067128894799500, 2607837324627710794066500], [13061970574776460292205900, 27221387322851631084017700, 15959396870609081291417700, 1789003029577110499605900]], [[9271934489610275697556720, 19822755776730281661470160, 12298064050786536230270160, 1739924701695330266356720], [8709441338541506467659840, 18151872860358750291779520, 10643777671249781180579520, 1194028087461337356459840]], [[2318350664490880599091699, 4956764659577439935675097, 3075566317221438074075097, 435322806642078737491699], [2177725583498665051846419, 4539038572967140333939257, 2661989386977485512339257, 298846882016210230246419]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (9/25) (19/50))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(475980001123755606997/731806197120000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(475980001123755606997/731806197120000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.localSplit lam S p (9/25) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.localSplit,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.LocalSplitHi
