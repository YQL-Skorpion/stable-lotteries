import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.LocalSplitLo
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (-1847839/2500000), (11529/10000), (-1/2)], [(-1529/5000), -1]], [[(1/2), (8533349/5270000)], [2, (2958920800/1143447183)]], [[(-109/500), (-8751/2635)]], [[(-4527/1054)], [(-9676000000/1143447183)]], [[(4000/527)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-211098272184417123797/731806197120000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (19/50)⟩]
def numeratorScale : ℚ := 457378873200000000000000000
def numeratorCertificate : DenseBernstein3 := [[[2299716388861776274030625, 4770281236755918163091875, 2753544311480219504091875, 281149948093277615030625], [2147854507101978993373125, 4317343945258306689119375, 2303255373764388398119375, 131936420115260702373125]], [[9200469652510555176062375, 19085843154729991010187125, 11018801370143164492187125, 1126109805952528658062375], [8593014712589979301195875, 17274071825382165692787625, 9217623531209241481987625, 529248356445855090395875]], [[13803110686300043196586500, 28635842228712078050599500, 16535138425846298511439500, 1691429790477463657426500], [12891917156993267570925900, 25918151989342775887217700, 13833338535028021061657700, 796126609721712745365900]], [[9203677970516245485396720, 19095279940260014295870160, 11028049987186140135550160, 1129129955471171325076720], [8596208204625232428299840, 17283464283574439102179520, 9226827971488028919459520, 532253830567622245579840]], [[2301320547864981193011699, 4774999629522009098875097, 2758168620002786618715097, 282660022852958712851699], [2149451253119965167366419, 4322040174355522225139257, 2307857593904860948179257, 133439157176503890406419]]]
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
  have he : numeratorReduced.eval lam S p=numerator lam S p-(211098272184417123797/731806197120000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(211098272184417123797/731806197120000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.localSplit lam S p (1529/5000) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.localSplit,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.LocalSplitLo
