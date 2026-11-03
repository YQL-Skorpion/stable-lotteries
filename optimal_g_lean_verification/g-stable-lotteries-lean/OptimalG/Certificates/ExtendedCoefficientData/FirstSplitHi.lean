import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.ExtendedScalarExpressions

/-! An exact endpoint polynomial sign for C.4. -/
namespace OptimalG.Certificates.ExtendedCoefficientData.FirstSplitHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numeratorPolynomial : RationalPolynomial3 := [[[0, (-43/50), (59/50), (-1/2)], [(-9/25), -1]], [[(1/2), (50229/26350)], [2, (387040000/127049687)]], [[0, (-1967/527)]], [[(-4527/1054)], [(-9676000000/1143447183)]], [[(4000/527)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-74681772139651579536691/18295154928000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(9/25), (56233/100000)⟩]
def numeratorScale : ℚ := 457378873200000000000000000
def numeratorCertificate : DenseBernstein3 := [[[19353887282371700645486475, 30584361938702853147581925, 15090367695562358265904425, 1965688167938679226274775], [19213269374175745756828975, 30204482257863553632409425, 14752462058471623901531925, 1867044303491289488417275]], [[77417577863699901628085775, 122342505698452948957520325, 60365500466893208659583325, 7863753146970055180011975], [76855099058223653407619275, 120822966353650049578680825, 59013858193716154563303825, 7469171413119652242105475]], [[116129409959607821092941600, 183521345642721533279106900, 90554295398250126722589000, 11797130487381255311218500], [115285680992250974078481000, 181242005693037137178605100, 88526802400951875564967200, 11205248472410553239637900]], [[77421635457603459407860120, 122352621944897790848845560, 60373560178072219102910760, 7865754205607781511788520], [76859142306534690177963240, 120833041356580497800434920, 59021878454643940695780120, 7471159919428026923171640]], [[19355916079323839299687549, 30589420061926353386186247, 15094397551152942780509847, 1966688697257902156476949], [19215290998331623752442269, 30209519759329856574610407, 14756472188936595799094007, 1868038556645836439391669]]]
noncomputable def numerator (lam S p : ℝ) : ℝ := numeratorPolynomial.eval lam S p

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {lam S p : ℝ}
    (hlam : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (9/25) (56233/100000))
    : 0<numerator lam S p := by
  have hx : ∀ i,(numeratorBox i).Contains (![lam, S, p] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hlam
    · simpa [numeratorBox,RatInterval.Contains] using hS
    · simpa [numeratorBox,RatInterval.Contains] using hp
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![lam, S, p] hx
  have he : numeratorReduced.eval lam S p=numerator lam S p-(74681772139651579536691/18295154928000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval lam S p at hh
  rw [he] at hh
  have hm : (0:ℝ)<(74681772139651579536691/18295154928000000000000000) := by norm_num
  linarith only [hh,hm]

 theorem expression_identity (lam S p : ℝ) :
    numerator lam S p=ExtendedScalarExpressions.firstSplit lam S p (9/25) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,ExtendedScalarExpressions.firstSplit,
    ExtendedScalarExpressions.denominator,ExtendedScalarExpressions.etaNumerator,
    ExtendedScalarExpressions.betaNumerator,ExtendedScalarExpressions.denominatorDerivative,
    ExtendedScalarExpressions.etaNumeratorDerivative,SmallMassExpressions.initial,
    headInitial,Variational.cap,Variational.capScore,Variational.quadratic]
  <;> ring

end OptimalG.Certificates.ExtendedCoefficientData.FirstSplitHi
