import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf009
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-16726296926514261942011847001916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(3203/4000), (807/1000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[2774158254176080880158926487547921215325], [20129097851063445984942740320926351272606], [16038109595994717830552360393054627573131]], [[3154775829808452656057714850095842430650], [35471114345039473761365204391852702545212], [29682678513445726556844582661109255146262]], [[418157423162856548550296175047921215325], [15417096189036997321725479695926351272606], [13682108764981493498943730080554627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (3203/4000) (807/1000))
    (hr : r∈Icc (1581/8000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<exclusion p r u := by
  have hx : ∀ i,(exclusionBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [exclusionBox,RatInterval.Contains] using hp
    · simpa [exclusionBox,RatInterval.Contains] using hr
    · simpa [exclusionBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound exclusionChecked ![p, r, u] hx
  have he : exclusionReduced.eval p r u=exclusion p r u-(16726296926514261942011847001916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(16726296926514261942011847001916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf009


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf000
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-470665515539944325054867138626827152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(807/1000), (1657/2000)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5903356367650356980497409554035084000605], [6186272398283921993491417111126837064496], [941331031079888650109734277253654305966]], [[12803650958198291971346381783070168001210], [14366421242363000007685959572253674128992], [2879600285057355310571031229507308611932]], [[6844765648080841915142861872785084000605], [8069090959144891862782321748626837064496], [1882740311510373584755186596003654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (807/1000) (1657/2000))
    (hr : r∈Icc 0 (527/4000))
    (hu : u∈Icc 0 1)
    : 0<exclusion p r u := by
  have hx : ∀ i,(exclusionBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [exclusionBox,RatInterval.Contains] using hp
    · simpa [exclusionBox,RatInterval.Contains] using hr
    · simpa [exclusionBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound exclusionChecked ![p, r, u] hx
  have he : exclusionReduced.eval p r u=exclusion p r u-(470665515539944325054867138626827152983/60063756048775636242412500000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(470665515539944325054867138626827152983/60063756048775636242412500000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf000


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf001
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-4000020758903206697798069946612400321673310099503133217029849322365903983074188766864231/4018259015661622321352678581599737436600772376399072982986427525000000000000000000000000)], [(-1246677700573519569456060733600653498001182672329613864848492941062506010500952571048896581/9923355509416492017851788921323722049044969984429988370379111295001856250000000000000000000)], [(1761871278962121759986821794711257009833575947535666195880736379948577535396498319731/18606291580155922533472104227481978841959318720806228194460833678128480468750000000000)]], [[(337056797889800445736958559535773461189291407385507664055338968815633124489266269013019/150639172818466671997750116452732023514914155361366047368183852675550000000000000000000)], [(1602465100356422722335868957527755979818101636184481378046532194133120654163957/2545341979290049197456439268098353448469821537323266824229338637500000000000000)], [(49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(-1127210515087107726208678383444201018123688142271223/940495458876260379210500804301011162778996490500000)], [-1]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-156200033816767964904055707560111313123500683960364060409802785490606590045849204980297/2126670675084235369380001644038569743739964546278108904021419096596000000000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(807/1000), (3271/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 903835036910800031986500698716392141089484932168196284209103116053300000000000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[4220389227825138457645651089965304683098900814539036020964486909668986258672940335661782711], [1916476942166237121725422501534104660550525831294024304525393009080395473657040954801064136], [66385014372126385084223675713047308077487790683154725674166183833507800769485912116626225]], [[10231956008385883446249865727300814887756788754860090000227489608888921096714657489568716422], [6891725413821297655819295225108007799633016184063585583805738026887747558250062150194868022], [1426991167170428119831731454807652231485132851118090197775316553629809368229137931905703700]], [[5872619951626912955625059387211064307674275773540646497181381115064073100580642153906933711], [4690474207161054807982684239181688509339509463145792171930790233201456697593527445393803886], [1214778717238128041615474544826836190648276337591573846833217169346267917921233269789077475]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (807/1000) (3271/4000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(156200033816767964904055707560111313123500683960364060409802785490606590045849204980297/2126670675084235369380001644038569743739964546278108904021419096596000000000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(156200033816767964904055707560111313123500683960364060409802785490606590045849204980297/2126670675084235369380001644038569743739964546278108904021419096596000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[(56233/100000)], [-1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-72941/400000)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(807/1000), (3271/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 400000
def denominatorCertificate : DenseBernstein3 := [[[99291], [72941]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (807/1000) (3271/4000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<denominator p r u := by
  have hx : ∀ i,(denominatorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [denominatorBox,RatInterval.Contains] using hp
    · simpa [denominatorBox,RatInterval.Contains] using hr
    · simpa [denominatorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound denominatorChecked ![p, r, u] hx
  have he : denominatorReduced.eval p r u=denominator p r u-(72941/400000) := by
    norm_num [denominatorReduced,RationalPolynomial3.eval_add,denominator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤denominatorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(72941/400000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf001


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf002
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-428788929552032165393052462837010303783326615875983576051318244343564528287076993494879/573577169950500942000895354661608043709285504427294515794167725000000000000000000000000)], [(-40286437357596574860424871435933929794600037826624004905187346263177685979165881156866029/1416486629487881313458304637355635841603628390252703972583863295776706250000000000000000000)], [(21978723696983185604607004362985241325239807479763353349238091294990573902380431879/2655912430289777462734321195041817203006803231723819948594743679581324218750000000000)]], [[(36342731360293381593673596066614637488418301713819852875367790520150243150058453200371/21502643331884346314357565652457470081269501180306701671102289119950000000000000000000)], [(1602465100356422722335868957527755979818101636184481378046532194133120654163957/2545341979290049197456439268098353448469821537323266824229338637500000000000000)], [(49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(-124159907796232250492622065452478878288014186075407/134248867868145906872552270775059816113326814500000)], [-1]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-993582830020934358494815176519767886211038393553477935125825746982713487411486585352641/5160634399652243115445815756589792819504680283273608401064549388788000000000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(807/1000), (3271/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 129015859991306077886145393914744820487617007081840210026613734719700000000000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[24839570750523358962370379412994197155275959838836948378145643674567837185287164633816025], [330782992769389237413102767817229147762933294258345816430291815254599979652653140602386076], [595904196960750935252464739793816735869828487034809710981730802354539496381820442651113251]], [[87905052934404712649602334225819261470230681710126788266967164337971739951656129895693300], [670881737629394064092921767644626956832476178608738127200113857699238142902679691353559402], [1166699067719844385447924189289484330739377410509491330029575343190507103239734478986715002]], [[46330076180244751233947550632716241196310115767778548156794262942707529410600215261877275], [305645776436010462067531039489253698830581756308278258688777190790536242842395300751173326], [553077308338735688036455893337632307749232401536078858698826946902562059806051536335601751]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (807/1000) (3271/4000))
    (hr : r∈Icc (1581/8000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(993582830020934358494815176519767886211038393553477935125825746982713487411486585352641/5160634399652243115445815756589792819504680283273608401064549388788000000000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(993582830020934358494815176519767886211038393553477935125825746982713487411486585352641/5160634399652243115445815756589792819504680283273608401064549388788000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[(56233/100000)], [-1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-29883/200000)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(807/1000), (3271/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 200000
def denominatorCertificate : DenseBernstein3 := [[[43058], [29883]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (807/1000) (3271/4000))
    (hr : r∈Icc (1581/8000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<denominator p r u := by
  have hx : ∀ i,(denominatorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [denominatorBox,RatInterval.Contains] using hp
    · simpa [denominatorBox,RatInterval.Contains] using hr
    · simpa [denominatorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound denominatorChecked ![p, r, u] hx
  have he : denominatorReduced.eval p r u=denominator p r u-(29883/200000) := by
    norm_num [denominatorReduced,RationalPolynomial3.eval_add,denominator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤denominatorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(29883/200000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf002


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf003
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-60807603206608255857868752748083151387/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(3271/4000), (1657/2000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[17417801423769137895303059604856390110781], [17621161503041697017518324983234666411306], [1520190080165206396446718818702078784675]], [[38601239969260215529187928484712780221562], [42773597249527273512200268516469332822612], [6806017282052352531475246912404157569350]], [[21072380660556891482472648167356390110781], [24930319976617204191857502108234666411306], [5174769316952959983616307381202078784675]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (3271/4000) (1657/2000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<exclusion p r u := by
  have hx : ∀ i,(exclusionBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [exclusionBox,RatInterval.Contains] using hp
    · simpa [exclusionBox,RatInterval.Contains] using hr
    · simpa [exclusionBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound exclusionChecked ![p, r, u] hx
  have he : exclusionReduced.eval p r u=exclusion p r u-(60807603206608255857868752748083151387/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(60807603206608255857868752748083151387/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadLateLeaf003

