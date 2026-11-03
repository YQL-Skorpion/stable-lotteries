import OptimalG.Certificates.ScaledTensorReconstruction
import OptimalG.Certificates.StaticHighMassTailModelBatch04
import OptimalG.Certificates.StaticHighMassTailModelBatch05
import OptimalG.Certificates.StaticHighMassTailModelBatch06
import OptimalG.Certificates.StaticHighMassTailModelBatch07
import OptimalG.Certificates.StaticHighMassTailModelBatch08
import OptimalG.Certificates.StaticHighMassTailModelBatch09
import OptimalG.Certificates.StaticHighMassTailModelBatch10


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-37576735389196839995752664856952036019104416905668973234066042002727498030929/59013182077308629637480262128239117422495373250000000000000000000000000000000)], [(207335923288189010766721494947054875985595437157033017999644407551100716551/73176345775862700750475525039016505603894262830000000000000000000000000000)], [(-665373669476905753265835399413092350924223702678054151905731859326807529/312219075310347523202028906833137090576615521408000000000000000000000000)]], [[(564227632913903249902971199142281933232570839337400966273038644233626863828121495621/100997167376547076723855358047305766123394177650152591750000000000000000000000000000)], [(-1517794107871986596714203503173888119055463611125559/87067155744156321879962132048038650000000000000000)], [(5535425099112912635161595125938314708099604351077/371486531175066973354505096738298240000000000000)], [(-3474682092298477128274714468776989105141/1288541558012719297101994785772800000000)]], [[(-6189421775127653782134559034229230334573105836641/1404308963615424546451002129807075000000000000000)], [(19110240137150600688205361176842380249897551267/1741343114883126437599242640960773000000000000)], [(-53680363643919173154716063828135704685323309/7429730623501339467090101934765964800000000)]], [[(416589928088877360721174205096908403621/1368859907683542359162748752437500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 3231909356049506455163371457513784515948613684804882936000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨21264848015264743123667207986327503579726698937814845604224330419923436011720351368235277, 0, 4, 0, 3, 0, 0⟩,
  ⟨63551347838262323294088421072077715566988845518649342713166680915857635829973904545242581, 0, 4, 1, 2, 0, 0⟩,
  ⟨53443442660053781367879970923161958175574934535985042392970945805828908240995833167926206, 0, 4, 2, 1, 0, 0⟩,
  ⟨6587532710395521297007810056549535936387245866901748353837298533788437504617279990918902, 0, 4, 3, 0, 0, 0⟩,
  ⟨94145652883481871916225507225497656998860309097302241034423413883627660871325462979103571, 1, 3, 0, 3, 0, 0⟩,
  ⟨279983993382125613934293419951582773866522606590409410421780156449470697306900229211913463, 1, 3, 1, 2, 0, 0⟩,
  ⟨234578384430428874850787385668184418385058960629000794063498262183414762770722878980988088, 1, 3, 2, 1, 0, 0⟩,
  ⟨30018317530479738457981830116162573068330887111917735463439582442834524261398112748178196, 1, 3, 3, 0, 0, 0⟩,
  ⟨156071499471055877392562699427419713821377677039363142045020770072974760126435248797554219, 2, 2, 0, 3, 0, 0⟩,
  ⟨461664622793695239045262922911072185122124540646325790288827251947867518297780864573250407, 2, 2, 1, 2, 0, 0⟩,
  ⟨385060617520418409803800935196879042636062254917279015460474443481132394816234192144372532, 2, 2, 2, 1, 0, 0⟩,
  ⟨50707985943087058469637276592779839492783964686361489691235764176855003439263576368676344, 2, 2, 3, 0, 0, 0⟩,
  ⟨114874573340038566878193838223077303523381726384491540274573058472880938300197154130738833, 3, 1, 0, 3, 0, 0⟩,
  ⟨337881953711205448614497536623421323409604869362364465110380978942065686656231579691730749, 3, 1, 1, 2, 0, 0⟩,
  ⟨280419459489226156630068274553612557679149271963655032100268409495071834718093000017485624, 3, 1, 2, 1, 0, 0⟩,
  ⟨37780601305948759053246843266736418447358435456804832130936718586904342499558574456493708, 3, 1, 3, 0, 0, 0⟩,
  ⟨31685929631699558176021431240360804787641704029404204804073974677488084744471016944052908, 4, 0, 0, 3, 0, 0⟩,
  ⟨92656129144872719902935592208453381586526223362163975963135010969444274968689039785151224, 4, 0, 1, 2, 0, 0⟩,
  ⟨76499936422682060002670733718355160252083176713757001743289090833158339564897853686174974, 4, 0, 2, 1, 0, 0⟩,
  ⟨10505451077445657642415579939102677753022156540247740693625841132973107528179830845076658, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-46512760825713826556825847246326143290468881/23117859287970064611624000000000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(1043130600611597111282845711116292762846825497976021/92211255245285224698861501856866000000000000000000)], [(-3041264753121996342630036200004554363679806069/100667309219743695086093342638500000000000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-782682036928770831658208754067622477257693931/100667309219743695086093342638500000000000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨609205702577009465603907523873586463202659001461807575, 0, 3, 0, 3, 0, 0⟩,
  ⟨1428214652539539211314104700196196903677157466685554895, 0, 3, 1, 2, 0, 0⟩,
  ⟨1006424063713745305653417868900345540065820761509485290, 0, 3, 2, 1, 0, 0⟩,
  ⟨119832943762282002926688839568759131016947296285737970, 0, 3, 3, 0, 0, 0⟩,
  ⟨2008742007258213024167505895521611891383666568787070853, 1, 2, 0, 3, 0, 0⟩,
  ⟨4755022164057849910553082855047158604884439496380508269, 1, 2, 1, 2, 0, 0⟩,
  ⟨3378071690870182692688641303186559817325540263606117054, 1, 2, 2, 1, 0, 0⟩,
  ⟨425760980037786727112000484871500688119767336012679638, 1, 2, 3, 0, 0, 0⟩,
  ⟨2202137084126280599430937219956942574219825518995870085, 2, 1, 0, 3, 0, 0⟩,
  ⟨5255115993192575270256708384714436313846625766417870445, 2, 1, 1, 2, 0, 0⟩,
  ⟨3755972292675410499004838870162643329051523432689362110, 2, 1, 2, 1, 0, 0⟩,
  ⟨493678785510398340846535546853052663737848185267361750, 2, 1, 3, 0, 0, 0⟩,
  ⟨803314482110046998706520279889667906777277748412193751, 3, 0, 0, 3, 0, 0⟩,
  ⟨1930449589669174444535274524605726894854723126947677903, 3, 0, 1, 2, 0, 0⟩,
  ⟨1386465773513882985487159730618681334007183320817491178, 3, 0, 2, 1, 0, 0⟩,
  ⟨188464451899863574500405333131061867373487942282007026, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadZeroLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(314070943014603866333/27506241720000000000)], [(-20792975056554445802338150631411813192491269/657956269410089510366623154500000000000000)], [(5037535340588364121477154023743621595496801/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-4384068370854776144414386312041795245008731/657956269410089510366623154500000000000000)], [(24265126781984507961201066675923862524567/1398157072496440209529074203312500000000)], [(-671345950625/58679982336)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨4011462016310462142683853802384381364855197093671691, 0, 3, 0, 3, 0, 0⟩,
  ⟨8538332450057904867446943514833910228801895748382883, 0, 3, 1, 2, 0, 0⟩,
  ⟨5442310026461704143787759729242993295094995721024418, 0, 3, 2, 1, 0, 0⟩,
  ⟨620320946474376890568199042955141424273297066313226, 0, 3, 3, 0, 0, 0⟩,
  ⟨13284904647297167752849073634718364258607231198293281, 1, 2, 0, 3, 0, 0⟩,
  ⟨28698962743555470288668474051282040264522739652537833, 1, 2, 1, 2, 0, 0⟩,
  ⟨18599013357793474353723463668080406538921093712327398, 1, 2, 2, 1, 0, 0⟩,
  ⟨2285258519034040467724745090863837888005585258082846, 1, 2, 3, 0, 0, 0⟩,
  ⟨14619641727465747386440340499463942753189769201582369, 2, 1, 0, 3, 0, 0⟩,
  ⟨31997879215516421203130215513185426672089949128911337, 2, 1, 1, 2, 0, 0⟩,
  ⟨21032973866327131841451105569305362635209820141517542, 2, 1, 2, 1, 0, 0⟩,
  ⟨2740698831993848909772007155793062446934640214188574, 2, 1, 3, 0, 0, 0⟩,
  ⟨5348134262324256253635509229911254620958242534770443, 3, 0, 0, 3, 0, 0⟩,
  ⟨11843054419554499213989850665081180920930627538185379, 3, 0, 1, 2, 0, 0⟩,
  ⟨7882076032531005063596567318811833675945244463643554, 3, 0, 2, 1, 0, 0⟩,
  ⟨1077696425279399809975849670665660744722859460228618, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadZero.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadZero.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadZeroLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadCapBoundaryLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-46814214854050934558552138628601501327812281/23117859287970064611624000000000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(657207341223773872612643456446128471583/57794648219925161529060000000000000000)], [(-10535205352556651021646195253207062036608129/348329789687694446664682846500000000000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-2711843715794730218486496345444943900891871/348329789687694446664682846500000000000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2976423898083919444234825290290339175675859302936587, 0, 3, 0, 3, 0, 0⟩,
  ⟨6925778279154301509098841321765934916503870194647971, 0, 3, 1, 2, 0, 0⟩,
  ⟨4824520088361190885654477690253477294274847338668706, 0, 3, 2, 1, 0, 0⟩,
  ⟨580047061050924292333990684939558546571836446957322, 0, 3, 3, 0, 0, 0⟩,
  ⟨9771978669774381813436413730684519247275047113698337, 1, 2, 0, 3, 0, 0⟩,
  ⟨22974089748907772838034798011032444697418529691606761, 1, 2, 1, 2, 0, 0⟩,
  ⟨16170467875082452393336744697509490088416551130355686, 1, 2, 2, 1, 0, 0⟩,
  ⟨2068660053447930018559042256508671993273068552447262, 1, 2, 3, 0, 0, 0⟩,
  ⟨10666728225103482864332661830726747121620400573155361, 2, 1, 0, 3, 0, 0⟩,
  ⟨25295990262972267044287455937301626740491638752023273, 2, 1, 1, 2, 0, 0⟩,
  ⟨17946169469276451245726418786809904797422287386507238, 2, 1, 2, 1, 0, 0⟩,
  ⟨2402869885125057950782401280444208909176049207639326, 2, 1, 3, 0, 0, 0⟩,
  ⟨3874290058936906773904791432169906616564705324583947, 3, 0, 0, 3, 0, 0⟩,
  ⟨9257028609790454551672653373547135659207456941635491, 3, 0, 1, 2, 0, 0⟩,
  ⟨6609571499126848574365305905065910702911061281391266, 3, 0, 2, 1, 0, 0⟩,
  ⟨917373498251938503331067750712435029018309664339722, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadCapBoundary.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadCapBoundary.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadCapBoundaryLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-49199258306854354791853981781353238528746650047811608320725943301714172080297/107612273199798089338934595645612508241020974750000000000000000000000000000000)], [(359459057374911803608389142106872460395501855944844554591906030858468613577/146352691551725401500951050078033011207788525660000000000000000000000000000)], [(-603648919111935135127150270528534171409758617860590226352481122329901079/312219075310347523202028906833137090576615521408000000000000000000000000)]], [[(461401414635094047573885987674191118803066755625365625205826036084742832578121495621/100997167376547076723855358047305766123394177650152591750000000000000000000000000000)], [(-2623340198573177169162787474809244339587014718245293/174134311488312643759924264096077300000000000000000)], [(4941247318281734257257622046556006286935637995227/371486531175066973354505096738298240000000000000)], [(-3152346095875039749952404233859018478091/1288541558012719297101994785772800000000)]], [[(-165370367899913829901591847232422136765347057967121/43533577872078160939981066024019325000000000000000)], [(33766077074878186986796846155867667609424322509/3482686229766252875198485281921546000000000000)], [(-48700594835173489097014693008887976468027859/7429730623501339467090101934765964800000000)]], [[(416589928088877360721174205096908403621/1368859907683542359162748752437500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 3231909356049506455163371457513784515948613684804882936000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨20268365887603269283027981906504780773735445360833483018578212288825642892878343779379027, 0, 4, 0, 3, 0, 0⟩,
  ⟨64311667760201293719745541779258249820923019411999206287022520632214220752429973452636331, 0, 4, 1, 2, 0, 0⟩,
  ⟨54995148173627607528253984825336700914322557762240150474946164800910088322961276548188706, 0, 4, 2, 1, 0, 0⟩,
  ⟨6806326857637199662455820671362340433614995369739935676930931960692741701534646874931402, 0, 4, 3, 0, 0, 0⟩,
  ⟨90192500969491502543760709197502893016233484687195379334654695099393979575383888701959821, 1, 3, 0, 3, 0, 0⟩,
  ⟨283096240732251086902974596326175493148882303283150266433688714032365463249671429960744713, 1, 3, 1, 2, 0, 0⟩,
  ⟨240776469504514858496605066771706299760152491916872106940321991896223441410315070242738088, 1, 3, 2, 1, 0, 0⟩,
  ⟨30887762610515892415173460823300021682493388607828075518084338579825646849777528983953196, 1, 3, 3, 0, 0, 0⟩,
  ⟨150204537167584712881465518045831599293509217452061056742655547460865253979350071499260469, 2, 2, 0, 3, 0, 0⟩,
  ⟨466433285830622661452815134829226457363565679394153469607017283312692531943065553375381657, 2, 2, 1, 2, 0, 0⟩,
  ⟨394318036646266307868538107371740890748731415534451024543384813159476266694258105648047532, 2, 2, 2, 1, 0, 0⟩,
  ⟨51997714378002971083392347626953528861634008662725656805132505292401347056167623771926344, 2, 2, 3, 0, 0, 0⟩,
  ⟨111014670235698774643406787928625953918238409665329357884725381222937989612233492010157583, 3, 1, 0, 3, 0, 0⟩,
  ⟨341123513093968323288778592866905046411877031272849384843161309966801136791061630679074499, 3, 1, 1, 2, 0, 0⟩,
  ⟨286545845839245273956536710851485021133367959051293263713720214806998324311226026760635624, 3, 1, 2, 1, 0, 0⟩,
  ⟨38626679390673560333903359324738389106598348358436793858830347195603751394897888091718708, 3, 1, 3, 0, 0, 0⟩,
  ⟨30736319044502034920505990379325528533731276064418608602468919386518754026492965433477908, 4, 0, 0, 3, 0, 0⟩,
  ⟨93480952918894674712688492201195017375782769324212208815778028495892892478549533811801224, 4, 0, 1, 2, 0, 0⟩,
  ⟨78015283207365436749845665042712914229978611245839429068679037184468455837633714807137474, 4, 0, 2, 1, 0, 0⟩,
  ⟨10712451660049021901060645055255603160346777458587688039173851336212991198077146428814158, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-39939590000138385914516708194723020165000131/23117859287970064611624000000000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(894471116168830777965261219221477405432762997976021/92211255245285224698861501856866000000000000000000)], [(-2663886646864594038955021191924027008211056069/100667309219743695086093342638500000000000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-685641773471996579714267039452681071007693931/100667309219743695086093342638500000000000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨594467602324282282784377335213393121463741431302638825, 0, 3, 0, 3, 0, 0⟩,
  ⟨1439459883058604834377967777290261751412430893335136145, 0, 3, 1, 2, 0, 0⟩,
  ⟨1029373990046523168343095311457035362713038819217872790, 0, 3, 2, 1, 0, 0⟩,
  ⟨123068937652433615310597179697398461658724357185375470, 0, 3, 3, 0, 0, 0⟩,
  ⟨1965571402511530122179402118249818966540476358309564603, 1, 2, 0, 3, 0, 0⟩,
  ⟨4788789289788687897155909953047980936253602276329252019, 1, 2, 1, 2, 0, 0⟩,
  ⟨3445205291628647799440853767221212781613754436731279554, 1, 2, 2, 1, 0, 0⟩,
  ⟨435069696375934357673609446229036031445628518711592138, 1, 2, 3, 0, 0, 0⟩,
  ⟨2160160614420510387920229183787036767806447808518363835, 2, 1, 0, 3, 0, 0⟩,
  ⟨5288821926068202328417701793255016594606381046366614195, 2, 1, 1, 2, 0, 0⟩,
  ⟨3821079647993662924079057684274794606178297605814524610, 2, 1, 2, 1, 0, 0⟩,
  ⟨502521235374160654316835171467090031785239367966274250, 2, 1, 3, 0, 0, 0⟩,
  ⟨789770516898232506364385832331361683468172678253025001, 3, 0, 0, 3, 0, 0⟩,
  ⟨1941633627333029139157303912239549691980589053597259153, 3, 0, 1, 2, 0, 0⟩,
  ⟨1407389454406448166498843523252869469492961378525878678, 3, 0, 2, 1, 0, 0⟩,
  ⟨191234179315629869793004336516203222736795003181644526, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadZeroLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(269726424526310272583/27506241720000000000)], [(-54979354458733880472210236049519216921223807/1973868808230268531099869463500000000000000)], [(4527610922282892023757583141586539075965551/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-11249454848706009767675674335832416985026193/1973868808230268531099869463500000000000000)], [(64300321071919019248267922701184673511201/4194471217489320628587222609937500000000)], [(-609067169375/58679982336)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3947103499923007195873678306051659348528046132277941, 0, 3, 0, 3, 0, 0⟩,
  ⟨8587438260184828985629751711751223974370775340739133, 0, 3, 1, 2, 0, 0⟩,
  ⟨5542528045382131491777617557001464136349223047261918, 0, 3, 2, 1, 0, 0⟩,
  ⟨634451924160628473030680877578020597381493838800726, 0, 3, 3, 0, 0, 0⟩,
  ⟨13096386722639163814036393384623198647938278314112031, 1, 2, 0, 3, 0, 0⟩,
  ⟨28846417441070046649379509413731046078361878429606583, 1, 2, 1, 2, 0, 0⟩,
  ⟨18892173186433059972728758270851816863323775691039898, 1, 2, 2, 1, 0, 0⟩,
  ⟨2325907935357829247469762389368359037900175575545346, 1, 2, 3, 0, 0, 0⟩,
  ⟨14436338366305178777223274839333349712083316317401119, 2, 1, 0, 3, 0, 0⟩,
  ⟨32145066695322652898156387602882283793311587905980087, 2, 1, 1, 2, 0, 0⟩,
  ⟨21317285461603343304657301264118250308252502120230042, 2, 1, 2, 1, 0, 0⟩,
  ⟨2779312150176217090865018616989732176399230531651074, 2, 1, 3, 0, 0, 0⟩,
  ⟨5288990309434236636420948323543105174193591573376693, 3, 0, 0, 3, 0, 0⟩,
  ⟨11891893011973078666487795589246345973882007130541629, 3, 0, 1, 2, 0, 0⟩,
  ⟨7973445818088058255787326238611781865839471789881054, 3, 0, 2, 1, 0, 0⟩,
  ⟨1089791304824230793786325667980688497401056232716118, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadZero.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadZero.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadZeroLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadCapBoundaryLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-40241044028475493916242999576998378202343531/23117859287970064611624000000000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(564033003827858057076699486993003471583/57794648219925161529060000000000000000)], [(-9229398756510276268445451280610081567858129/348329789687694446664682846500000000000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-2376064257466791630445175533628537650891871/348329789687694446664682846500000000000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2912065381696464497424649793957617159348708341542837, 0, 3, 0, 3, 0, 0⟩,
  ⟨6974884089281225627281649518683248662072749787004221, 0, 3, 1, 2, 0, 0⟩,
  ⟨4924738107281618233644335518011948135529074664906206, 0, 3, 2, 1, 0, 0⟩,
  ⟨594178038737175874796472519562437719680033219444822, 0, 3, 3, 0, 0, 0⟩,
  ⟨9583460745116377874623733480589353636606094229517087, 1, 2, 0, 3, 0, 0⟩,
  ⟨23121544446422349198745833373481450511257668468675511, 1, 2, 1, 2, 0, 0⟩,
  ⟨16463627703722038012342039300280900412819233109068186, 1, 2, 2, 1, 0, 0⟩,
  ⟨2109309469771718798304059555013193143167658869909762, 1, 2, 3, 0, 0, 0⟩,
  ⟨10483424863942914255115596170596154080513947688974111, 2, 1, 0, 3, 0, 0⟩,
  ⟨25443177742778498739313628026998483861713277529092023, 2, 1, 1, 2, 0, 0⟩,
  ⟨18230481064552662708932614481622792470464969365219738, 2, 1, 2, 1, 0, 0⟩,
  ⟨2441483203307426131875412741640878638640639525101826, 2, 1, 3, 0, 0, 0⟩,
  ⟨3815146106046887156690230525801757169800054363190197, 3, 0, 0, 3, 0, 0⟩,
  ⟨9305867202209034004170598297712300712158836533991741, 3, 0, 1, 2, 0, 0⟩,
  ⟨6700941284683901766556064824865858892805288607628766, 3, 0, 2, 1, 0, 0⟩,
  ⟨929468377796769487141543748027462781696506436827222, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadCapBoundary.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower1HeadCapBoundary.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower1HeadCapBoundaryLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-4431332756651440461141449387814368601408005139136345192094692150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(423095797379541045748562152188550259/534578778771420155200000000000000000)], [(-3634609129017190887995840251120023/6842608368274177986560000000000000)]], [[(4218250533328254666013211470484069387332083459447804235593341004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5994035210099497485829796500222859136689/181232981107021044050303250000000000000)], [(245424351899/8141516800)], [(-78220125/10176896)]], [[(-2531593290219647285551430339798172113311/362465962214042088100606500000000000000)], [(221074063/12721120)], [(-234660375/20353792)]], [[(13/20)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 756823434210800748985880482465584136687241071500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2861532267899236933271967997678507923939523540940639267083478151117097595643113, 0, 4, 0, 3, 0, 0⟩,
  ⟨8388850272620714501547715434916150517178985979592084237699596142865452943179339, 0, 4, 1, 2, 0, 0⟩,
  ⟨16475970647742027409543194322406092553788047608751737103050272248120579896304339, 0, 4, 2, 1, 0, 0⟩,
  ⟨6148506138385878320668068848489315451082984238596519396838451131372224548768113, 0, 4, 3, 0, 0, 0⟩,
  ⟨23617973159022198291391946020586028204427399516751661044604739699253493060353252, 1, 3, 0, 3, 0, 0⟩,
  ⟨56956964410418201145098418320023235583913647420320840959209981400841533868559756, 1, 3, 1, 2, 0, 0⟩,
  ⟨72781296836950440581642103853435402287731398801804839386728492924198467462309756, 1, 3, 2, 1, 0, 0⟩,
  ⟨18292121602056438904863910481615054546538256947732882372513876222610426654103252, 1, 3, 3, 0, 0, 0⟩,
  ⟨61677858386046184205369824857839917783807538436891163161003248193840865194505302, 2, 2, 0, 3, 0, 0⟩,
  ⟨138864913772838993878102341501082279611164783986231190243161306579680798708515906, 2, 2, 1, 2, 0, 0⟩,
  ⟨129584715561724270019793698830123787980278810072303839840520076619220837771015906, 2, 2, 2, 1, 0, 0⟩,
  ⟨17550028074265008938543059821969895580942586176145522047912799483380904257005302, 2, 2, 3, 0, 0, 0⟩,
  ⟨65836351374034273868443408527960606621948567050611338758101670915061641590523300, 3, 1, 0, 3, 0, 0⟩,
  ⟨145470947553803018636211097315892030832527896680380800519686246590314807584069900, 3, 1, 1, 2, 0, 0⟩,
  ⟨110863805141203135999047927657202744178244871683678174561610331520344592740319900, 3, 1, 2, 1, 0, 0⟩,
  ⟨5783910692056798801061645209881141870965863485765371735572630845091426746773300, 3, 1, 3, 0, 0, 0⟩,
  ⟨25064283337683789471823898931804514834654959054091921464219684269357171860728137, 4, 0, 0, 3, 0, 0⟩,
  ⟨55622196294479726753550470416245753436175937528560539266835325268610089800934411, 4, 0, 1, 2, 0, 0⟩,
  ⟨38032464144405494503244150074437183079987576198109609273568475577201642535309411, 4, 0, 2, 1, 0, 0⟩,
  ⟨526847540035088897344764259813291101504604483316936752935256452948724595103137, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-471577819842998606581001153797673073129/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(5174170580594332314690692996593362972005483/812782596260958971681199000000000000000000)], [(-2419165294819/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-226363679141/63605600000)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-10492667313488366792145471030249198757/8178224269671439965600000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 416144689285610993500773888000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨1069462132581415963928487105294536826414112663, 0, 3, 0, 3, 0, 0⟩,
  ⟨3380654263251374534648788682866707087111019239, 0, 3, 1, 2, 0, 0⟩,
  ⟨9793604018305661899560020706190647229844934864, 0, 3, 2, 1, 0, 0⟩,
  ⟨5226519303957171791429248181352851969148028288, 0, 3, 3, 0, 0, 0⟩,
  ⟨8452804234094322107249020625662873079260901061, 1, 2, 0, 3, 0, 0⟩,
  ⟨17034565016282013664189423639278044061388746933, 1, 2, 1, 2, 0, 0⟩,
  ⟨25516430004404651350707914892919686989590493808, 1, 2, 2, 1, 0, 0⟩,
  ⟨9708871746495878777015818783601391007462647936, 1, 2, 3, 0, 0, 0⟩,
  ⟨17134515435802106983652711563998451359279464133, 2, 1, 0, 3, 0, 0⟩,
  ⟨32326936664542028774433142407271913901444436149, 2, 1, 1, 2, 0, 0⟩,
  ⟨27414045057381624655156571214042879329646183024, 2, 1, 2, 1, 0, 0⟩,
  ⟨4537706628235135443104167021160041787481211008, 2, 1, 3, 0, 0, 0⟩,
  ⟨10229733068652624913082172002447907106432675735, 3, 0, 0, 3, 0, 0⟩,
  ⟨20108705114601661863142489327313952927166708455, 3, 0, 1, 2, 0, 0⟩,
  ⟨13126898274372907422258658903767215569900624080, 3, 0, 2, 1, 0, 0⟩,
  ⟨533913920059852530267590377729294749166591360, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(10492667313488366792145471030249198757/8178224269671439965600000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10492667313488366792145471030249198757/8178224269671439965600000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-145574515429127804300290651129487273/855326046034272248320000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(2852448748993382904820519021173690280411/459069526269957058278000000000000000000)], [(-2384750848883/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-75189533/20353792)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-36224015925813285896519171661161126661491/9401743898008720553533440000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 235043597450218013838336000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨905600398145332147412979291529028166537275, 0, 3, 0, 3, 0, 0⟩,
  ⟨7980490670512008549662932006490556178724325, 0, 3, 1, 2, 0, 0⟩,
  ⟨16768993413770828181542110920286625166430575, 0, 3, 2, 1, 0, 0⟩,
  ⟨8419947488380411854180341799075097154243525, 0, 3, 3, 0, 0, 0⟩,
  ⟨2837498414717736932371152005744768410908849, 1, 2, 0, 3, 0, 0⟩,
  ⟨20359430655466741080434007517734720270064047, 1, 2, 1, 2, 0, 0⟩,
  ⟨41698437613870692343181912585787927233182797, 1, 2, 2, 1, 0, 0⟩,
  ⟨20095286804513339696530131292547975374027599, 1, 2, 3, 0, 0, 0⟩,
  ⟨4345656629967003685599056916302452322205873, 2, 1, 0, 3, 0, 0⟩,
  ⟨19859788847790005968876128288197772003955119, 2, 1, 1, 2, 0, 0⟩,
  ⟨34682448548804608368810731741915978967073869, 2, 1, 2, 1, 0, 0⟩,
  ⟨14828346152836128863691258026270659285324623, 2, 1, 3, 0, 0, 0⟩,
  ⟨2684054989764790413066749188710712077834299, 3, 0, 0, 3, 0, 0⟩,
  ⟨8291737991945847975382647736825607912615397, 3, 0, 1, 2, 0, 0⟩,
  ⟨10563893477815318744448525036286676900321647, 3, 0, 2, 1, 0, 0⟩,
  ⟨3423303213073392533767333519421781065540549, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(36224015925813285896519171661161126661491/9401743898008720553533440000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(36224015925813285896519171661161126661491/9401743898008720553533440000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardRightLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-20690417652172137151278069042805304949750340226440258206672616094448583539/565096618596266793016980512000000000000000000000000)], [(2188758673898363809783634349709253993398843463650685247998872004578281/22603864743850671720679220480000000000000000000)], [(-17768226637330148792689116774323247085387269913862494963400633652597/289329468721288598024694022144000000000000000)]], [[(186798988495503444275262858708169538426124134979057821628622978360408903/141274154649066698254245128000000000000000000000)], [(-106317882055121891029473364078021607335515768609/26894677387974400000000)], [(1239587439146065379250229551165192175456871361/344251870566072320000)], [(-15295541933292935457516910698836992232895/17212593528303616)]], [[(-9989345948683760086080691729766438407019717031/13447338693987200000000)], [(1018558579579581592231762547161256137404477/537893547759488000)], [(-45886625799878806372550732096510976698685/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-21073462214284472433442851214763222672449693767930170995106636931948721/56509661859626679301698051200000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 36166183590161074753086752768000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨16339283818694850369355709284021620509361338072406991948963904116781065639, 0, 3, 0, 3, 0, 0⟩,
  ⟨65196490954505976516768040564490053346609137405855302154133224327800178167, 0, 3, 1, 2, 0, 0⟩,
  ⟨194245062403289077644950971691043442129107965796582033095416467452528643792, 0, 3, 2, 1, 0, 0⟩,
  ⟨104587435231071085448137505786285433334591846222332693349231522241509531264, 0, 3, 3, 0, 0, 0⟩,
  ⟨136387845054848395548816963749456169185066162621996530108431320605280847093, 1, 2, 0, 3, 0, 0⟩,
  ⟨300458864663840036721343175405153293475745596915641872934824952748213485029, 1, 2, 1, 2, 0, 0⟩,
  ⟨495704896903296699948717485788748188338740701712210033875735824622398881904, 1, 2, 2, 1, 0, 0⟩,
  ⟨200946993423844912445647947536480453058780278585722008734889067479466243968, 1, 2, 3, 0, 0, 0⟩,
  ⟨284524582207776398095581043073153214382090270315845388289369077500218497269, 2, 1, 0, 3, 0, 0⟩,
  ⟨553045759547490982136631175381724692782915543016585020426835678433026435557, 2, 1, 1, 2, 0, 0⟩,
  ⟨508684954063087924812210781160881586554453122446252102339011192807211832432, 2, 1, 2, 1, 0, 0⟩,
  ⟨101191269091673646258277399532037614046870832802230194195685216874403894144, 2, 1, 3, 0, 0, 0⟩,
  ⟨173131325889865096012756255603324533894070849338890280756742237011718715815, 3, 0, 0, 3, 0, 0⟩,
  ⟨343749300592883651221965441527879057216835294224701741526665678012613128695, 3, 0, 1, 2, 0, 0⟩,
  ⟨233191034317807031798353668049994444907876597248527393439213563637341594320, 3, 0, 2, 1, 0, 0⟩,
  ⟨13487015817142062357403424777448462510367804011475309436868247636447181440, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(21073462214284472433442851214763222672449693767930170995106636931948721/56509661859626679301698051200000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(21073462214284472433442851214763222672449693767930170995106636931948721/56509661859626679301698051200000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-3498116332725399241815061395769916844657/33618346734968000)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 33618346734968000
def dCertificate : TensorBernstein3 := [
  ⟨3498116332725399241815061395769916844657, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(3498116332725399241815061395769916844657/33618346734968000) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3498116332725399241815061395769916844657/33618346734968000) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper0HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper0HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-3749627361259356829044446177511919411344480294058021813188442150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(745658156744762367554288939637959293/1069157557542840310400000000000000000)], [(-3297437173686884379523502527008873/6842608368274177986560000000000000)]], [[(3572148473661177682127797497000020533994578295671356774655841004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5225940290395326879470059930315437261689/181232981107021044050303250000000000000)], [(219015142949/8141516800)], [(-70963875/10176896)]], [[(-2179491068398648830876733132766922113311/362465962214042088100606500000000000000)], [(390222401/25442240)], [(-212891625/20353792)]], [[(13/20)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 756823434210800748985880482465584136687241071500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2332205401839678928365531086348928259578002105917186805889289114557039001893113, 0, 4, 0, 3, 0, 0⟩,
  ⟨9888218818376388287086393702319767072180433527117586884708494948102269349429339, 0, 4, 1, 2, 0, 0⟩,
  ⟨18059370643904889234824622574294656783822058516134943615061953839917454896304339, 0, 4, 2, 1, 0, 0⟩,
  ⟨6148506138385878320668068848489315451082984238596519396838451131372224548768113, 0, 4, 3, 0, 0, 0⟩,
  ⟨21452924163486638826709997348807666859581056317586907276357135981357985247853252, 1, 3, 0, 3, 0, 0⟩,
  ⟨63269474462146534043091063223033463308195352899018816704777726311852276056059756, 1, 3, 1, 2, 0, 0⟩,
  ⟨79296815775862967436272390722865489791570007591552639701325091553104717462309756, 1, 3, 2, 1, 0, 0⟩,
  ⟨18292121602056438904863910481615054546538256947732882372513876222610426654103252, 1, 3, 3, 0, 0, 0⟩,
  ⟨58408927866891978347506640800242000351933780904767405196960727509514693319505302, 2, 2, 0, 3, 0, 0⟩,
  ⟨148741376783897299455292119471422681128476611206895962131111929731292126833515906, 2, 2, 1, 2, 0, 0⟩,
  ⟨139497397172460036332883999389413350695529426533631569521614782955158337771015906, 2, 2, 2, 1, 0, 0⟩,
  ⟨17550028074265008938543059821969895580942586176145522047912799483380904257005302, 2, 2, 3, 0, 0, 0⟩,
  ⟨63684071335025974748156401415714069945201790242106563489201434553855586903023300, 3, 1, 0, 3, 0, 0⟩,
  ⟨152270211841695059152927966027814269671247824700675967471138603381452502896569900, 3, 1, 1, 2, 0, 0⟩,
  ⟨117454864291594602055604652952770983964394127293238309653056674672688342740319900, 3, 1, 2, 1, 0, 0⟩,
  ⟨5783910692056798801061645209881141870965863485765371735572630845091426746773300, 3, 1, 3, 0, 0, 0⟩,
  ⟨24545211688353694749624564116707113909297118013569602852308553911141839829478137, 4, 0, 0, 3, 0, 0⟩,
  ⟨57358139077286120805531527793434201926864296259363407428895905013910382769684411, 4, 0, 1, 2, 0, 0⟩,
  ⟨39642960626810859276059433428257383424690813228706608486505029430717267535309411, 4, 0, 2, 1, 0, 0⟩,
  ⟨526847540035088897344764259813291101504604483316936752935256452948724595103137, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(6626429622990288871983149405879873489184656487063236607283087689747124091/9518953478445932420867099531683803145474500000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-405119042073610645478178104704931354379/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(4403198873547694503433467762425394222005483/812782596260958971681199000000000000000000)], [(-4239284140313/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-192037585391/63605600000)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-10492667313488366792145471030249198757/8178224269671439965600000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 416144689285610993500773888000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨820697943752467511951816470150480017338643913, 0, 3, 0, 3, 0, 0⟩,
  ⟨4085302419157715461376493273082000817690550489, 0, 3, 1, 2, 0, 0⟩,
  ⟨10537743870056347322845829037018747769499934864, 0, 3, 2, 1, 0, 0⟩,
  ⟨5226519303957171791429248181352851969148028288, 0, 3, 3, 0, 0, 0⟩,
  ⟨7734593167126416441861911393620327652034494811, 1, 2, 0, 3, 0, 0⟩,
  ⟨19153466994026850857731845187250050253127340683, 1, 2, 1, 2, 0, 0⟩,
  ⟨27683227156203632001665974481527988608555493808, 1, 2, 2, 1, 0, 0⟩,
  ⟨9708871746495878777015818783601391007462647936, 1, 2, 3, 0, 0, 0⟩,
  ⟨16462301295749710667100564984920530932053057883, 2, 1, 0, 3, 0, 0⟩,
  ⟨34419309519393258356641211207345045093183029899, 2, 1, 1, 2, 0, 0⟩,
  ⟨29465817745411538004229544893975180948611183024, 2, 1, 2, 1, 0, 0⟩,
  ⟨4537706628235135443104167021160041787481211008, 2, 1, 3, 0, 0, 0⟩,
  ⟨10026965806739185809940464020268475297357206985, 3, 0, 0, 3, 0, 0⟩,
  ⟨20786824147614395178535841169630371657746239705, 3, 0, 1, 2, 0, 0⟩,
  ⟨13756013662354525543659381325919316109555624080, 3, 0, 2, 1, 0, 0⟩,
  ⟨533913920059852530267590377729294749166591360, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(10492667313488366792145471030249198757/8178224269671439965600000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10492667313488366792145471030249198757/8178224269671439965600000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-124307706542923656747387275419809923/855326046034272248320000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(2416994523042161322636263028986190280411/459069526269957058278000000000000000000)], [(-4170455248441/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-64205183/20353792)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-33413914950620420017087704446882032517741/9401743898008720553533440000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 235043597450218013838336000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨835347873765510500427192611172050812943525, 0, 3, 0, 3, 0, 0⟩,
  ⟨8589242118775077515883045275584811442318075, 0, 3, 1, 2, 0, 0⟩,
  ⟨17400050253643241681260164737594835137211825, 0, 3, 2, 1, 0, 0⟩,
  ⟨8490200012760233501166128479432074507837275, 0, 3, 3, 0, 0, 0⟩,
  ⟨2642601615099277182344547498923836350127599, 1, 2, 0, 3, 0, 0⟩,
  ⟨22188485062399870268481135112267486060845297, 1, 2, 1, 2, 0, 0⟩,
  ⟨43554543799428020038665153165712557145526547, 1, 2, 2, 1, 0, 0⟩,
  ⟨20306044377652804637487491333618907434808849, 1, 2, 3, 0, 0, 0⟩,
  ⟨4176739455830334022460316093731520261424623, 2, 1, 0, 3, 0, 0⟩,
  ⟨21673859282459024673255166219980537794736369, 2, 1, 1, 2, 0, 0⟩,
  ⟨36473587513933205591611065849840608879417619, 2, 1, 2, 1, 0, 0⟩,
  ⟨15039103725975593804648618067341591346105873, 2, 1, 3, 0, 0, 0⟩,
  ⟨2639782090866758852968826192603734724240549, 3, 0, 0, 3, 0, 0⟩,
  ⟨8885505467944806457934671343169863176209147, 3, 0, 1, 2, 0, 0⟩,
  ⟨11129983097259001771483672381594886871102897, 3, 0, 2, 1, 0, 0⟩,
  ⟨3493555737453214180753120199778758419134299, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(33413914950620420017087704446882032517741/9401743898008720553533440000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(33413914950620420017087704446882032517741/9401743898008720553533440000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardRightLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-17766391642285413927111194132096021186824473887119982126559315794964677289/565096618596266793016980512000000000000000000000000)], [(3886047468131445379000312578196296956674433855682441649743116247721287/45207729487701343441358440960000000000000000000)], [(-16119920724534344743834037552784249779216493821233331700389025732747/289329468721288598024694022144000000000000000)]], [[(158911162886009819409190778899958644331684872993101124196662040860408903/141274154649066698254245128000000000000000000000)], [(-186279164459333287183623051027704234952990566643/53789354775948800000000)], [(1110482824790162696258982751571073446463517311/344251870566072320000)], [(-13876619678266407912161964215966555438145/17212593528303616)]], [[(-8479080573489899829993520567061217243607685781/13447338693987200000000)], [(1783271967734917406599525168536991132228179/1075787095518976000)], [(-41629859034799223736485892647899666314435/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-25327112277506789175731902227076600984678849997546659960347039619900278329/72332367180322149506173505536000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 72332367180322149506173505536000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨25327112277506789175731902227076600984678849997546659960347039619900278329, 0, 3, 0, 3, 0, 0⟩,
  ⟨160822489706937493059751144176355450986017543222963454676527148644356672487, 0, 3, 1, 2, 0, 0⟩,
  ⟨420348138367638815175765069363975212988893814479460831246001359160469541237, 0, 3, 2, 1, 0, 0⟩,
  ⟨210821789818919506435349958900391190705240450470069345611852500136013147079, 0, 3, 3, 0, 0, 0⟩,
  ⟨251737096663828890854431414987359327741131087436155031169695585369576135339, 1, 2, 0, 3, 0, 0⟩,
  ⟨692385577298213004103324163154501841390820477095886184409176255462695918517, 1, 2, 1, 2, 0, 0⟩,
  ⟨1084610120737573445235899944064769574478157366403133672820520922011034524767, 1, 2, 2, 1, 0, 0⟩,
  ⟨406834744918021831508520737056421878225730831247655894209946501917914741589, 1, 2, 3, 0, 0, 0⟩,
  ⟨549674385951049382693695835367718552058621479107349915377096349159451435691, 2, 1, 0, 3, 0, 0⟩,
  ⟨1196599747476277491954569745188753575307727984473625107519091956832321819573, 2, 1, 1, 2, 0, 0⟩,
  ⟨1106409534791376594782438863008066071809548723686516635261815658380660425823, 2, 1, 2, 1, 0, 0⟩,
  ⟨207323296253679299133779641047536200201911939680672265131538800707790041941, 2, 1, 3, 0, 0, 0⟩,
  ⟨340575011401211767208269256598647561677540048814010405421428955409775578681, 3, 0, 0, 3, 0, 0⟩,
  ⟨716968489394455439490815528184242394029037472036508961547486306013982573543, 3, 0, 1, 2, 0, 0⟩,
  ⟨494079381930895423302122790280906919446397593198650377448339551530095442293, 3, 0, 2, 1, 0, 0⟩,
  ⟨28620950991061460253881796882717249056792366048354577787125950925888447431, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(25327112277506789175731902227076600984678849997546659960347039619900278329/72332367180322149506173505536000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(25327112277506789175731902227076600984678849997546659960347039619900278329/72332367180322149506173505536000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-3498116332725399241815061395769916844657/33618346734968000)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 33618346734968000
def dCertificate : TensorBernstein3 := [
  ⟨3498116332725399241815061395769916844657, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(3498116332725399241815061395769916844657/33618346734968000) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3498116332725399241815061395769916844657/33618346734968000) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.LineUpper1HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.LineUpper1HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-4431332756651440461141449387814368601408005139136345192094692150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(423095797379541045748562152188550259/534578778771420155200000000000000000)], [(-3634609129017190887995840251120023/6842608368274177986560000000000000)]], [[(4218250533328254666013211470484069387332083459447804235593341004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5994035210099497485829796500222859136689/181232981107021044050303250000000000000)], [(245424351899/8141516800)], [(-78220125/10176896)]], [[(-2531593290219647285551430339798172113311/362465962214042088100606500000000000000)], [(221074063/12721120)], [(-234660375/20353792)]], [[(13/20)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 756823434210800748985880482465584136687241071500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨25435111708356820855311609105031712619153700571635928986134441704411291446173449, 0, 4, 0, 3, 0, 0⟩,
  ⟨56734681406498820904013600935927346789672162081192561832579597573772448557270347, 0, 4, 1, 2, 0, 0⟩,
  ⟨39144949256424588653707280594118776433483800750741631839312747882364001291645347, 0, 4, 2, 1, 0, 0⟩,
  ⟨897675910708120280832474433040488886003346000860944274850013888002844180548449, 0, 4, 3, 0, 0, 0⟩,
  ⟨111649459826719962153946308492640359592020167652443270412367528288629618378563428, 1, 3, 0, 3, 0, 0⟩,
  ⟨249110527366271069664263871965417397390981697040578819669794845373853210604440284, 1, 3, 1, 2, 0, 0⟩,
  ⟨168459417893758324285505558439662587168668585261549027177260201301892028963815284, 1, 3, 2, 1, 0, 0⟩,
  ⟨2532311368492898986633395076981174152589119374694460891024290466668436737938428, 1, 3, 3, 0, 0, 0⟩,
  ⟨183543902078666032471976814563109006109863475048879878256383606614717807272014334, 2, 2, 0, 3, 0, 0⟩,
  ⟨409922317086144731630043491871681668710109514318933517023761482623315042909793002, 2, 2, 1, 2, 0, 0⟩,
  ⟨272596000449119030990334389524283150211598484899982331087904363793132181581668002, 2, 2, 2, 1, 0, 0⟩,
  ⟨2489284662127164824242584321448395428322859888745338896454222159534945943889334, 2, 2, 3, 0, 0, 0⟩,
  ⟨133939177583975221884044719573730959294018143406018621055485570683879925193032180, 3, 1, 0, 3, 0, 0⟩,
  ⟨299615174609221544649004503574311834934240862029468767809950877178224248235346540, 3, 1, 1, 2, 0, 0⟩,
  ⟨196534938839269614572386365879340655208660119985026511803954813593108281438471540, 3, 1, 2, 1, 0, 0⟩,
  ⟨1009642621842037860348868439218107345884066414070490415700444598763958396157180, 3, 1, 3, 0, 0, 0⟩,
  ⟨36610649375534736482652453723106296289880018504560345320935050653380444853407825, 4, 0, 0, 3, 0, 0⟩,
  ⟨82071780738436279095060830706747305224017531869764291910204642354989967372723475, 4, 0, 1, 2, 0, 0⟩,
  ⟨53256484283071536529699802175228404130823068795694359340797903219504127528973475, 4, 0, 2, 1, 0, 0⟩,
  ⟨156019169362057513857054086586093317005862965772929231020499017894605009657825, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-471577819842998606581001153797673073129/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(5174170580594332314690692996593362972005483/812782596260958971681199000000000000000000)], [(-2419165294819/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-226363679141/63605600000)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-20599778317492683276816943358722925029/40891121348357199828000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 416144689285610993500773888000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨10554005187152299424880657136577587954763337111, 0, 3, 0, 3, 0, 0⟩,
  ⟨21081521470100685398537944729702995472158692583, 0, 3, 1, 2, 0, 0⟩,
  ⟨14099714629871930957654114306156258114892608208, 0, 3, 2, 1, 0, 0⟩,
  ⟨858186038559527042066075511858975597497252736, 0, 3, 3, 0, 0, 0⟩,
  ⟨35564121495289619295191702991907917337628688581, 1, 2, 0, 3, 0, 0⟩,
  ⟨71304934030089877096900079430301849336492109493, 1, 2, 1, 2, 0, 0⟩,
  ⟨45744088519146169458125505107073571014693856368, 1, 2, 2, 1, 0, 0⟩,
  ⟨1729356108208035986899339840554639015830435456, 1, 2, 3, 0, 0, 0⟩,
  ⟨39870071115350467455178448112950953890967365829, 2, 1, 0, 3, 0, 0⟩,
  ⟨80418370072786803130283425006024111496508141237, 2, 1, 1, 2, 0, 0⟩,
  ⟨50023496310133480128432983285711641924709888112, 2, 1, 2, 1, 0, 0⟩,
  ⟨1069394525513446940084682339904109319169112704, 2, 1, 3, 0, 0, 0⟩,
  ⟨14871372152908387608085089490011792508102014359, 3, 0, 0, 3, 0, 0⟩,
  ⟨30229209549883331501574352002598761632174724327, 3, 0, 1, 2, 0, 0⟩,
  ⟨18413374457944961697614654181967833024908639952, 3, 0, 2, 1, 0, 0⟩,
  ⟨209641801560178018469105243599613900835929984, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(20599778317492683276816943358722925029/40891121348357199828000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(20599778317492683276816943358722925029/40891121348357199828000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-145574515429127804300290651129487273/855326046034272248320000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(2852448748993382904820519021173690280411/459069526269957058278000000000000000000)], [(-2384750848883/127211200000)], [(28173985411/1628303360)], [(-43455625/10176896)]], [[(-75189533/20353792)], [(23150327/2544224)], [(-130366875/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-3785279667251236203828075717736193/577395105173075400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 117521798725109006919168000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨1024379743864452545884001670929338290247227, 0, 3, 0, 3, 0, 0⟩,
  ⟨3192925742919096005743205098134750710297931, 0, 3, 1, 2, 0, 0⟩,
  ⟨4329003485853831390276143747865285204151056, 0, 3, 2, 1, 0, 0⟩,
  ⟨1394003855518753606234293836284872784100352, 0, 3, 3, 0, 0, 0⟩,
  ⟨3606651795587448421882479424505923918579889, 1, 2, 0, 3, 0, 0⟩,
  ⟨10300694482036857874715709866550479274408417, 1, 2, 1, 2, 0, 0⟩,
  ⟨12556521107623506363450870819140832755967792, 1, 2, 2, 1, 0, 0⟩,
  ⟨3525872977475176924874124752096277400139264, 1, 2, 3, 0, 0, 0⟩,
  ⟨4231257609672470609801516296264832966418097, 2, 1, 0, 3, 0, 0⟩,
  ⟨11251140105816480828832603289569706417923041, 2, 1, 1, 2, 0, 0⟩,
  ⟨12292825233677757180252037981933809899482416, 2, 1, 2, 1, 0, 0⟩,
  ⟨2899092743977209962281859191753936447977472, 2, 1, 3, 0, 0, 0⟩,
  ⟨1652209886019296824516872835936247338085435, 3, 0, 0, 3, 0, 0⟩,
  ⟨4153044350908185232001601400897977853812555, 3, 0, 1, 2, 0, 0⟩,
  ⟨4074980596117548479218813790402262347665680, 3, 0, 2, 1, 0, 0⟩,
  ⟨770447950090608734355862569190531831938560, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(3785279667251236203828075717736193/577395105173075400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3785279667251236203828075717736193/577395105173075400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardRightLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-20690417652172137151278069042805304949750340226440258206672616094448583539/565096618596266793016980512000000000000000000000000)], [(2188758673898363809783634349709253993398843463650685247998872004578281/22603864743850671720679220480000000000000000000)], [(-17768226637330148792689116774323247085387269913862494963400633652597/289329468721288598024694022144000000000000000)]], [[(186798988495503444275262858708169538426124134979057821628622978360408903/141274154649066698254245128000000000000000000000)], [(-106317882055121891029473364078021607335515768609/26894677387974400000000)], [(1239587439146065379250229551165192175456871361/344251870566072320000)], [(-15295541933292935457516910698836992232895/17212593528303616)]], [[(-9989345948683760086080691729766438407019717031/13447338693987200000000)], [(1018558579579581592231762547161256137404477/537893547759488000)], [(-45886625799878806372550732096510976698685/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 36166183590161074753086752768000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨180152445662420958600518823901941694988692271447890199308322358586689811623, 0, 3, 0, 3, 0, 0⟩,
  ⟨364812659910551238985253146423730540500699560551701497181406042737526416119, 0, 3, 1, 2, 0, 0⟩,
  ⟨254254393635474619561641372945845928191740863575527149093953928362254881744, 0, 3, 2, 1, 0, 0⟩,
  ⟨20508135589697924945165993076065623604989226120475227988448369211418277248, 0, 3, 3, 0, 0, 0⟩,
  ⟨608071253862634980482027180054303681310051409439362774070971546020127243253, 1, 2, 0, 3, 0, 0⟩,
  ⟨1232102232798199769365699406465681577539738324889845156376188821492752673509, 1, 2, 1, 2, 0, 0⟩,
  ⟨817715829829398559307259789091976166623924965221843136396921792116938070384, 1, 2, 2, 1, 0, 0⟩,
  ⟨44041464175689203251630170458588502575580087534330516513579516644312640128, 1, 2, 3, 0, 0, 0⟩,
  ⟨682873070106581375876439218897074639109310311094402643303241185120185051637, 2, 1, 0, 3, 0, 0⟩,
  ⟨1388464168209201918751568150260343280529010604046056050192244771292926098661, 2, 1, 1, 2, 0, 0⟩,
  ⟨887412468907268953778238216662696820098981929646413588467684930667111495536, 2, 1, 2, 1, 0, 0⟩,
  ⟨29792728761298519254417672899383020266198757274421576119696969494370448512, 2, 1, 3, 0, 0, 0⟩,
  ⟨255160757775646312816618223706683812908089659144839171831314301686747620007, 3, 0, 0, 3, 0, 0⟩,
  ⟨521794082929390264836183973104305723850387297833639700869628904537699841271, 3, 0, 1, 2, 0, 0⟩,
  ⟨324570520321181890497681883402480062027213286125824911036883978912428306896, 3, 0, 2, 1, 0, 0⟩,
  ⟨6465896044586199769640856478831301415746381902475390885288126061476085632, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-3498116332725399241815061395769916844657/33618346734968000)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 33618346734968000
def dCertificate : TensorBernstein3 := [
  ⟨3498116332725399241815061395769916844657, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(3498116332725399241815061395769916844657/33618346734968000) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3498116332725399241815061395769916844657/33618346734968000) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper0HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper0HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-3749627361259356829044446177511919411344480294058021813188442150109/15231882996669345366073446917469447615000000000000000000000000000000)], [(745658156744762367554288939637959293/1069157557542840310400000000000000000)], [(-3297437173686884379523502527008873/6842608368274177986560000000000000)]], [[(3572148473661177682127797497000020533994578295671356774655841004034176181913/378411717105400374492940241232792068343620535750000000000000000000000000000)], [(-5225940290395326879470059930315437261689/181232981107021044050303250000000000000)], [(219015142949/8141516800)], [(-70963875/10176896)]], [[(-2179491068398648830876733132766922113311/362465962214042088100606500000000000000)], [(390222401/25442240)], [(-212891625/20353792)]], [[(13/20)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 756823434210800748985880482465584136687241071500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨24916040059026726133112274289934311693795859531113610374223311346195959414923449, 0, 4, 0, 3, 0, 0⟩,
  ⟨58470624189305214955994658313115795280360520811995429994640177319072741526020347, 0, 4, 1, 2, 0, 0⟩,
  ⟨40755445738829953426522563947938976778187037781338631052249301735879626291645347, 0, 4, 2, 1, 0, 0⟩,
  ⟨897675910708120280832474433040488886003346000860944274850013888002844180548449, 0, 4, 3, 0, 0, 0⟩,
  ⟨109595050129279439089365691795664115383482634403716034079932985395746317597313428, 1, 3, 0, 3, 0, 0⟩,
  ⟨256095898952395694025717493218713608737926596072205592442870638318860534823190284, 1, 3, 1, 2, 0, 0⟩,
  ⟨174858488805279326826151294192436398702945323652781408475153349639782653963815284, 1, 3, 2, 1, 0, 0⟩,
  ⟨2532311368492898986633395076981174152589119374694460891024290466668436737938428, 1, 3, 3, 0, 0, 0⟩,
  ⟨180501192453579011056862208451899018022551560003302846054008674147859897115764334, 2, 2, 0, 3, 0, 0⟩,
  ⟨420454017569802283090844942339805837636990108751586004075434953299035257753543002, 2, 2, 1, 2, 0, 0⟩,
  ⟨282113865231052346301755601148016184031432657165960377868808235685710306581668002, 2, 2, 2, 1, 0, 0⟩,
  ⟨2489284662127164824242584321448395428322859888745338896454222159534945943889334, 2, 2, 3, 0, 0, 0⟩,
  ⟨131940885522816457549934751473441244589917611264270699083695594245952679099282180, 3, 1, 0, 3, 0, 0⟩,
  ⟨306665907346882628562587120766989614787792554866631706234988539925843877141596540, 3, 1, 1, 2, 0, 0⟩,
  ⟨202814932301674886341794332499739239155840901243886560433204327778655156438471540, 3, 1, 2, 1, 0, 0⟩,
  ⟨1009642621842037860348868439218107345884066414070490415700444598763958396157180, 3, 1, 3, 0, 0, 0⟩,
  ⟨36119728891352565221275809852147726389911709200184537830996594147643140165907825, 4, 0, 0, 3, 0, 0⟩,
  ⟨83840241795758041857314561307408679006945170575098647894584047626596412685223475, 4, 0, 1, 2, 0, 0⟩,
  ⟨54807187392659130755517009570847565447743179149211743274100139996847877528973475, 4, 0, 2, 1, 0, 0⟩,
  ⟨156019169362057513857054086586093317005862965772929231020499017894605009657825, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(78493299640060630564380035260338494475134499238018907024789775941542259/380758139137837296834683981267352125818980000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-405119042073610645478178104704931354379/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(4403198873547694503433467762425394222005483/812782596260958971681199000000000000000000)], [(-4239284140313/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-192037585391/63605600000)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-20599778317492683276816943358722925029/40891121348357199828000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 416144689285610993500773888000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨10351237925238860321738949154398156145687868361, 0, 3, 0, 3, 0, 0⟩,
  ⟨21759640503113418713931296572019414202738223833, 0, 3, 1, 2, 0, 0⟩,
  ⟨14728830017853549079054836728308358654547608208, 0, 3, 2, 1, 0, 0⟩,
  ⟨858186038559527042066075511858975597497252736, 0, 3, 3, 0, 0, 0⟩,
  ⟨34974218720639142912060721924434059410402282331, 1, 2, 0, 3, 0, 0⟩,
  ⟨73322589623666750329678131136200293028230703243, 1, 2, 1, 2, 0, 0⟩,
  ⟨47584099774642294720622440224195872633658856368, 1, 2, 2, 1, 0, 0⟩,
  ⟨1729356108208035986899339840554639015830435456, 1, 2, 3, 0, 0, 0⟩,
  ⟨39300052078440465985174354105585283463740959579, 2, 1, 0, 3, 0, 0⟩,
  ⟨82416714731498329596648818288115492688246734987, 2, 1, 1, 2, 0, 0⟩,
  ⟨51812078501126222249381287469699943543674888112, 2, 1, 2, 1, 0, 0⟩,
  ⟨1069394525513446940084682339904109319169112704, 2, 1, 3, 0, 0, 0⟩,
  ⟨14688488628735423418070268567940548199026545609, 3, 0, 0, 3, 0, 0⟩,
  ⟨30888017648030718050555045421108117862754255577, 3, 0, 1, 2, 0, 0⟩,
  ⟨18991060781423196677466745670985933564563639952, 3, 0, 2, 1, 0, 0⟩,
  ⟨209641801560178018469105243599613900835929984, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(20599778317492683276816943358722925029/40891121348357199828000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(20599778317492683276816943358722925029/40891121348357199828000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-124307706542923656747387275419809923/855326046034272248320000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(2416994523042161322636263028986190280411/459069526269957058278000000000000000000)], [(-4170455248441/254422400000)], [(25239628861/1628303360)], [(-39424375/10176896)]], [[(-64205183/20353792)], [(40531129/5088448)], [(-118273125/20353792)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-3785279667251236203828075717736193/577395105173075400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 117521798725109006919168000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨967117032225525942342146832697360936653477, 0, 3, 0, 3, 0, 0⟩,
  ⟨3384430694348842776540536880771412311704181, 0, 3, 1, 2, 0, 0⟩,
  ⟨4506669509005940433315037399983924159151056, 0, 3, 2, 1, 0, 0⟩,
  ⟨1394003855518753606234293836284872784100352, 0, 3, 3, 0, 0, 0⟩,
  ⟨3440059653635887737575509340497491857798639, 1, 2, 0, 3, 0, 0⟩,
  ⟨10870492729305107869852126614897964078627167, 1, 2, 1, 2, 0, 0⟩,
  ⟨13076151510192307623687226401496749620967792, 1, 2, 2, 1, 0, 0⟩,
  ⟨3525872977475176924874124752096277400139264, 1, 2, 3, 0, 0, 0⟩,
  ⟨4070280756549058728975734311693900905636847, 2, 1, 0, 3, 0, 0⟩,
  ⟨11815484827282599571099023307104691222141791, 2, 1, 1, 2, 0, 0⟩,
  ⟨12797931754714961958831056390289726764482416, 2, 1, 2, 1, 0, 0⟩,
  ⟨2899092743977209962281859191753936447977472, 2, 1, 3, 0, 0, 0⟩,
  ⟨1600562463208519024456206097141769984491685, 3, 0, 0, 3, 0, 0⟩,
  ⟨4339095776535800749928936452722139455218805, 3, 0, 1, 2, 0, 0⟩,
  ⟨4238122737738061040600370268520901302665680, 3, 0, 2, 1, 0, 0⟩,
  ⟨770447950090608734355862569190531831938560, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(3785279667251236203828075717736193/577395105173075400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3785279667251236203828075717736193/577395105173075400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardRightLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-17766391642285413927111194132096021186824473887119982126559315794964677289/565096618596266793016980512000000000000000000000000)], [(3886047468131445379000312578196296956674433855682441649743116247721287/45207729487701343441358440960000000000000000000)], [(-16119920724534344743834037552784249779216493821233331700389025732747/289329468721288598024694022144000000000000000)]], [[(158911162886009819409190778899958644331684872993101124196662040860408903/141274154649066698254245128000000000000000000000)], [(-186279164459333287183623051027704234952990566643/53789354775948800000000)], [(1110482824790162696258982751571073446463517311/344251870566072320000)], [(-13876619678266407912161964215966555438145/17212593528303616)]], [[(-8479080573489899829993520567061217243607685781/13447338693987200000000)], [(1783271967734917406599525168536991132228179/1075787095518976000)], [(-41629859034799223736485892647899666314435/34425187056607232)]], [[(3498116332725399241815061395769916844657/33618346734968000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 36166183590161074753086752768000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨176485165794773078422359722934030779915363067503303141805599871453361842873, 0, 3, 0, 3, 0, 0⟩,
  ⟨377077224979729304200083047996242194244297865307148298058399334252413447369, 0, 3, 1, 2, 0, 0⟩,
  ⟨265632671247949296105736679044574456952977925888219006008825957010469881744, 0, 3, 2, 1, 0, 0⟩,
  ⟨20508135589697924945165993076065623604989226120475227988448369211418277248, 0, 3, 3, 0, 0, 0⟩,
  ⟨597402181602494481173830129060700358886285980383840824786925522120143337003, 1, 2, 0, 3, 0, 0⟩,
  ⟨1268593862010662819447519295109298541284471658050854998458106883537413767259, 1, 2, 1, 2, 0, 0⟩,
  ⟨850994556236460644585048375382650939374564361469802892606635878061583070384, 1, 2, 2, 1, 0, 0⟩,
  ⟨44041464175689203251630170458588502575580087534330516513579516644312640128, 1, 2, 3, 0, 0, 0⟩,
  ⟨672563618183674423956173026024000668203824297228676562589260348720201145387, 2, 1, 0, 3, 0, 0⟩,
  ⟨1424606536885280263744129882857054796909437480701063632389644770837587192411, 2, 1, 1, 2, 0, 0⟩,
  ⟨919761041348225129013290524764473400716247427392029185461097016611756495536, 2, 1, 2, 1, 0, 0⟩,
  ⟨29792728761298519254417672899383020266198757274421576119696969494370448512, 2, 1, 3, 0, 0, 0⟩,
  ⟨251853098245231980026389980859302249353039870390047982898657002053419651257, 3, 0, 0, 3, 0, 0⟩,
  ⟨533709387462183624961755718629911930229679146083084241862104133552586872521, 3, 0, 1, 2, 0, 0⟩,
  ⟨335018643967550656999040911312310398655076449936172608735454007560643306896, 3, 0, 2, 1, 0, 0⟩,
  ⟨6465896044586199769640856478831301415746381902475390885288126061476085632, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(50514812848329685700319191240869542310518608613088991291313484855281919/282548309298133396508490256000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(3498116332725399241815061395769916844657/16809173367484000)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-3498116332725399241815061395769916844657/33618346734968000)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 33618346734968000
def dCertificate : TensorBernstein3 := [
  ⟨3498116332725399241815061395769916844657, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(3498116332725399241815061395769916844657/33618346734968000) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3498116332725399241815061395769916844657/33618346734968000) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-42242454576356207684825680169252282622441404626429881801085314189160813789/14066963816967070501821515770668301730852415000000000000000000000000000000)], [(41846706260670808950344743062278771190091/4623571857594012922324800000000000000000)], [(-39942732574815753314702066481326342103/6575746641911485045084160000000000000)]], [[(6488674005484913483571998291689192004391207202168044323424925254943246421696475673/349471167392896459252094664523549363748768780796375750000000000000000000000000000)], [(-1048803767555663421957004441296851958928681/19351654982649691481371269250000000000000)], [(346771025294939/7823997644800)], [(-78220125/10176896)]], [[(-4043844465283093820894812770950052416472118831/334744927889874363244760215486500000000000000)], [(3398072476087/110024966880)], [(-402807570375/19559994112)]], [[(1329399613/1496104020)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-26085916593557311846543779178794464709511371603641559142171067627309048573939/351638137414714638210064185064006302588470228580000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 698942334785792918504189329047098727497537561592751500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨23582096455056717240548434093106857468326538262079097913497233133958552287661549793929, 0, 4, 0, 3, 0, 0⟩,
  ⟨52672379672341150642386149372405154830264105466768975317065844720904701464058868131787, 0, 4, 1, 2, 0, 0⟩,
  ⟨36427892647372445600351006104017762126346673822509601998754050427045480836861602506787, 0, 4, 2, 1, 0, 0⟩,
  ⟨921259209776391637304889161694850535063789658522413257947127072521206660464284168929, 0, 4, 3, 0, 0, 0⟩,
  ⟨103479567408805516918095454928707178325074431476397314095673541679279241794589275589988, 1, 3, 0, 3, 0, 0⟩,
  ⟨231165643204345836776573053791200622638793930510148149803789014154413474910623295519964, 1, 3, 1, 2, 0, 0⟩,
  ⟨156682649933181393651636797325582014547473103206866776811290927126431812480691654894964, 1, 3, 2, 1, 0, 0⟩,
  ⟨2707589347515201314755465818164191728865630339882455777713113342703829364657634964988, 1, 3, 3, 0, 0, 0⟩,
  ⟨170215995954381139281542619884719362786501327436799817805466081673284925689657949750014, 2, 2, 0, 3, 0, 0⟩,
  ⟨380467419470235697519383850637023815030881807527406546834471077982828896543094943000042, 2, 2, 1, 2, 0, 0⟩,
  ⟨253299407359174855007145631541301769076146178863891524263550364024909590266483614875042, 2, 2, 2, 1, 0, 0⟩,
  ⟨2663979779123517260886026650960495196802032720001403496992724893099994413046621625014, 2, 2, 3, 0, 0, 0⟩,
  ⟨124396701180606215097287336946276844747769762465796319745799914858265865994194271905780, 3, 1, 0, 3, 0, 0⟩,
  ⟨278327796720675001272644211873278066055944711217873238501432517884166016754555471967340, 3, 1, 1, 2, 0, 0⟩,
  ⟨182425755145808256631715096008351878180171462746651617568002757714726133982338675092340, 3, 1, 2, 1, 0, 0⟩,
  ⟨928204966477046629899064087951692199351835550519125964698645899763483221977475030780, 3, 1, 3, 0, 0, 0⟩,
  ⟨34079471179146635476652702709976474909306162746989221371106149330301629811464047951825, 4, 0, 0, 3, 0, 0⟩,
  ⟨76357525779962269837530160093505735107462232244869375899472632134845893658024956355475, 4, 0, 1, 2, 0, 0⟩,
  ⟨49384990069960629625938150127070377799021216778140777862777293189202875359685112605475, 4, 0, 2, 1, 0, 0⟩,
  ⟨51850324265099029824578906279210287641478015552268236067914876846111513124204201825, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(26085916593557311846543779178794464709511371603641559142171067627309048573939/351638137414714638210064185064006302588470228580000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(26085916593557311846543779178794464709511371603641559142171067627309048573939/351638137414714638210064185064006302588470228580000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-15547289469855765011444288323214691469830907/7705953095990021537208000000000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(8650342982576524150725048479104779816097269163/781084075006781571785632239000000000000000000)], [(-34586695074649531/1100249668800000)], [(118198340979913/4694398586880)], [(-43455625/10176896)]], [[(-1204700531743903/183374944800000)], [(374950125023/22004993376)], [(-671345950625/58679982336)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-50337269951568302333099211559198192858607/117889102847313807104124000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1199745139210416494262731119104000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨30519317107237036819436856908330915097582700891013, 0, 3, 0, 3, 0, 0⟩,
  ⟨61054386856331148736502661806466923018233510716789, 0, 3, 1, 2, 0, 0⟩,
  ⟨40925837735951649683434578695381679217235389463664, 0, 3, 2, 1, 0, 0⟩,
  ⟨2566270501844074039782418084267155671584579637888, 0, 3, 3, 0, 0, 0⟩,
  ⟨102807722728950845160555446876403712756383509179023, 1, 2, 0, 3, 0, 0⟩,
  ⟨206401206182841733867916230449759792853106751668319, 1, 2, 1, 2, 0, 0⟩,
  ⟨132709288574791024745329132675892666451362387908944, 1, 2, 2, 1, 0, 0⟩,
  ⟨5262094117994640482748563911052211354639145419648, 1, 2, 3, 0, 0, 0⟩,
  ⟨115362777240314223312737416184029479091658915685007, 2, 1, 0, 3, 0, 0⟩,
  ⟨232909319720239923738703650432885250516432971186271, 2, 1, 1, 2, 0, 0⟩,
  ⟨144955656600428525462416799062410250740938607426896, 2, 1, 2, 1, 0, 0⟩,
  ⟨3175184569732225105770061569521276191164551925632, 2, 1, 3, 0, 0, 0⟩,
  ⟨43107287826239791958555418506940418776858107396997, 3, 0, 0, 3, 0, 0⟩,
  ⟨87661249016647469568099858662543592713559730234741, 3, 0, 1, 2, 0, 0⟩,
  ⟨53270954384507281361332021954850475538811608981616, 3, 0, 2, 1, 0, 0⟩,
  ⟨512277161221035649740508033719957852109986143872, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(50337269951568302333099211559198192858607/117889102847313807104124000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(50337269951568302333099211559198192858607/117889102847313807104124000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-14398190726384118151062388417618935424177/7397714972150420675719680000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(14235553745142617039661976450543749078424913/1323497444236286199015474000000000000000000)], [(-34289044531749067/1100249668800000)], [(118198340979913/4694398586880)], [(-43455625/10176896)]], [[(-1161603095317/176039947008)], [(374950125023/22004993376)], [(-671345950625/58679982336)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-3785279667251236203828075717736193/577395105173075400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 338815345724489266947961344000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2953286801561216689783576817289282290782755441, 0, 3, 0, 3, 0, 0⟩,
  ⟨9205204916835753784557660297922486297788935073, 0, 3, 1, 2, 0, 0⟩,
  ⟨12480517049716595898166122425095617243567494448, 0, 3, 2, 1, 0, 0⟩,
  ⟨4018913115460566646773469130009288236561314816, 0, 3, 3, 0, 0, 0⟩,
  ⟨10397977126678613800287188180850578657265819987, 1, 2, 0, 3, 0, 0⟩,
  ⟨29696902191712261252805391545265031748119466211, 1, 2, 1, 2, 0, 0⟩,
  ⟨36200450353278568845828860571583020835455144336, 1, 2, 2, 1, 0, 0⟩,
  ⟨10165091794060935074412101660293567744601498112, 1, 2, 3, 0, 0, 0⟩,
  ⟨12290566030985045973918270745281513442183373651, 2, 1, 0, 3, 0, 0⟩,
  ⟨32659233576400373586084341341379463602872127203, 2, 1, 1, 2, 0, 0⟩,
  ⟨35570561457725120101366072296315173940207805328, 2, 1, 2, 1, 0, 0⟩,
  ⟨8358084380886296321258600049826598779519051776, 2, 1, 3, 0, 0, 0⟩,
  ⟨4855171443692945950942643649154201075700309105, 3, 0, 0, 3, 0, 0⟩,
  ⟨12195423514999757380420562896338870152541596065, 3, 0, 1, 2, 0, 0⟩,
  ⟨11878515367639038416287286952129722348320155440, 3, 0, 2, 1, 0, 0⟩,
  ⟨2221201440111224981147951786976303271478868480, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(3785279667251236203828075717736193/577395105173075400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3785279667251236203828075717736193/577395105173075400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardRightLeaf000
