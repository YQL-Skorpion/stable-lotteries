import OptimalG.Certificates.ScaledTensorReconstruction
import OptimalG.Certificates.StaticHighMassTailModelBatch10
import OptimalG.Certificates.StaticHighMassTailModelBatch11


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-682135373961459664533260718447260846677428971104421977650425537656295266342937/22603864743850671720679220480000000000000000000000)], [(72160443623249265892913455269153796528705074364653256047636571989199184123/904154589754026868827168819200000000000000000)], [(-585794647824073463078033116602309297272133898992822591809772026820437151/11573178748851543920987760885760000000000000)]], [[(936549731831415837215228630732924615924011239348968145561322850613058867349/5650966185962667930169805120000000000000000000)], [(-506899046362289802875186547839781998957718124819747/1075787095518976000000)], [(5200442062747676760156250282651960839795009173763/13770074822642892800)], [(-1102426184842088323100531338618676215185907125/17212593528303616)]], [[(-53022341284790066218244856255475787630068578096773/537893547759488000000)], [(5498967203308667631135818983604593324053042791/21515741910379520)], [(-5907520683186063997079468834658317325149871375/34425187056607232)]], [[(10085069387247326014152822004004670263146131/1344733869398720)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1446647343606442990123470110720000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨520914043186065124683566425210360889957890115826184913243373805757426726909109, 0, 3, 0, 3, 0, 0⟩,
  ⟨1056358525546035725109296788842804098179987724796307822286434959068288657671077, 0, 3, 1, 2, 0, 0⟩,
  ⟨737619043874989831311024045906062760893259801413997176750310513324380824067952, 0, 3, 2, 1, 0, 0⟩,
  ⟨60659497246404618655184213939360176158674236147247550928177094388518893305984, 0, 3, 3, 0, 0, 0⟩,
  ⟨1757673051909893151844496327799746463133349105139435283559052305032026842298399, 1, 2, 0, 3, 0, 0⟩,
  ⟨3565961618228959444425747291950126837796478265834680803569876385931605957726447, 1, 2, 1, 2, 0, 0⟩,
  ⟨2371285618469905555827265875061734138126188349911830979969649540241132456917072, 1, 2, 2, 1, 0, 0⟩,
  ⟨131575168242428476089261749135299602841868284087227285021091084341553341489024, 1, 2, 3, 0, 0, 0⟩,
  ⟨1976139981388475907437608027030505205326898773365054387767619732653493503869471, 2, 1, 0, 3, 0, 0⟩,
  ⟨4021775979734970457749861640978128082338539756067147724632129163493505942439663, 2, 1, 1, 2, 0, 0⟩,
  ⟨2571361552717601419984188339366937299449500238535004408993328192969282441630288, 2, 1, 2, 1, 0, 0⟩,
  ⟨87426979360129132048756806869984230732941314464074872590566809004270003060096, 2, 1, 3, 0, 0, 0⟩,
  ⟨739976300255779118559602786094482486777799039310627962239093635810893388480181, 3, 0, 0, 3, 0, 0⟩,
  ⟨1513958869825440453282185122830893906601126980805246577710144943926188642384293, 3, 0, 1, 2, 0, 0⟩,
  ⟨939480960896079410316720495171354486095649455813642440135446373348530808781168, 3, 0, 2, 1, 0, 0⟩,
  ⟨17106635955236512897603933327407658676106521782919083284805221483235554877056, 3, 0, 3, 0, 0, 0⟩]
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
  have he : nReduced.eval p z dummy=n p z dummy-(133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(10085069387247326014152822004004670263146131/672366934699360)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-10085069387247326014152822004004670263146131/1344733869398720)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1344733869398720
def dCertificate : TensorBernstein3 := [
  ⟨10085069387247326014152822004004670263146131, 0, 0, 0, 0, 0, 0⟩]
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
  have he : dReduced.eval p z dummy=d p z dummy-(10085069387247326014152822004004670263146131/1344733869398720) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10085069387247326014152822004004670263146131/1344733869398720) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighCapMaxLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-35042990342848522461373323593071938698363800575790803515874435282910813789/14066963816967070501821515770668301730852415000000000000000000000000000000)], [(73750053887158160962879085854928709925157/9247143715188025844649600000000000000000)], [(-36237363230979920656676949928455526953/6575746641911485045084160000000000000)]], [[(5474546541529662666925469684896172559781648415272624209727464317443246421696475673/349471167392896459252094664523549363748768780796375750000000000000000000000000000)], [(-918223107951025946636930044037153912053681/19351654982649691481371269250000000000000)], [(311102219493989/7823997644800)], [(-70963875/10176896)]], [[(-3463013158267425651300936030670032885222118831/334744927889874363244760215486500000000000000)], [(5993944426649/220049933760)], [(-365440301625/19559994112)]], [[(1329399613/1496104020)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-26085916593557311846543779178794464709511371603641559142171067627309048573939/351638137414714638210064185064006302588470228580000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 698942334785792918504189329047098727497537561592751500000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨23102722886395738832608182205333290668339139546494885706706454114409170634829518543929, 0, 4, 0, 3, 0, 0⟩,
  ⟨54275559287061294483665747462443607968833109210198770924960193387864173326851836881787, 0, 4, 1, 2, 0, 0⟩,
  ⟨37915219969299930480706149402221147368887351988243573308884429578398084352486602506787, 0, 4, 2, 1, 0, 0⟩,
  ⟨921259209776391637304889161694850535063789658522413257947127072521206660464284168929, 0, 4, 3, 0, 0, 0⟩,
  ⟨101582276910615547616970899216098980297361640232999488070707260192300762973788494339988, 1, 3, 0, 3, 0, 0⟩,
  ⟨237616780556935235991487063544665993038135830608735138621952743530779583980447514269964, 1, 3, 1, 2, 0, 0⟩,
  ⟨162592326300460181438976487853719437749419890922676096819902505372588900371316654894964, 1, 3, 2, 1, 0, 0⟩,
  ⟨2707589347515201314755465818164191728865630339882455777713113342703829364657634964988, 1, 3, 3, 0, 0, 0⟩,
  ⟨167408749443455686382323809474235302728176944293087852418694433229059841644247793500014, 2, 2, 0, 3, 0, 0⟩,
  ⟨390188815774886248380845792197374962275668291629526825349936214857240705075809786750042, 2, 2, 1, 2, 0, 0⟩,
  ⟨262081745377988799370606539803895271485680040169128076055916238699015232844608614875042, 2, 2, 2, 1, 0, 0⟩,
  ⟨2663979779123517260886026650960495196802032720001403496992724893099994413046621625014, 2, 2, 3, 0, 0, 0⟩,
  ⟨122556890051753362034385217366654778386177488284445012179841049965834857754448178155780, 3, 1, 0, 3, 0, 0⟩,
  ⟨284829360263585083375542990897148898641992474040121256594043561160010444061684378217340, 3, 1, 1, 2, 0, 0⟩,
  ⟨188209871228734265713714105290735264231918301574465897492167148304876569529213675092340, 3, 1, 2, 1, 0, 0⟩,
  ⟨928204966477046629899064087951692199351835550519125964698645899763483221977475030780, 3, 1, 3, 0, 0, 0⟩,
  ⟨33628989631690244419785089716003837378312879181536265373743430414666608449159360451825, 4, 0, 0, 3, 0, 0⟩,
  ⟨77985650756091056452601409220452337709496407320154308686887919245685149639470268855475, 4, 0, 1, 2, 0, 0⟩,
  ⟨50809117179423997251460798376794299400640303850793854693057008200052152703435112605475, 4, 0, 2, 1, 0, 0⟩,
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
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighCapMax.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighCapMax.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighCapMaxLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardLeftLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-4452077509332428265780413990893439031558219/2568651031996673845736000000000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(7391108894632577821656280655006861847347269163/781084075006781571785632239000000000000000000)], [(-60924234795087137/2200499337600000)], [(106308739046263/4694398586880)], [(-39424375/10176896)]], [[(-342644196987551/61124981600000)], [(660766858321/44009986752)], [(-609067169375/58679982336)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-50337269951568302333099211559198192858607/117889102847313807104124000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1199745139210416494262731119104000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨29934739091140591885079312795707613192018124484763, 0, 3, 0, 3, 0, 0⟩,
  ⟨63009404028506858884781695167865158218494299310539, 0, 3, 1, 2, 0, 0⟩,
  ⟨42739577399502654727432861438446185073060754463664, 0, 3, 2, 1, 0, 0⟩,
  ⟨2566270501844074039782418084267155671584579637888, 0, 3, 3, 0, 0, 0⟩,
  ⟨101107033029633521747988828458876580352189779960273, 1, 2, 0, 3, 0, 0⟩,
  ⟨212218107259123859398015353517865006016389117449569, 1, 2, 1, 2, 0, 0⟩,
  ⟨138014041024386353877107796618556262018838482908944, 1, 2, 2, 1, 0, 0⟩,
  ⟨5262094117994640482748563911052211354639145419648, 1, 2, 3, 0, 0, 0⟩,
  ⟨113722777737310792778203166637826751249965186466257, 2, 1, 0, 3, 0, 0⟩,
  ⟨238664632664656142421077595498907202492215336967521, 2, 1, 1, 2, 0, 0⟩,
  ⟨150102858970003385173465722781568524308414702426896, 2, 1, 2, 1, 0, 0⟩,
  ⟨3175184569732225105770061569521276191164551925632, 2, 1, 3, 0, 0, 0⟩,
  ⟨42583400006457239902230243265641521433793530990747, 3, 0, 0, 3, 0, 0⟩,
  ⟨89554678056957272868653714021858566726320518828491, 3, 0, 1, 2, 0, 0⟩,
  ⟨54927143968037816984600564474409659394636973981616, 3, 0, 2, 1, 0, 0⟩,
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
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardLeft.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardLeft.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardLeftLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardRightLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-12294776062199977145523463921105936024027/7397714972150420675719680000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(12101861418776144863888859550067186578424913/1323497444236286199015474000000000000000000)], [(-60328933709286209/2200499337600000)], [(106308739046263/4694398586880)], [(-39424375/10176896)]], [[(-991905872167/176039947008)], [(660766858321/44009986752)], [(-609067169375/58679982336)]], [[(1/2)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-3785279667251236203828075717736193/577395105173075400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 338815345724489266947961344000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2788198403906191291772409318666491580371974191, 0, 3, 0, 3, 0, 0⟩,
  ⟨9757313691807713724766367827263981694643153823, 0, 3, 1, 2, 0, 0⟩,
  ⟨12992728194464126269247252824153653350832494448, 0, 3, 2, 1, 0, 0⟩,
  ⟨4018913115460566646773469130009288236561314816, 0, 3, 3, 0, 0, 0⟩,
  ⟨9917691981432264347430193428654269026033476237, 1, 2, 0, 3, 0, 0⟩,
  ⟨31339630538586625988783681030750830438682122461, 1, 2, 1, 2, 0, 0⟩,
  ⟨37698544803884422879090273715515129157250144336, 1, 2, 2, 1, 0, 0⟩,
  ⟨10165091794060935074412101660293567744601498112, 1, 2, 3, 0, 0, 0⟩,
  ⟨11827420167386223456399420266263516310951029901, 2, 1, 0, 3, 0, 0⟩,
  ⟨34284569059149941132645749154432824793434783453, 2, 1, 1, 2, 0, 0⟩,
  ⟨37024162804682154755714822287605282262002805328, 2, 1, 2, 1, 0, 0⟩,
  ⟨8358084380886296321258600049826598779519051776, 2, 1, 3, 0, 0, 0⟩,
  ⟨4707222327685447488269620423709722865289527855, 3, 0, 0, 3, 0, 0⟩,
  ⟨12730139425846920131212388753247928049395814815, 3, 0, 1, 2, 0, 0⟩,
  ⟨12346233408737749408455754198545758455585155440, 3, 0, 2, 1, 0, 0⟩,
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
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardRight.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardRight.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardRightLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardKinkLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-585734150493758517287728981924392449295713487975652404936976392892883164624187/22603864743850671720679220480000000000000000000000)], [(128117783191657206837171006684927763306064147619042858252937452142180470421/1808309179508053737654337638400000000000000000)], [(-531452208288551970796347581040387006322957819249065228448109561187509601/11573178748851543920987760885760000000000000)]], [[(799901524153467120696765691554232702691430692009881318850604467800558867349/5650966185962667930169805120000000000000000000)], [(-892817109600419004079161401006659811795406493471769/2151574191037952000000)], [(4677328239893028067588896491075879850111917447613/13770074822642892800)], [(-1000157363311051350269073570865789483204300875/17212593528303616)]], [[(-45244978024333417186147953824598133712217754503023/537893547759488000000)], [(9690716285846277588197993016055681270862621257/43031483820759040)], [(-5359497435238443395874754629311682874097552625/34425187056607232)]], [[(10085069387247326014152822004004670263146131/1344733869398720)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1446647343606442990123470110720000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨510341275327636286129933737119873721801482020853940426463024875352042193002859, 0, 3, 0, 3, 0, 0⟩,
  ⟨1091717266640476087123651395076355195922781637406260949214806618505707968764827, 0, 3, 1, 2, 0, 0⟩,
  ⟨770422618231754323787650813388697109311906252061487800235886571917184669067952, 0, 3, 2, 1, 0, 0⟩,
  ⟨60659497246404618655184213939360176158674236147247550928177094388518893305984, 0, 3, 3, 0, 0, 0⟩,
  ⟨1726914116583908092338964229785188084585633373172365503773147618128373240579649, 1, 2, 0, 3, 0, 0⟩,
  ⟨3671166985248490417811634030909674544272544465337872178292046158806363891007697, 1, 2, 1, 2, 0, 0⟩,
  ⟨2467228186701465547683130369337749507966281729294698957122255250019543991917072, 1, 2, 2, 1, 0, 0⟩,
  ⟨131575168242428476089261749135299602841868284087227285021091084341553341489024, 1, 2, 3, 0, 0, 0⟩,
  ⟨1946478698282110752351221967054339452309712322189694493186685481312339902150721, 2, 1, 0, 3, 0, 0⟩,
  ⟨4125867454334460258103150212115675831005955390555345398946865862180763875720913, 2, 1, 1, 2, 0, 0⟩,
  ⟨2664454645983858417626835865608681123208391890827896593847495236747693976630288, 2, 1, 2, 1, 0, 0⟩,
  ⟨87426979360129132048756806869984230732941314464074872590566809004270003060096, 2, 1, 3, 0, 0, 0⟩,
  ⟨730501184616970184425116136042387944151920225130093360663715140968008854573931, 3, 0, 0, 3, 0, 0⟩,
  ⟨1548203718499839642263941561242445046535270328400206004231083529176107953478043, 3, 0, 1, 2, 0, 0⟩,
  ⟨969435060287540908580130294619717288433094179371157271322583765941334653781168, 3, 0, 2, 1, 0, 0⟩,
  ⟨17106635955236512897603933327407658676106521782919083284805221483235554877056, 3, 0, 3, 0, 0, 0⟩]
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
  have he : nReduced.eval p z dummy=n p z dummy-(133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(133645593400285257012530729120372333407082201429055338162540792837777772477/11301932371925335860339610240000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[(10085069387247326014152822004004670263146131/672366934699360)]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-10085069387247326014152822004004670263146131/1344733869398720)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1344733869398720
def dCertificate : TensorBernstein3 := [
  ⟨10085069387247326014152822004004670263146131, 0, 0, 0, 0, 0, 0⟩]
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
  have he : dReduced.eval p z dummy=d p z dummy-(10085069387247326014152822004004670263146131/1344733869398720) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10085069387247326014152822004004670263146131/1344733869398720) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardKink.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardKink.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardKinkLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf001
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(43788721965159355955426972315692967/6682234734642751940000000000000000), (-56233/100000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-30049621545625615932868176893448603856403949818057/41233329856407017507263833144729600000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(179/250), (391/500)⟩, ⟨(97/100), (197/200)⟩, ⟨(1/20), (527/2000)⟩]
def nScale : ℚ := 206166649282035087536319165723648000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨1120554489822165054030827795070096828159073169540155, 0, 3, 0, 3, 0, 1⟩,
  ⟨1172262216332759596198631339600193828745844480186427, 0, 3, 0, 3, 1, 0⟩,
  ⟨2425481972467987017847641536056105574194449717800745, 0, 3, 1, 2, 0, 1⟩,
  ⟨2904071833106225261831542807631603983660577166519081, 0, 3, 1, 2, 1, 0⟩,
  ⟨1457302925329203058339121400439741582817396297350875, 0, 3, 2, 1, 0, 1⟩,
  ⟨2259359467073895919803513310000447399989337262848731, 0, 3, 2, 1, 1, 0⟩,
  ⟨150248107728128079664340884467243019282019749090285, 0, 3, 3, 0, 0, 1⟩,
  ⟨525422515345177239312635066982547427574604576516077, 0, 3, 3, 0, 1, 0⟩,
  ⟨4697136757898975040809803393565030486194319427959985, 1, 2, 0, 3, 0, 1⟩,
  ⟨4380329529488294671103365993670178991625045710583985, 1, 2, 0, 3, 1, 0⟩,
  ⟨10920609144892986421092282979862504230518601629142395, 1, 2, 1, 2, 0, 1⟩,
  ⟨10970404264087887383344208590931091088515628418564475, 1, 2, 1, 2, 1, 0⟩,
  ⟨7638087274194052130835826697891698877626631530787985, 1, 2, 2, 1, 0, 1⟩,
  ⟨8688099197815895164458990119713427077328506261760145, 1, 2, 2, 1, 1, 0⟩,
  ⟨1408036787212708104051198452627621144552349329605575, 1, 2, 3, 0, 0, 1⟩,
  ⟨2091446363228969805715998863485910991687923553779655, 1, 2, 3, 0, 1, 0⟩,
  ⟨6192712871632871565740541855114649736713384216661169, 2, 1, 0, 3, 0, 1⟩,
  ⟨5368649596822477198342937496844565114973930328639665, 2, 1, 0, 3, 1, 0⟩,
  ⟨15016221149760703511513029267692883001467659194559867, 2, 1, 1, 2, 0, 1⟩,
  ⟨13574064890864040699621219900433289596541552863256955, 2, 1, 1, 2, 1, 0⟩,
  ⟨11325560623451242821030370662704829847172789740792977, 2, 1, 2, 1, 0, 1⟩,
  ⟨10913437930089100299439565002995896902538938742251665, 2, 1, 2, 1, 1, 0⟩,
  ⟨2495278150214504626827486257152858057418514762894279, 2, 1, 3, 0, 0, 1⟩,
  ⟨2701248440938630549730885606433433895971316207634375, 2, 1, 3, 0, 1, 0⟩,
  ⟨2625488456364688545194985269136127293588734898738235, 3, 0, 0, 3, 0, 1⟩,
  ⟨2169940136475569089671621855290991167005326038739003, 3, 0, 0, 3, 1, 0⟩,
  ⟨6549167535761585006968644861435717989875298104708905, 3, 0, 1, 2, 0, 1⟩,
  ⟨5535806018308259476808811154683036136418292432702249, 3, 0, 1, 2, 1, 0⟩,
  ⟨5172849833012274647233922402802106197095345328846555, 3, 0, 2, 1, 0, 1⟩,
  ⟨4512771757772981953484345230832150869931560564830939, 3, 0, 2, 1, 1, 0⟩,
  ⟨1246847323538551568674047701508891147058782122875885, 3, 0, 3, 0, 0, 1⟩,
  ⟨1144582445863464949560940822446481546768594170867693, 3, 0, 3, 0, 1, 0⟩]
noncomputable def n (p z r : ℝ) : ℝ := nPolynomial.eval p z r

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z r : ℝ}
    (hp : p∈Icc (179/250) (391/500))
    (hz : z∈Icc (97/100) (197/200))
    (hr : r∈Icc (1/20) (527/2000))
    : 0<n p z r := by
  have hx : ∀ i,(nBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, r] hx
  have he : nReduced.eval p z r=n p z r-(30049621545625615932868176893448603856403949818057/41233329856407017507263833144729600000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(30049621545625615932868176893448603856403949818057/41233329856407017507263833144729600000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(179/250), (391/500)⟩, ⟨(97/100), (197/200)⟩, ⟨(1/20), (527/2000)⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z r : ℝ) : ℝ := dPolynomial.eval p z r

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z r : ℝ}
    (hp : p∈Icc (179/250) (391/500))
    (hz : z∈Icc (97/100) (197/200))
    (hr : r∈Icc (1/20) (527/2000))
    : 0<d p z r := by
  have hx : ∀ i,(dBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, r] hx
  have he : dReduced.eval p z r=d p z r-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (179/250:ℝ) (391/500))
    (hz : z∈Icc (97/100:ℝ) (197/200))
    (hr : r∈Icc (1/20:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.numerator p z r := by
  exact n_pos hp hz hr

theorem denominator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (179/250:ℝ) (391/500))
    (hz : z∈Icc (97/100:ℝ) (197/200))
    (hr : r∈Icc (1/20:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.denominator p z r := by
  exact d_pos hp hz hr

end OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf001
namespace OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf004
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(43788721965159355955426972315692967/6682234734642751940000000000000000), (-56233/100000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-234838107829986701858893628912010074232527694828991/274888865709380116715092220964864000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(749/1000), (391/500)⟩, ⟨(197/200), (397/400)⟩, ⟨(627/4000), (527/2000)⟩]
def nScale : ℚ := 824666597128140350145276662894592000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2837255640940085943965066064909188662009022030190123, 0, 3, 0, 3, 0, 1⟩,
  ⟨3127827990110673485240912830807128785431715166273067, 0, 3, 0, 3, 1, 0⟩,
  ⟨6426999597004227678893566461969398853082292051860569, 0, 3, 1, 2, 0, 1⟩,
  ⟨7637091706176234029666480346047186190349888672494681, 0, 3, 1, 2, 1, 0⟩,
  ⟨4295370970812121748416226754791268956583353106157419, 0, 3, 2, 1, 0, 1⟩,
  ⟨5843838141644371826134514225253023260850466939176811, 0, 3, 2, 1, 1, 0⟩,
  ⟨704514323489960105576680886736030222697583084486973, 0, 3, 3, 0, 0, 1⟩,
  ⟨1333461734320791373797901239017937313119793432955197, 0, 3, 3, 0, 1, 0⟩,
  ⟨10222847142744655548036501260974942625542519588459137, 1, 2, 0, 3, 0, 1⟩,
  ⟨10617124904964282393102640497091048987227826217273985, 1, 2, 0, 3, 1, 0⟩,
  ⟨24003398571087864172703810981811665806139278434714891, 1, 2, 1, 2, 0, 1⟩,
  ⟨26216265423281264998203232397710645351487453653921035, 1, 2, 1, 2, 1, 0⟩,
  ⟨17188866510492897008051255143328529230216122105709121, 1, 2, 2, 1, 0, 1⟩,
  ⟨20431766928220818123851680266778169235856552657676865, 1, 2, 2, 1, 1, 0⟩,
  ⟨3404927984595235259168746926004936787119363259453367, 1, 2, 3, 0, 0, 1⟩,
  ⟨4829239312349382394535889869671703609096925221029815, 1, 2, 3, 0, 1, 0⟩,
  ⟨12060250221626841370505385388851235598163447587381889, 2, 1, 0, 3, 0, 1⟩,
  ⟨11959425879325707436069464100944582635845685176097409, 2, 1, 0, 3, 1, 0⟩,
  ⟨29089042850971244747098793036430572871402059457746187, 2, 1, 1, 2, 0, 1⟩,
  ⟨29831511770156152343556915828660034004034731252260107, 2, 1, 1, 2, 1, 0⟩,
  ⟨21838816974341866885433218003715606243294018877640257, 2, 1, 2, 1, 0, 1⟩,
  ⟨23626227839615083881657227451894487395512649700521537, 2, 1, 2, 1, 1, 0⟩,
  ⟨4806588223662616984142549776147616073492907007275959, 2, 1, 3, 0, 0, 1⟩,
  ⟨5750705827449792449472515144190383130761103624358839, 2, 1, 3, 0, 1, 0⟩,
  ⟨4679337646226585249550659699043687242085248499361323, 3, 0, 0, 3, 0, 1⟩,
  ⟨4474807890876412011324445940918868041504872595344939, 3, 0, 0, 3, 1, 0⟩,
  ⟨11526680656100548702638677035362922740710968485637209, 3, 0, 1, 2, 0, 1⟩,
  ⟨11266374832264061824370292295771191665263061681579097, 3, 0, 1, 2, 1, 0⟩,
  ⟨8959358213874032075148318133952962792027145288833899, 3, 0, 2, 1, 0, 1⟩,
  ⟨9052335832251578033290189929143958242872459392766827, 3, 0, 2, 1, 1, 0⟩,
  ⟨2110853488961655313667193243136915116526425302558013, 3, 0, 3, 0, 0, 1⟩,
  ⟨2259607175825514911851236019794822442239270306532669, 3, 0, 3, 0, 1, 0⟩]
noncomputable def n (p z r : ℝ) : ℝ := nPolynomial.eval p z r

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z r : ℝ}
    (hp : p∈Icc (749/1000) (391/500))
    (hz : z∈Icc (197/200) (397/400))
    (hr : r∈Icc (627/4000) (527/2000))
    : 0<n p z r := by
  have hx : ∀ i,(nBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, r] hx
  have he : nReduced.eval p z r=n p z r-(234838107829986701858893628912010074232527694828991/274888865709380116715092220964864000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(234838107829986701858893628912010074232527694828991/274888865709380116715092220964864000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(749/1000), (391/500)⟩, ⟨(197/200), (397/400)⟩, ⟨(627/4000), (527/2000)⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z r : ℝ) : ℝ := dPolynomial.eval p z r

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z r : ℝ}
    (hp : p∈Icc (749/1000) (391/500))
    (hz : z∈Icc (197/200) (397/400))
    (hr : r∈Icc (627/4000) (527/2000))
    : 0<d p z r := by
  have hx : ∀ i,(dBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, r] hx
  have he : dReduced.eval p z r=d p z r-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (749/1000:ℝ) (391/500))
    (hz : z∈Icc (197/200:ℝ) (397/400))
    (hr : r∈Icc (627/4000:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.numerator p z r := by
  exact n_pos hp hz hr

theorem denominator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (749/1000:ℝ) (391/500))
    (hz : z∈Icc (197/200:ℝ) (397/400))
    (hr : r∈Icc (627/4000:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.denominator p z r := by
  exact d_pos hp hz hr

end OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf004
namespace OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf007
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000), (1936100805801358073341014781/84045866837420000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(43788721965159355955426972315692967/6682234734642751940000000000000000), (-56233/100000)], [(-3557097867436876397904718518112950120400691/191019562086800180429019625500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-783188379524825216692658570393653942099309/191019562086800180429019625500000000000000), (-29159425505356880854446649382872771/158267997188523801498756937500000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-460809585991978552247859273491091552895048780786937/659733277702512280116221330315673600000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(1531/2000), (391/500)⟩, ⟨(397/400), (797/800)⟩, ⟨(1681/8000), (527/2000)⟩]
def nScale : ℚ := 3298666388512561400581106651578368000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨6813983881663684859120605455663749300078431243675915, 0, 3, 0, 3, 0, 1⟩,
  ⟨7600516388972688225896198315826086373923634726451467, 0, 3, 0, 3, 1, 0⟩,
  ⟨15987340745080064176693755042646626491228711936961465, 0, 3, 1, 2, 0, 1⟩,
  ⟨18692767518944212558698348683716984459410691445476281, 0, 3, 1, 2, 1, 0⟩,
  ⟨11477973394950380382888484210811295135547399597220235, 0, 3, 2, 1, 0, 1⟩,
  ⟨14529229420751667046570892912464999850375748165923211, 0, 3, 2, 1, 1, 0⟩,
  ⟨2304047929959892761239296367455457764475243903934685, 0, 3, 3, 0, 0, 1⟩,
  ⟨3436409689206034409692704288201141584966816446898397, 0, 3, 3, 0, 1, 0⟩,
  ⟨22772096788765316581947308751039915119455963587552033, 1, 2, 0, 3, 0, 1⟩,
  ⟨24651500586725355012236909755902926576282208691385121, 1, 2, 0, 3, 1, 0⟩,
  ⟨54514942110193048396109629444326221757037731699796779, 1, 2, 1, 2, 0, 1⟩,
  ⟨61198095450161473086744319114864676147102426039663403, 1, 2, 1, 2, 1, 0⟩,
  ⟨40544686538127859864241936555196963764797190361231009, 1, 2, 2, 1, 0, 1⟩,
  ⟨48272781824184593954642512881684838174447843729464993, 1, 2, 2, 1, 1, 0⟩,
  ⟨8800123156032704787730985571916330678934172248986263, 1, 2, 3, 0, 0, 1⟩,
  ⟨11724468900081052617786473232728762155346376381186711, 1, 2, 3, 0, 1, 0⟩,
  ⟨25210704137473763093372634247599201259496362760946465, 2, 1, 0, 3, 0, 1⟩,
  ⟨26601082801852517353254727945615690293903094389953313, 2, 1, 0, 3, 1, 0⟩,
  ⟨61385063004465278899170446984046993227562993159717675, 2, 1, 1, 2, 0, 1⟩,
  ⟨66608595133966745633315056208245260130015998922908459, 2, 1, 1, 2, 1, 0⟩,
  ⟨46964387426003125222568425149319100738637200122207905, 2, 1, 2, 1, 0, 1⟩,
  ⟨53240315691869795911211362503666167440323016761568929, 2, 1, 2, 1, 1, 0⟩,
  ⟨10788298242399087804301466602001536413773694723436695, 2, 1, 3, 0, 0, 1⟩,
  ⟨13231073043143046018681888430166825247413237228613783, 2, 1, 3, 0, 1, 0⟩,
  ⟨9254930693574288112104285705352138243846479652194571, 3, 0, 0, 3, 0, 1⟩,
  ⟨9552438067302007308472371258667952895272169660143883, 3, 0, 0, 3, 1, 0⟩,
  ⟨22864480028958764904429636841754706372936921102255033, 3, 0, 1, 2, 0, 1⟩,
  ⟨24110285592355955329944150036484876853507212034094009, 3, 0, 1, 2, 1, 0⟩,
  ⟨17904692672432115965890037064320740520570357063569803, 3, 0, 2, 1, 0, 1⟩,
  ⟨19503781678043339227814806793833637527433868903399819, 3, 0, 2, 1, 1, 0⟩,
  ⟨4294562479528432519368132150669766303042415613509341, 3, 0, 3, 0, 0, 1⟩,
  ⟨4945353295470184552146474238768307480761326529449693, 3, 0, 3, 0, 1, 0⟩]
noncomputable def n (p z r : ℝ) : ℝ := nPolynomial.eval p z r

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z r : ℝ}
    (hp : p∈Icc (1531/2000) (391/500))
    (hz : z∈Icc (397/400) (797/800))
    (hr : r∈Icc (1681/8000) (527/2000))
    : 0<n p z r := by
  have hx : ∀ i,(nBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, r] hx
  have he : nReduced.eval p z r=n p z r-(460809585991978552247859273491091552895048780786937/659733277702512280116221330315673600000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(460809585991978552247859273491091552895048780786937/659733277702512280116221330315673600000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(1531/2000), (391/500)⟩, ⟨(397/400), (797/800)⟩, ⟨(1681/8000), (527/2000)⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z r : ℝ) : ℝ := dPolynomial.eval p z r

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z r : ℝ}
    (hp : p∈Icc (1531/2000) (391/500))
    (hz : z∈Icc (397/400) (797/800))
    (hr : r∈Icc (1681/8000) (527/2000))
    : 0<d p z r := by
  have hx : ∀ i,(dBox i).Contains (![p, z, r] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hr
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, r] hx
  have he : dReduced.eval p z r=d p z r-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z r at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1531/2000:ℝ) (391/500))
    (hz : z∈Icc (397/400:ℝ) (797/800))
    (hr : r∈Icc (1681/8000:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.numerator p z r := by
  exact n_pos hp hz hr

theorem denominator_pos {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1531/2000:ℝ) (391/500))
    (hz : z∈Icc (397/400:ℝ) (797/800))
    (hr : r∈Icc (1681/8000:ℝ) (527/2000))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head.denominator p z r := by
  exact d_pos hp hz hr

end OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf007
