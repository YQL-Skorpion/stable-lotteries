import OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Parameters
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Batch0000
namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell0_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow,1,⟨1819663951560908899101764607325320827558132973568,1820556221576192863825674302505950041366580953088⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-519092784606947090870663355472421293454,519092784606947090870663355472421293454⟩,⟨11163654598267569393326580279642253739650599575354,11212204876866927724617042764642415840633775871787⟩,⟨617258630745224021060467875130549403344590643358,629070087178821771714557920155782494497283566067⟩,⟨32260491334788979636961216338270678940380397830144,32894364650871770456391526782244366409266060328960⟩⟩
theorem link0_1_checked : cell0_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert0 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.start)/500000)=true := by decide +kernel
def cell0_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow,2,⟨1819663951560908899101764607325320827558132973568,1820556221576192863825674302505950041366580953088⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-519092784606947090870663355472421293454,519092784606947090870663355472421293454⟩,⟨11156630304383626530028022191448909430789494946661,11214237399665790179310199416843781220767847240626⟩,⟨892056631333042885803262504588351877932525210199,903567853847871811328614326202866677219648486441⟩,⟨46622572531205604642044262636431093588148912914432,47247979231432640772936724973256209013470557896704⟩⟩
theorem link0_2_checked : cell0_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert0 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.start)/500000)=true := by decide +kernel
def cell1_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow,1,⟨1818773034445805367792049685123315601878724640768,1819664866787312346769834613316108416628432044032⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1038185569213894181741326710944842586908,1038185569213894181741326710944842586908⟩,⟨11167228459483376880390441283366880096460002728110,11215762248967106058577645980320687358387631691769⟩,⟨617995030691663300045169006137719766368600702115,629811755328595833165197564714761875606961245192⟩,⟨32283164685449152535807172924194332637418903044096,32917022770157384894997630890575918991308253822976⟩⟩
theorem link1_1_checked : cell1_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert1 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.start)/500000)=true := by decide +kernel
def cell1_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow,2,⟨1818773034445805367792049685123315601878724640768,1819664866787312346769834613316108416628432044032⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1038185569213894181741326710944842586908,1038185569213894181741326710944842586908⟩,⟨11161686777650773373757025043967874171851303965363,11219282434201118170463248925888317726165861792188⟩,⟨893499386696826925116948882888955091135273408034,905018799235037132207881143337928156048912489323⟩,⟨46675113114389436315220302616564368972821288714240,47300680013161347817219941955855603296046954840064⟩⟩
theorem link1_2_checked : cell1_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert1 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.start)/500000)=true := by decide +kernel
def cell2_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow,1,⟨1818230779886167157825813361967973801562401144832,1818773399737343873928003231568353760704727089152⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1354254662103785312770201769166710294731,1354254662103785312770201769166710294731⟩,⟨11179575683972631587322072974169898636654091393023,11209126636701082949251025553425026127097510398655⟩,⟨620894041159523379629575642832384394430484361298,628091199961636486558658071994118900777850150810⟩,⟨32424934513734260156023434790969344122690841083904,32811016079426964153202654070684366225304039981056⟩⟩
theorem link2_1_checked : cell2_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert2 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.start)/500000)=true := by decide +kernel
def cell2_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow,2,⟨1818230779886167157825813361967973801562401144832,1818773399737343873928003231568353760704727089152⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1354254662103785312770201769166710294731,1354254662103785312770201769166710294731⟩,⟨11177003421525089005719980225525309435088944628505,11212073867350979040967098079886252084403633313305⟩,⟨896908810193913914494578075505771208364551125923,903926656464736871544381660838142987125767375662⟩,⟨46839247370847225600793796322281701482508545163264,47220454469229017104511454179738107551041265336320⟩⟩
theorem link2_2_checked : cell2_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert2 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.start)/500000)=true := by decide +kernel
def cell3_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow,1,⟨1817688686891321870353269660554938994029257293824,1818231145182825919990460381603006572657832361984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1670323754993676443799076827388578002554,1670323754993676443799076827388578002554⟩,⟨11181741642610472057181198149956929018996268072836,11211303668707726421224657060400444814701309266632⟩,⟨621343521868369644956241712677692841123328177663,628543788091292644956396348061754921063225983216⟩,⟨32438733338168875138703356567823443897614503772160,32824869648612578226029741384522704349918757126144⟩⟩
theorem link3_1_checked : cell3_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert3 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.start)/500000)=true := by decide +kernel
def cell3_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow,2,⟨1817688686891321870353269660554938994029257293824,1818231145182825919990460381603006572657832361984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-1670323754993676443799076827388578002554,1670323754993676443799076827388578002554⟩,⟨11180081943025735407282957328854079622110489283239,11215166815651832363248309773250039444776121362171⟩,⟨897789678244317667864281687615823734943106012090,904812067929762798732718941379479285157714226366⟩,⟨46871270281435781920306727175367890367500875988992,47252615592235599419921585447762234864615982891008⟩⟩
theorem link3_2_checked : cell3_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert3 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.start)/500000)=true := by decide +kernel
def cell4_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow,1,⟨1816914321123188274031427841511332331101970497536,1817689390130028527288530587510097246808361140224⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2121983696410228471629953170477152710268,2121983696410228471629953170477152710268⟩,⟨11178037868540448188811500134027387811824122758460,11220306558821126839356290549359171657724047453547⟩,⟨620349164464419584104233416274524535555164761669,630642776410617022166052300261386059214162459359⟩,⟨32373023008217369190943775157041023772876613877760,32924673654991906242127298307087737925199334473728⟩⟩
theorem link4_1_checked : cell4_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert4 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.start)/500000)=true := by decide +kernel
def cell4_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow,2,⟨1816914321123188274031427841511332331101970497536,1817689390130028527288530587510097246808361140224⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2121983696410228471629953170477152710268,2121983696410228471629953170477152710268⟩,⟨11176309361172600048556556563798144910496419226417,11226474773619622325406876050823216127652780097703⟩,⟨897358030850613663478332076610553971052946851749,907400247597395921568956834304821870773086556215⟩,⟨46828776564283318874849166252609427493322099785728,47373660508016756327100447506065969947178885447680⟩⟩
theorem link4_2_checked : cell4_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert4 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.start)/500000)=true := by decide +kernel
def cell5_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow,1,⟨1816140284670472768793363786086417068341030027264,1816915024395825212506630876408732266513450401792⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2573643637826780499460829513565727417983,2573643637826780499460829513565727417983⟩,⟨11181122980753312934489472517555552498191893128508,11223420448569956898106734682312567660126190638504⟩,⟨620991407012299424472213109038715251186774680427,631291784956881442354585751952776810124215054216⟩,⟨32392732623274739736721731399364025204233346220032,32944516461028969611485673081709969729181211164672⟩⟩
theorem link5_1_checked : cell5_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert5 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.start)/500000)=true := by decide +kernel
def cell5_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow,2,⟨1816140284670472768793363786086417068341030027264,1816915024395825212506630876408732266513450401792⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2573643637826780499460829513565727417983,2573643637826780499460829513565727417983⟩,⟨11180709934429606818239615980906898220432864894885,11230911541230335534980161379350721950591482249235⟩,⟨898617612417980959971790847057182113095484953970,908669666075427159492432599345210793398055163025⟩,⟨46874529996250428354292241330113872768348937256960,47419724443351006739580690174291487214420352827392⟩⟩
theorem link5_2_checked : cell5_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert5 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.start)/500000)=true := by decide +kernel
def cell6_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow,1,⟨1815443703385514596425847459722307898671676522496,1816140862655467814583877405213409122444694781952⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2980271824696930828395901274326806551749,2980271824696930828395901274326806551749⟩,⟨11186157853697581971517520904976830680998585145798,11224263099043474609282738704932696065797173228913⟩,⟨622115201251243060536781813216972131353737753452,631393114805410075425637161246198604328386861823⟩,⟨32438906136269277993433151676970848922298862272512,32935765166346915454763466123221587282096314908672⟩⟩
theorem link6_1_checked : cell6_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert6 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.start)/500000)=true := by decide +kernel
def cell6_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow,2,⟨1815443703385514596425847459722307898671676522496,1816140862655467814583877405213409122444694781952⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-2980271824696930828395901274326806551749,2980271824696930828395901274326806551749⟩,⟨11187395839795432930831935534022099083683983531480,11232621845355370165502705447719703164853061771883⟩,⟨900316188892086331407703796158155830948086152116,909373356199250307751507065403386093111768055734⟩,⟨46945119838198182074725318318889972964950357835776,47436226773254686803609820122555224222554338099200⟩⟩
theorem link6_2_checked : cell6_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert6 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.start)/500000)=true := by decide +kernel
def cell7_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow,1,⟨1814747388513666548315098835164208823738837237760,1815444281392823780008031979690375289181638230016⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-3386900011567081157330973035087885685515,3386900011567081157330973035087885685515⟩,⟨11188935210457231242025711096746620526539576643523,11227063833205642765035286881555361039959323881178⟩,⟨622694957695938512189265125084135181091197934873,631978366502419386057412233476380269926006857377⟩,⟨32456682607964354154613479996102401418084023795712,32953649959162868539528007958885221822745314066432⟩⟩
theorem link7_1_checked : cell7_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert7 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.start)/500000)=true := by decide +kernel
def cell7_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow,2,⟨1814747388513666548315098835164208823738837237760,1815444281392823780008031979690375289181638230016⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-3386900011567081157330973035087885685515,3386900011567081157330973035087885685515⟩,⟨11191370796253908263613351517853983209411538788412,11236626238820128313876948157252891300213082098309⟩,⟨901453319720138432484165080654554979618113959720,910518485270260911436125366746415735280641796554⟩,⟨46986384424281129933215140195625089998581305180160,47477743951659338980855540849755646177101945503744⟩⟩
theorem link7_2_checked : cell7_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0000.cert7 ((ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.start)/500000)=true := by decide +kernel
def cells : List Transport.ReferencePositionCell := [cell0_1,cell0_2,cell1_1,cell1_2,cell2_1,cell2_2,cell3_1,cell3_2,cell4_1,cell4_2,cell5_1,cell5_2,cell6_1,cell6_2,cell7_1,cell7_2]
theorem checked : cells.all (fun c => c.check scale 1)=true := by decide +kernel
theorem weight0_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert0∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound0_1_checked : cell0_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound0_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell0_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight0_member hc link0_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound0_1_checked
theorem bound0_2_checked : cell0_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound0_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell0_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight0_member hc link0_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound0_2_checked
theorem weight1_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert1∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound1_1_checked : cell1_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound1_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell1_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight1_member hc link1_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound1_1_checked
theorem bound1_2_checked : cell1_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound1_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell1_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight1_member hc link1_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound1_2_checked
theorem weight2_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert2∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound2_1_checked : cell2_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound2_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell2_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight2_member hc link2_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound2_1_checked
theorem bound2_2_checked : cell2_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound2_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell2_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight2_member hc link2_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound2_2_checked
theorem weight3_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert3∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound3_1_checked : cell3_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound3_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell3_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight3_member hc link3_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound3_1_checked
theorem bound3_2_checked : cell3_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound3_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell3_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight3_member hc link3_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound3_2_checked
theorem weight4_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert4∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound4_1_checked : cell4_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound4_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell4_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight4_member hc link4_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound4_1_checked
theorem bound4_2_checked : cell4_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound4_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell4_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight4_member hc link4_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound4_2_checked
theorem weight5_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert5∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound5_1_checked : cell5_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound5_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell5_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight5_member hc link5_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound5_1_checked
theorem bound5_2_checked : cell5_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound5_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell5_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight5_member hc link5_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound5_2_checked
theorem weight6_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert6∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound6_1_checked : cell6_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound6_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell6_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight6_member hc link6_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound6_1_checked
theorem bound6_2_checked : cell6_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound6_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell6_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight6_member hc link6_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound6_2_checked
theorem weight7_member : ReferenceWeightData.CoarseLowerShape.Batch0000.cert7∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound7_1_checked : cell7_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound7_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell7_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight7_member hc link7_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound7_1_checked
theorem bound7_2_checked : cell7_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound7_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell7_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight7_member hc link7_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound7_2_checked
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>⟨actual_bound0_1 hz,actual_bound0_2 hz⟩
  · exact fun z hz=>⟨actual_bound1_1 hz,actual_bound1_2 hz⟩
  · exact fun z hz=>⟨actual_bound2_1 hz,actual_bound2_2 hz⟩
  · exact fun z hz=>⟨actual_bound3_1 hz,actual_bound3_2 hz⟩
  · exact fun z hz=>⟨actual_bound4_1 hz,actual_bound4_2 hz⟩
  · exact fun z hz=>⟨actual_bound5_1 hz,actual_bound5_2 hz⟩
  · exact fun z hz=>⟨actual_bound6_1 hz,actual_bound6_2 hz⟩
  · exact fun z hz=>⟨actual_bound7_1 hz,actual_bound7_2 hz⟩
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0000
