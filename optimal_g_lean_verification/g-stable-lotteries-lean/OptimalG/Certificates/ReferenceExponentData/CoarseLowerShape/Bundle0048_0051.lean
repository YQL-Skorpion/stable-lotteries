import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0044_0047
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0045_0048
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0049_0052

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0048
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert384 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert384,⟨164795811438621111195116,164795816388977796149451⟩,⟨0,33705988655738618461⟩⟩
def cert385 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert385,⟨164762107546461480921722,164762112496818131700489⟩,⟨0,33706105700660402696⟩⟩
def cert386 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert386,⟨164729696434627538361569,164729701384984157428183⟩,⟨0,32413158910226630557⟩⟩
def cert387 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert387,⟨164697285214664731492913,164697290165021317469876⟩,⟨0,32413267142811761456⟩⟩
def cert388 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert388,⟨164546257185876135682621,164546262136228212364992⟩,⟨0,151072490059223206814⟩⟩
def cert389 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert389,⟨164395226809356411922874,164395231759703335554753⟩,⟨0,151074848293731915938⟩⟩
def cert390 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert390,⟨164189159318350874937254,164189164268681912025036⟩,⟨0,206150302221111071737⟩⟩
def cert391 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.cert391,⟨163983087457173730180085,163983092407486703624696⟩,⟨0,206154699107430567237⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert384,cert385,cert386,cert387,cert388,cert389,cert390,cert391]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0048.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell384,ReferenceCumulativeData.CoarseLowerShapeTime.cell385,ReferenceCumulativeData.CoarseLowerShapeTime.cell386,ReferenceCumulativeData.CoarseLowerShapeTime.cell387,ReferenceCumulativeData.CoarseLowerShapeTime.cell388,ReferenceCumulativeData.CoarseLowerShapeTime.cell389,ReferenceCumulativeData.CoarseLowerShapeTime.cell390,ReferenceCumulativeData.CoarseLowerShapeTime.cell391] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0048

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0049
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert392 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert392,⟨163850615656259902064446,163850620606567997398562⟩,⟨0,132505813116127311722⟩⟩
def cert393 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert393,⟨163718142062183733908182,163718147012486587260219⟩,⟨0,132507613286886328429⟩⟩
def cert394 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert394,⟨163583965763696157007475,163583970713993187799054⟩,⟨0,134211199838106615947⟩⟩
def cert395 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert395,⟨163449787625824815969900,163449792576115653331754⟩,⟨0,134213046510230833469⟩⟩
def cert396 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert396,⟨163308763100223873605754,163308768050507043939158⟩,⟨0,141063095065428363633⟩⟩
def cert397 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert397,⟨163167736542957360776444,163167741493232411408925⟩,⟨0,141065135200907360143⟩⟩
def cert398 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert398,⟨163102496051055819316330,163102501001330082553276⟩,⟨0,65248697390138728744⟩⟩
def cert399 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.cert399,⟨163037255127246112332069,163037260077519567856834⟩,⟨0,65249130126693547696⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert392,cert393,cert394,cert395,cert396,cert397,cert398,cert399]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0049.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell392,ReferenceCumulativeData.CoarseLowerShapeTime.cell393,ReferenceCumulativeData.CoarseLowerShapeTime.cell394,ReferenceCumulativeData.CoarseLowerShapeTime.cell395,ReferenceCumulativeData.CoarseLowerShapeTime.cell396,ReferenceCumulativeData.CoarseLowerShapeTime.cell397,ReferenceCumulativeData.CoarseLowerShapeTime.cell398,ReferenceCumulativeData.CoarseLowerShapeTime.cell399] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0049

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0050
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert400 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert400,⟨162694977233860245234157,162694982183988400266579⟩,⟨0,342503886899291798141⟩⟩
def cert401 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert401,⟨162352687454683568541914,162352692404651482348828⟩,⟨0,342515892533909884236⟩⟩
def cert402 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert402,⟨162245057110994126545935,162245062060957352496641⟩,⟨0,107652543173588898285⟩⟩
def cert403 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert403,⟨162137425601008114038866,162137430550966514082902⟩,⟨0,107653713146746185594⟩⟩
def cert404 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert404,⟨161900217755748692326436,161900222705650072577731⟩,⟨0,237315732738875511093⟩⟩
def cert405 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert405,⟨161663004246727061894366,161663009196568161949062⟩,⟨0,237321435911128548727⟩⟩
def cert406 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert406,⟨161453645427222420054118,161453650377020486927456⟩,⟨0,209442899444656684364⟩⟩
def cert407 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.cert407,⟨161244282197176654325486,161244287146929777867039⟩,⟨0,209447337114040345202⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert400,cert401,cert402,cert403,cert404,cert405,cert406,cert407]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0050.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell400,ReferenceCumulativeData.CoarseLowerShapeTime.cell401,ReferenceCumulativeData.CoarseLowerShapeTime.cell402,ReferenceCumulativeData.CoarseLowerShapeTime.cell403,ReferenceCumulativeData.CoarseLowerShapeTime.cell404,ReferenceCumulativeData.CoarseLowerShapeTime.cell405,ReferenceCumulativeData.CoarseLowerShapeTime.cell406,ReferenceCumulativeData.CoarseLowerShapeTime.cell407] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0050

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0051
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert408 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert408,⟨161107751352903569998361,161107756302644305305429⟩,⟨0,136566364829411758451⟩⟩
def cert409 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert409,⟨160971218647500720371070,160971223597228729907220⟩,⟨0,136568233380438992740⟩⟩
def cert410 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert410,⟨160898225340339764759926,160898230290065832969215⟩,⟨0,73003461041288455823⟩⟩
def cert411 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert411,⟨160825231501306029175701,160825236451030129487534⟩,⟨0,73003994048580259411⟩⟩
def cert412 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert412,⟨160550724761050115634915,160550729710659232901276⟩,⟨0,274650432512409432702⟩⟩
def cert413 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert413,⟨160276210500512574499566,160276215450001385347816⟩,⟨0,274658013222975438596⟩⟩
def cert414 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert414,⟨159926679240102128210115,159926684189328478033029⟩,⟨0,349763152573764354680⟩⟩
def cert415 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.cert415,⟨159577135863464213956479,159577140812414836248452⟩,⟨0,349775392400763091844⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert408,cert409,cert410,cert411,cert412,cert413,cert414,cert415]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0051.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell408,ReferenceCumulativeData.CoarseLowerShapeTime.cell409,ReferenceCumulativeData.CoarseLowerShapeTime.cell410,ReferenceCumulativeData.CoarseLowerShapeTime.cell411,ReferenceCumulativeData.CoarseLowerShapeTime.cell412,ReferenceCumulativeData.CoarseLowerShapeTime.cell413,ReferenceCumulativeData.CoarseLowerShapeTime.cell414,ReferenceCumulativeData.CoarseLowerShapeTime.cell415] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0051
