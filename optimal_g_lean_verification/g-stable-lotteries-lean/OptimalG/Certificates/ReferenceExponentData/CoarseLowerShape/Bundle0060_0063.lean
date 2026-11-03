import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0056_0059
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0057_0060
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0061_0064

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0060
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert480 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert480,⟨151061197918559042598259,151061202722368229410634⟩,⟨0,198836665275998771355⟩⟩
def cert481 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert481,⟨150862532597692997852149,150862537397792493884445⟩,⟨0,198847996566977826456⟩⟩
def cert482 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert482,⟨150717703659815988438766,150717708458471587940686⟩,⟨0,144926321915631353803⟩⟩
def cert483 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert483,⟨150572868702598242084566,150572873499809039197481⟩,⟨0,144932385286902496093⟩⟩
def cert484 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert484,⟨150484706052614579960071,150484710849498131416840⟩,⟨0,88198854430690439272⟩⟩
def cert485 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert485,⟨150396541155840438371936,150396545952396618851804⟩,⟨0,88201111212775338685⟩⟩
def cert486 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert486,⟨150290443128682495390114,150290447924667629768153⟩,⟨0,106150488593628196620⟩⟩
def cert487 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.cert487,⟨150184341835443549513984,150184346630857374298277⟩,⟨0,106153772102007600455⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert480,cert481,cert482,cert483,cert484,cert485,cert486,cert487]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0060.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell480,ReferenceCumulativeData.CoarseLowerShapeTime.cell481,ReferenceCumulativeData.CoarseLowerShapeTime.cell482,ReferenceCumulativeData.CoarseLowerShapeTime.cell483,ReferenceCumulativeData.CoarseLowerShapeTime.cell484,ReferenceCumulativeData.CoarseLowerShapeTime.cell485,ReferenceCumulativeData.CoarseLowerShapeTime.cell486,ReferenceCumulativeData.CoarseLowerShapeTime.cell487] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0060

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0061
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert488 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert488,⟨149903165725685702330916,149903170510315247236574⟩,⟨0,281546517631987418679⟩⟩
def cert489 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert489,⟨149621966414732415037398,149621971188564378091835⟩,⟨0,281570046556352813937⟩⟩
def cert490 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert490,⟨149393945232883896820259,149393950000914905457955⟩,⟨0,228266085546018532539⟩⟩
def cert491 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert491,⟨149165908579852590780138,149165913342076811476951⟩,⟨0,228281733209335897161⟩⟩
def cert492 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert492,⟨148918775771438810967325,148918780526203227036136⟩,⟨0,247421964797383506365⟩⟩
def cert493 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert493,⟨148671624553797469260463,148671629301093899977069⟩,⟨0,247440600836380305680⟩⟩
def cert494 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert494,⟨148631638622107762738614,148631643369372549449668⟩,⟨0,39993529177890225625⟩⟩
def cert495 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.cert495,⟨148591652204239373934675,148591656951472511020545⟩,⟨0,39994016323357046563⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert488,cert489,cert490,cert491,cert492,cert493,cert494,cert495]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0061.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell488,ReferenceCumulativeData.CoarseLowerShapeTime.cell489,ReferenceCumulativeData.CoarseLowerShapeTime.cell490,ReferenceCumulativeData.CoarseLowerShapeTime.cell491,ReferenceCumulativeData.CoarseLowerShapeTime.cell492,ReferenceCumulativeData.CoarseLowerShapeTime.cell493,ReferenceCumulativeData.CoarseLowerShapeTime.cell494,ReferenceCumulativeData.CoarseLowerShapeTime.cell495] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0061

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0062
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert496 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert496,⟨148460411261873989274896,148460416007984425706822⟩,⟨0,131322841225026341473⟩⟩
def cert497 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert497,⟨148329165064955190740814,148329169809942270530841⟩,⟨0,131328130003186465862⟩⟩
def cert498 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert498,⟨148111722946136489459811,148111727685965934339256⟩,⟨0,217667452421008341310⟩⟩
def cert499 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert499,⟨147894266262172203191193,147894270996839701033458⟩,⟨0,217682173860611350873⟩⟩
def cert500 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert500,⟨147700809019513131587153,147700813750522477655594⟩,⟨0,193636376618241909560⟩⟩
def cert501 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert501,⟨147507340119986831814831,147507344847335290955031⟩,⟨0,193648144420794584194⟩⟩
def cert502 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert502,⟨147364633725063667673754,147364638450936652476396⟩,⟨0,142804205913622484585⟩⟩
def cert503 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.cert503,⟨147221920929930437363888,147221925654327131284940⟩,⟨0,142810650928530114995⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert496,cert497,cert498,cert499,cert500,cert501,cert502,cert503]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0062.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell496,ReferenceCumulativeData.CoarseLowerShapeTime.cell497,ReferenceCumulativeData.CoarseLowerShapeTime.cell498,ReferenceCumulativeData.CoarseLowerShapeTime.cell499,ReferenceCumulativeData.CoarseLowerShapeTime.cell500,ReferenceCumulativeData.CoarseLowerShapeTime.cell501,ReferenceCumulativeData.CoarseLowerShapeTime.cell502,ReferenceCumulativeData.CoarseLowerShapeTime.cell503] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0062

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0063
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert504 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert504,⟨147015208960789967432480,147015213680663453043501⟩,⟨0,206917984976368055723⟩⟩
def cert505 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert505,⟨146808483436873274229854,146808488152219901765967⟩,⟨0,206931676913608899239⟩⟩
def cert506 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert506,⟨146553617547432350348352,146553622254213759894525⟩,⟨0,255180631529811597454⟩⟩
def cert507 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert507,⟨146298730797994027524618,146298735496201631191368⟩,⟨0,255201751001682895878⟩⟩
def cert508 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert508,⟨146074865749499000309631,146074870441855082611613⟩,⟨0,224109085757929729224⟩⟩
def cert509 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert509,⟨145850984402225985013322,145850989088725362445710⟩,⟨0,224125561967090552106⟩⟩
def cert510 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert510,⟨145611685110391473054814,145611689789677590734861⟩,⟨0,239579504832424526984⟩⟩
def cert511 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.cert511,⟨145372366966397537934404,145372371638463518983393⟩,⟨0,239598575670628378976⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert504,cert505,cert506,cert507,cert508,cert509,cert510,cert511]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0063.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell504,ReferenceCumulativeData.CoarseLowerShapeTime.cell505,ReferenceCumulativeData.CoarseLowerShapeTime.cell506,ReferenceCumulativeData.CoarseLowerShapeTime.cell507,ReferenceCumulativeData.CoarseLowerShapeTime.cell508,ReferenceCumulativeData.CoarseLowerShapeTime.cell509,ReferenceCumulativeData.CoarseLowerShapeTime.cell510,ReferenceCumulativeData.CoarseLowerShapeTime.cell511] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0063
