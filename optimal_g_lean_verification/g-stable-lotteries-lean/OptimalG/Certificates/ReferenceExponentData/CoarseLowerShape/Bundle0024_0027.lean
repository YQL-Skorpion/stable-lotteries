import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0020_0023
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0025_0028

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0024
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert192 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert192,⟨184831168429163490795323,184831173753046864889438⟩,⟨0,309099440792483296589⟩⟩
def cert193 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert193,⟨184522305953961398230311,184522311266127982974451⟩,⟨0,309112699914567601775⟩⟩
def cert194 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert194,⟨184275210255024775015931,184275215561200427964895⟩,⟨0,247255930774129876293⟩⟩
def cert195 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert195,⟨184028106006484692556836,184028111306673237151106⟩,⟨0,247264558627425665103⟩⟩
def cert196 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert196,⟨183811885197462258477662,183811890493643574148938⟩,⟨0,216343609974741299262⟩⟩
def cert197 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert197,⟨183595657739826120424606,183595663032002436890488⟩,⟨0,216350311110740485123⟩⟩
def cert198 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert198,⟨183286753040524669602812,183286758321022038470482⟩,⟨0,309155656494820134534⟩⟩
def cert199 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.cert199,⟨182977834535076807109999,182977839803904482433708⟩,⟨0,309169616180398842670⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert192,cert193,cert194,cert195,cert196,cert197,cert198,cert199]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0024.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell192,ReferenceCumulativeData.CoarseLowerShapeTime.cell193,ReferenceCumulativeData.CoarseLowerShapeTime.cell194,ReferenceCumulativeData.CoarseLowerShapeTime.cell195,ReferenceCumulativeData.CoarseLowerShapeTime.cell196,ReferenceCumulativeData.CoarseLowerShapeTime.cell197,ReferenceCumulativeData.CoarseLowerShapeTime.cell198,ReferenceCumulativeData.CoarseLowerShapeTime.cell199] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0024

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0025
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert200 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert200,⟨182668905145392606193536,182668910402559970480274⟩,⟨0,309180704032312919597⟩⟩
def cert201 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert201,⟨182359961670473615414344,182359966915989866395555⟩,⟨0,309194943227814212506⟩⟩
def cert202 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert202,⟨182143694189062459310428,182143699430588703581666⟩,⟨0,216390754827330002846⟩⟩
def cert203 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert203,⟨181927419689804065415165,181927424927342496240689⟩,⟨0,216397825587094880270⟩⟩
def cert204 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert204,⟨181731487554820078967127,181731492789395835747278⟩,⟨0,196033396625740283173⟩⟩
def cert205 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert205,⟨181535549585708257487326,181535554817322810904779⟩,⟨0,196039270161680061587⟩⟩
def cert206 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert206,⟨181341690383823017442282,181341695612571342190064⟩,⟨0,193958413734385750617⟩⟩
def cert207 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.cert207,⟨181147825402190592079553,181147830628074091780750⟩,⟨0,193964231715224392784⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert200,cert201,cert202,cert203,cert204,cert205,cert206,cert207]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0025.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell200,ReferenceCumulativeData.CoarseLowerShapeTime.cell201,ReferenceCumulativeData.CoarseLowerShapeTime.cell202,ReferenceCumulativeData.CoarseLowerShapeTime.cell203,ReferenceCumulativeData.CoarseLowerShapeTime.cell204,ReferenceCumulativeData.CoarseLowerShapeTime.cell205,ReferenceCumulativeData.CoarseLowerShapeTime.cell206,ReferenceCumulativeData.CoarseLowerShapeTime.cell207] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0025

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0026
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert208 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert208,⟨181043238720018626430938,181043243945452909642463⟩,⟨0,104615461405145868268⟩⟩
def cert209 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert209,⟨180938650340410233113284,180938655565395418181187⟩,⟨0,104617164845327319152⟩⟩
def cert210 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert210,⟨180660532255324228162657,180660537471855473488984⟩,⟨0,278321833682761320123⟩⟩
def cert211 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert211,⟨180382402028746767861372,180382407236829985971493⟩,⟨0,278334088345857278681⟩⟩
def cert212 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert212,⟨180227352724953977049760,180227357931576294056026⟩,⟨0,155112669496226904110⟩⟩
def cert213 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert213,⟨180072299599234188874309,180072304804396171991749⟩,⟨0,155116511055980629756⟩⟩
def cert214 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert214,⟨179887390003579395045791,179887395206265144064866⟩,⟨0,184999785232126231514⟩⟩
def cert215 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.cert215,⟨179702474918152477544082,179702480118363136323845⟩,⟨0,185005308353896347862⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert208,cert209,cert210,cert211,cert212,cert213,cert214,cert215]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0026.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell208,ReferenceCumulativeData.CoarseLowerShapeTime.cell209,ReferenceCumulativeData.CoarseLowerShapeTime.cell210,ReferenceCumulativeData.CoarseLowerShapeTime.cell211,ReferenceCumulativeData.CoarseLowerShapeTime.cell212,ReferenceCumulativeData.CoarseLowerShapeTime.cell213,ReferenceCumulativeData.CoarseLowerShapeTime.cell214,ReferenceCumulativeData.CoarseLowerShapeTime.cell215] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0026

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0027
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert216 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert216,⟨179455209263160744440663,179455214457453839055971⟩,⟨0,247427089071015036313⟩⟩
def cert217 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert217,⟨179207933668924905833215,179207938857304081203679⟩,⟨0,247437108218224021331⟩⟩
def cert218 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert218,⟨178939367120469735449099,178939372301276463403952⟩,⟨0,268757199553439695593⟩⟩
def cert219 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert219,⟨178670788674353442663996,178670793847592770038327⟩,⟨0,268769199815946770818⟩⟩
def cert220 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert220,⟨178475673614669481197551,178475678785011518596063⟩,⟨0,195215766663398523436⟩⟩
def cert221 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert221,⟨178280552193828793003574,178280557361274937546098⟩,⟨0,195222167223078003184⟩⟩
def cert222 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert222,⟨178002306288693737982508,178002311447741673297631⟩,⟨0,278450934565846805682⟩⟩
def cert223 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.cert223,⟨177724047278074016167217,177724052428729499988903⟩,⟨0,278464154577301207938⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert216,cert217,cert218,cert219,cert220,cert221,cert222,cert223]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0027.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell216,ReferenceCumulativeData.CoarseLowerShapeTime.cell217,ReferenceCumulativeData.CoarseLowerShapeTime.cell218,ReferenceCumulativeData.CoarseLowerShapeTime.cell219,ReferenceCumulativeData.CoarseLowerShapeTime.cell220,ReferenceCumulativeData.CoarseLowerShapeTime.cell221,ReferenceCumulativeData.CoarseLowerShapeTime.cell222,ReferenceCumulativeData.CoarseLowerShapeTime.cell223] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0027
