import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0000_0003
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0005_0008

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert32 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert32,⟨249089073264989574936983,249089079764530103804878⟩,⟨0,604079975119937449031⟩⟩
def cert33 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert33,⟨248485605064101230320137,248485611547103690380921⟩,⟨0,604085646902503785011⟩⟩
def cert34 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert34,⟨248019448768383164044817,248019455243791449689399⟩,⟨0,466524958909518560914⟩⟩
def cert35 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert35,⟨247553289172836787548816,247553295640662986103221⟩,⟨0,466528484908900764679⟩⟩
def cert36 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert36,⟨247059358324344073046997,247059364783170133749619⟩,⟨0,494345347858830508274⟩⟩
def cert37 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert37,⟨246565423562624624064836,246565430012465714098095⟩,⟨0,494349530551633020511⟩⟩
def cert38 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert38,⟨245971003401972376918343,245971009836182805484294⟩,⟨0,595021500774591192056⟩⟩
def cert39 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.cert39,⟨245376577233246165689814,245376583651857575971625⟩,⟨0,595027979411650712453⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert32,cert33,cert34,cert35,cert36,cert37,cert38,cert39]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0004.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell32,ReferenceCumulativeData.CoarseLowerShapeTime.cell33,ReferenceCumulativeData.CoarseLowerShapeTime.cell34,ReferenceCumulativeData.CoarseLowerShapeTime.cell35,ReferenceCumulativeData.CoarseLowerShapeTime.cell36,ReferenceCumulativeData.CoarseLowerShapeTime.cell37,ReferenceCumulativeData.CoarseLowerShapeTime.cell38,ReferenceCumulativeData.CoarseLowerShapeTime.cell39] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0004

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0005
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert40 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert40,⟨244806119027112664771112,244806125431979520165015⟩,⟨0,571012968906420077941⟩⟩
def cert41 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert41,⟨244235654953576604266398,244235661344725604390186⟩,⟨0,571019252936948517426⟩⟩
def cert42 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert42,⟨243768724612891449847397,243768730996543995335566⟩,⟨0,467302533633108503690⟩⟩
def cert43 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert43,⟨243301790143006118345285,243301796519174140911837⟩,⟨0,467306891602122964787⟩⟩
def cert44 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert44,⟨242782775125435575593081,242782781491345719342130⟩,⟨0,519475562840490869389⟩⟩
def cert45 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert45,⟨242263754774457443355244,242263761130127836569876⟩,⟨0,519481210943234568916⟩⟩
def cert46 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert46,⟨242084227600801804626958,242084233956050524040035⟩,⟨0,179582314357058726066⟩⟩
def cert47 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.cert47,⟨241904699769535885887270,241904706124363190316912⟩,⟨0,179582984996573724693⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert40,cert41,cert42,cert43,cert44,cert45,cert46,cert47]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0005.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell40,ReferenceCumulativeData.CoarseLowerShapeTime.cell41,ReferenceCumulativeData.CoarseLowerShapeTime.cell42,ReferenceCumulativeData.CoarseLowerShapeTime.cell43,ReferenceCumulativeData.CoarseLowerShapeTime.cell44,ReferenceCumulativeData.CoarseLowerShapeTime.cell45,ReferenceCumulativeData.CoarseLowerShapeTime.cell46,ReferenceCumulativeData.CoarseLowerShapeTime.cell47] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0005

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0006
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert48 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert48,⟨241513059387605951245888,241513065738054714917950⟩,⟨0,391903046094169042220⟩⟩
def cert49 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert49,⟨241121415799781210938120,241121422145857319826885⟩,⟨0,391906387216133225616⟩⟩
def cert50 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert50,⟨240549985487451238344267,240549991819959309347049⟩,⟨0,571990406881452029629⟩⟩
def cert51 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert51,⟨239978548079134137226033,239978554398100704040040⟩,⟨0,571997923775002490164⟩⟩
def cert52 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert52,⟨239458834260433722474000,239458840569245639837829⟩,⟨0,520177821886485878521⟩⟩
def cert53 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert53,⟨238939114319051001456551,238939120617726319805085⟩,⟨0,520184261705760884329⟩⟩
def cert54 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert54,⟨238471181565791091036125,238471187857089829833005⟩,⟨0,468309414476404490005⟩⟩
def cert55 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.cert55,⟨238003243664420812491799,238003249948354784208403⟩,⟨0,468314794376808809313⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert48,cert49,cert50,cert51,cert52,cert53,cert54,cert55]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0006.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell48,ReferenceCumulativeData.CoarseLowerShapeTime.cell49,ReferenceCumulativeData.CoarseLowerShapeTime.cell50,ReferenceCumulativeData.CoarseLowerShapeTime.cell51,ReferenceCumulativeData.CoarseLowerShapeTime.cell52,ReferenceCumulativeData.CoarseLowerShapeTime.cell53,ReferenceCumulativeData.CoarseLowerShapeTime.cell54,ReferenceCumulativeData.CoarseLowerShapeTime.cell55] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0006

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert56 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert56,⟨237535129435205577790167,237535135711783893491643⟩,⟨0,468491690303188899453⟩⟩
def cert57 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert57,⟨237067009879518367950820,237067016148752808129892⟩,⟨0,468497249165018440719⟩⟩
def cert58 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert58,⟨236442574102738437714295,236442580354566066901285⟩,⟨0,625108604948119382531⟩⟩
def cert59 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert59,⟨235818128487701291282997,235818134722159190112789⟩,⟨0,625118995955821765955⟩⟩
def cert60 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert60,⟨235453721645988066029463,235453727877010660733895⟩,⟨0,364636237078040272544⟩⟩
def cert61 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert61,⟨235089311343241082925841,235089317570832661495153⟩,⟨0,364639808055827931868⟩⟩
def cert62 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert62,⟨234651589408392907648472,234651595630046421590180⟩,⟨0,438053327952192193677⟩⟩
def cert63 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.cert63,⟨234213862350994888630839,234213868566719228445918⟩,⟨0,438058641321450082852⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert56,cert57,cert58,cert59,cert60,cert61,cert62,cert63]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0007.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell56,ReferenceCumulativeData.CoarseLowerShapeTime.cell57,ReferenceCumulativeData.CoarseLowerShapeTime.cell58,ReferenceCumulativeData.CoarseLowerShapeTime.cell59,ReferenceCumulativeData.CoarseLowerShapeTime.cell60,ReferenceCumulativeData.CoarseLowerShapeTime.cell61,ReferenceCumulativeData.CoarseLowerShapeTime.cell62,ReferenceCumulativeData.CoarseLowerShapeTime.cell63] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0007
