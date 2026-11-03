import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0040_0043
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0041_0044
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0045_0048

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0044
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert352 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert352,⟨166066880529724590077099,166066885480721718531961⟩,⟨0,57439818017702845368⟩⟩
def cert353 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert353,⟨166009449732637728002951,166009454683613585293191⟩,⟨0,57440329036264868774⟩⟩
def cert354 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert354,⟨165889225763663462765937,165889230714442448572139⟩,⟨0,120265749343334010369⟩⟩
def cert355 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert355,⟨165768999557005996124262,165769004507586774695918⟩,⟨0,120267997696192694143⟩⟩
def cert356 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert356,⟨165765838506453375467732,165765843457034150379115⟩,⟨0,3161079715449024190⟩⟩
def cert357 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert357,⟨165762677454336920230880,165762682404917691481334⟩,⟨0,3161081279481234543⟩⟩
def cert358 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert358,⟨165670424096854893594387,165670429047343944636025⟩,⟨0,92278201680040264872⟩⟩
def cert359 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.cert359,⟨165578169406298722983161,165578174356695604111370⟩,⟨0,92279539663107281724⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert352,cert353,cert354,cert355,cert356,cert357,cert358,cert359]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0044.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell352,ReferenceCumulativeData.CoarseLowerShapeTime.cell353,ReferenceCumulativeData.CoarseLowerShapeTime.cell354,ReferenceCumulativeData.CoarseLowerShapeTime.cell355,ReferenceCumulativeData.CoarseLowerShapeTime.cell356,ReferenceCumulativeData.CoarseLowerShapeTime.cell357,ReferenceCumulativeData.CoarseLowerShapeTime.cell358,ReferenceCumulativeData.CoarseLowerShapeTime.cell359] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0044

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0045
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert360 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert360,⟨165548207977437723855020,165548212927831449359755⟩,⟨0,29964049750045732378⟩⟩
def cert361 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert361,⟨165518246407820064493435,165518251358210629371860⟩,⟨0,29964190674824512855⟩⟩
def cert362 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert362,⟨165490079779063640753752,165490084729451576273252⟩,⟨0,28168945126216073707⟩⟩
def cert363 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert363,⟨165461913025846488156374,165461917976231790565793⟩,⟨0,28169069726479559661⟩⟩
def cert364 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert364,⟨165413072315125638708834,165413077265497014754073⟩,⟨0,48847714532798148457⟩⟩
def cert365 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert365,⟨165364231227826162808629,165364236178183578399507⟩,⟨0,48848091846880095811⟩⟩
def cert366 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert366,⟨165346817689193667462030,165346822639551082344053⟩,⟨0,17414133701042245254⟩⟩
def cert367 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.cert367,⟨165329404119083684850222,165329409069441098903884⟩,⟨0,17414165194840957957⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert360,cert361,cert362,cert363,cert364,cert365,cert366,cert367]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0045.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell360,ReferenceCumulativeData.CoarseLowerShapeTime.cell361,ReferenceCumulativeData.CoarseLowerShapeTime.cell362,ReferenceCumulativeData.CoarseLowerShapeTime.cell363,ReferenceCumulativeData.CoarseLowerShapeTime.cell364,ReferenceCumulativeData.CoarseLowerShapeTime.cell365,ReferenceCumulativeData.CoarseLowerShapeTime.cell366,ReferenceCumulativeData.CoarseLowerShapeTime.cell367] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0045

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0046
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert368 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert368,⟨165271319810836066754554,165271324761193425142942⟩,⟨0,58090921471416382566⟩⟩
def cert369 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert369,⟨165213235152846091562879,165213240103203379549025⟩,⟨0,58091271817748756934⟩⟩
def cert370 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert370,⟨165211993514205600583045,165211998464562888568638⟩,⟨0,1241641662468631291⟩⟩
def cert371 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert371,⟨165210751875405296491351,165210756825762584476388⟩,⟨0,1241641822287643238⟩⟩
def cert372 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert372,⟨165136090994348239783264,165136095944705327566309⟩,⟨0,74671809414967377151⟩⟩
def cert373 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert373,⟨165061429535456840175382,165061434485813687720011⟩,⟨0,74672388532637934502⟩⟩
def cert374 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert374,⟨165046580935831165665193,165046585886188011518590⟩,⟨0,14849031007279708008⟩⟩
def cert375 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.cert375,⟨165031732313401789018065,165031737263758633118038⟩,⟨0,14849053821035261734⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert368,cert369,cert370,cert371,cert372,cert373,cert374,cert375]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0046.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell368,ReferenceCumulativeData.CoarseLowerShapeTime.cell369,ReferenceCumulativeData.CoarseLowerShapeTime.cell370,ReferenceCumulativeData.CoarseLowerShapeTime.cell371,ReferenceCumulativeData.CoarseLowerShapeTime.cell372,ReferenceCumulativeData.CoarseLowerShapeTime.cell373,ReferenceCumulativeData.CoarseLowerShapeTime.cell374,ReferenceCumulativeData.CoarseLowerShapeTime.cell375] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0046

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0047
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert376 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert376,⟨165015134891356899550577,165015139841713741094416⟩,⟨0,16597961047732846257⟩⟩
def cert377 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert377,⟨164998537440820722698117,164998542391177561588735⟩,⟨0,16597989553062202337⟩⟩
def cert378 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert378,⟨164981432277271261954801,164981437227628097828323⟩,⟨0,17105736038251346480⟩⟩
def cert379 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert379,⟨164964327083460938481096,164964332033817771229157⟩,⟨0,17105766314486051055⟩⟩
def cert380 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert380,⟨164930624292273964695409,164930629242630771086403⟩,⟨0,33705013880056525968⟩⟩
def cert381 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert381,⟨164896921383609898229837,164896926333966676630353⟩,⟨0,33705131474757452154⟩⟩
def cert382 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert382,⟨164863218357469392499097,164863223307826141275713⟩,⟨0,33705249068819842210⟩⟩
def cert383 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.cert383,⟨164829515213852426040945,164829520164209143560216⟩,⟨0,33705366662918706262⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert376,cert377,cert378,cert379,cert380,cert381,cert382,cert383]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0047.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell376,ReferenceCumulativeData.CoarseLowerShapeTime.cell377,ReferenceCumulativeData.CoarseLowerShapeTime.cell378,ReferenceCumulativeData.CoarseLowerShapeTime.cell379,ReferenceCumulativeData.CoarseLowerShapeTime.cell380,ReferenceCumulativeData.CoarseLowerShapeTime.cell381,ReferenceCumulativeData.CoarseLowerShapeTime.cell382,ReferenceCumulativeData.CoarseLowerShapeTime.cell383] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0047
