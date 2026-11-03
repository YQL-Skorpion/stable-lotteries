import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0064_0067
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0065_0068
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0069_0072

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0068
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert544 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert544,⟨141135908917855150810762,141135913498529739631118⟩,⟨0,13183689667450581208⟩⟩
def cert545 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert545,⟨141122726051149357687167,141122730631822647434518⟩,⟨0,13183753892638220919⟩⟩
def cert546 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert546,⟨141014517168144359148630,141014521748770494280748⟩,⟨0,108219985195392853548⟩⟩
def cert547 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert547,⟨140906307558783931125757,140906312139362947290790⟩,⟨0,108220712668452328497⟩⟩
def cert548 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert548,⟨140466564228577342848648,140466568805984449527438⟩,⟨0,439926942028466115506⟩⟩
def cert549 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert549,⟨140026808939158704490978,140026813513403646594065⟩,⟨0,439938976393504932957⟩⟩
def cert550 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert550,⟨139236447245472118678768,139236451801299505717082⟩,⟨0,790956697917668079608⟩⟩
def cert551 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0068.cert551,⟨138446047181681005594564,138446051719193125935788⟩,⟨0,790995506147938040289⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert544,cert545,cert546,cert547,cert548,cert549,cert550,cert551]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0068.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell544,ReferenceCumulativeData.CoarseLowerShapeTime.cell545,ReferenceCumulativeData.CoarseLowerShapeTime.cell546,ReferenceCumulativeData.CoarseLowerShapeTime.cell547,ReferenceCumulativeData.CoarseLowerShapeTime.cell548,ReferenceCumulativeData.CoarseLowerShapeTime.cell549,ReferenceCumulativeData.CoarseLowerShapeTime.cell550,ReferenceCumulativeData.CoarseLowerShapeTime.cell551] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0068

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0069
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert552 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert552,⟨137209622132690476112536,137209626599809072192255⟩,⟨0,1237888425947400496505⟩⟩
def cert553 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert553,⟨135973104236364100150271,135973108633634754347196⟩,⟨0,1237982956226256895165⟩⟩
def cert554 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert554,⟨134732771194112451006787,134732775520836421395172⟩,⟨0,1241814808323893766463⟩⟩
def cert555 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert555,⟨133492346010242038608424,133492350266978744573525⟩,⟨0,1241908662221688150391⟩⟩
def cert556 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert556,⟨132257218777790760215262,132257222965401675759943⟩,⟨0,1236605684390016273600⟩⟩
def cert557 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert557,⟨131022001450272558061309,131022005569314649894200⟩,⟨0,1236697483516461621207⟩⟩
def cert558 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert558,⟨129792029188406334108650,129792033239730694967792⟩,⟨0,1231447440392783818967⟩⟩
def cert559 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0069.cert559,⟨128561968833005686397623,128561972817166865536976⟩,⟨0,1231537229877506157532⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert552,cert553,cert554,cert555,cert556,cert557,cert558,cert559]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0069.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell552,ReferenceCumulativeData.CoarseLowerShapeTime.cell553,ReferenceCumulativeData.CoarseLowerShapeTime.cell554,ReferenceCumulativeData.CoarseLowerShapeTime.cell555,ReferenceCumulativeData.CoarseLowerShapeTime.cell556,ReferenceCumulativeData.CoarseLowerShapeTime.cell557,ReferenceCumulativeData.CoarseLowerShapeTime.cell558,ReferenceCumulativeData.CoarseLowerShapeTime.cell559] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0069

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0070
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert560 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert560,⟨127863609742705922476811,127863613714630013271328⟩,⟨0,698837069812195055748⟩⟩
def cert561 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert561,⟨127165222556456098941416,127165226516201403238457⟩,⟨0,698865478177736693920⟩⟩
def cert562 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert562,⟨126944440956324683239229,126944444915688308021122⟩,⟨0,220829403265048539715⟩⟩
def cert563 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert563,⟨126723656567548906833522,126723660526531434620017⟩,⟨0,220832201773932988451⟩⟩
def cert564 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert564,⟨125595534604022653789183,125595538511572310831210⟩,⟨0,1129375981388336361374⟩⟩
def cert565 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert565,⟨124467340308321323204855,124467344164838886416524⟩,⟨0,1129449639417409665346⟩⟩
def cert566 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert566,⟨123310067151867120168545,123310070953296471709356⟩,⟨0,1158600385584751026330⟩⟩
def cert567 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0070.cert567,⟨122152718884222199425062,122152722631012283433979⟩,⟨0,1158676938517921052046⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert560,cert561,cert562,cert563,cert564,cert565,cert566,cert567]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0070.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell560,ReferenceCumulativeData.CoarseLowerShapeTime.cell561,ReferenceCumulativeData.CoarseLowerShapeTime.cell562,ReferenceCumulativeData.CoarseLowerShapeTime.cell563,ReferenceCumulativeData.CoarseLowerShapeTime.cell564,ReferenceCumulativeData.CoarseLowerShapeTime.cell565,ReferenceCumulativeData.CoarseLowerShapeTime.cell566,ReferenceCumulativeData.CoarseLowerShapeTime.cell567] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0070

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0071
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert568 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert568,⟨121046049184004647114123,121046052883064495823201⟩,⟨0,1107890272715017064805⟩⟩
def cert569 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert569,⟨119939311703789148245398,119939315355498509651474⟩,⟨0,1107959322500271398243⟩⟩
def cert570 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert570,⟨119079487324865725958658,119079490954440339084203⟩,⟨0,860564765701384177000⟩⟩
def cert571 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert571,⟨118219622502775923413440,118219626110355587250257⟩,⟨0,860605807995430194709⟩⟩
def cert572 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert572,⟨117015930391819039720319,117015933938871502401381⟩,⟨0,1205150744023951822820⟩⟩
def cert573 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert573,⟨115812159982547167081160,115812163469614721077177⟩,⟨0,1205230697397575220314⟩⟩
def cert574 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert574,⟨114655407297318649700864,114655410731232902168917⟩,⟨0,1158107738511252578169⟩⟩
def cert575 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0071.cert575,⟨113498583310720110709665,113498586691949142118509⟩,⟨0,1158180519756789778619⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert568,cert569,cert570,cert571,cert572,cert573,cert574,cert575]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0071.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell568,ReferenceCumulativeData.CoarseLowerShapeTime.cell569,ReferenceCumulativeData.CoarseLowerShapeTime.cell570,ReferenceCumulativeData.CoarseLowerShapeTime.cell571,ReferenceCumulativeData.CoarseLowerShapeTime.cell572,ReferenceCumulativeData.CoarseLowerShapeTime.cell573,ReferenceCumulativeData.CoarseLowerShapeTime.cell574,ReferenceCumulativeData.CoarseLowerShapeTime.cell575] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0071
