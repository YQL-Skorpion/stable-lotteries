import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0072_0075
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0073_0076
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0077_0080

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0076
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert608 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert608,⟨81956734638899731718574,81956736816714717576231⟩,⟨0,1136382768397703674976⟩⟩
def cert609 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert609,⟨80821707740055057746532,80821709873717184851473⟩,⟨0,1136440141280413939512⟩⟩
def cert610 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert610,⟨79973286191336902588748,79973288306652841175400⟩,⟨0,849214284381414723012⟩⟩
def cert611 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert611,⟨79124833834205513367176,79124835931297969216803⟩,⟨0,849245726155193715826⟩⟩
def cert612 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert612,⟨78138037317602482448562,78138039385998947502336⟩,⟨0,987873914205821380706⟩⟩
def cert613 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert613,⟨77151199631226719929096,77151201671153770849218⟩,⟨0,987916086858891217695⟩⟩
def cert614 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert614,⟨76307954689221900690526,76307956711446159233193⟩,⟨0,844035268858087719877⟩⟩
def cert615 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.cert615,⟨75464680051142167245418,75464682055785607213744⟩,⟨0,844065594507093822376⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert608,cert609,cert610,cert611,cert612,cert613,cert614,cert615]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0076.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell608,ReferenceCumulativeData.CoarseLowerShapeTime.cell609,ReferenceCumulativeData.CoarseLowerShapeTime.cell610,ReferenceCumulativeData.CoarseLowerShapeTime.cell611,ReferenceCumulativeData.CoarseLowerShapeTime.cell612,ReferenceCumulativeData.CoarseLowerShapeTime.cell613,ReferenceCumulativeData.CoarseLowerShapeTime.cell614,ReferenceCumulativeData.CoarseLowerShapeTime.cell615] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0076

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0077
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert616 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert616,⟨74333928389260583329716,74333930351395474007029⟩,⟨0,1132179975068656699719⟩⟩
def cert617 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert617,⟨73203124033970893019578,73203125953995325536293⟩,⟨0,1132234197174080150667⟩⟩
def cert618 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert618,⟨72371186143039638228251,72371188046382632553420⟩,⟨0,832715198588367515308⟩⟩
def cert619 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert619,⟨71539220090338531380282,71539221977118157911953⟩,⟨0,832743973666778413064⟩⟩
def cert620 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert620,⟨71234967078928893568876,71234968964909216207096⟩,⟨0,304356649884464201436⟩⟩
def cert621 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert621,⟨70930710337157414772344,70930712222339995885400⟩,⟨0,304360409035835101219⟩⟩
def cert622 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert622,⟨69797548968683433360344,69797550812025125890498⟩,⟨0,1134606472173396401295⟩⟩
def cert623 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.cert623,⟨68664336285344237823626,68664338087148324695544⟩,⟨0,1134659287495184271304⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert616,cert617,cert618,cert619,cert620,cert621,cert622,cert623]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0077.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell616,ReferenceCumulativeData.CoarseLowerShapeTime.cell617,ReferenceCumulativeData.CoarseLowerShapeTime.cell618,ReferenceCumulativeData.CoarseLowerShapeTime.cell619,ReferenceCumulativeData.CoarseLowerShapeTime.cell620,ReferenceCumulativeData.CoarseLowerShapeTime.cell621,ReferenceCumulativeData.CoarseLowerShapeTime.cell622,ReferenceCumulativeData.CoarseLowerShapeTime.cell623] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0077

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0078
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert624 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert624,⟨67579335646941053565891,67579337412301717522479⟩,⟨0,1086332817798374867076⟩⟩
def cert625 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert625,⟨66494288674283541999138,66494290403458560438233⟩,⟨0,1086380479416444482362⟩⟩
def cert626 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert626,⟨65322006095777771236097,65322007779250631950531⟩,⟨0,1173846519072076513439⟩⟩
def cert627 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert627,⟨64149670268448395415183,64149671906574247110279⟩,⟨0,1173901455563117895219⟩⟩
def cert628 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert628,⟨63145130720554927884197,63145132330224151140422⟩,⟨0,1005694119257010927597⟩⟩
def cert629 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert629,⟨62140552663956411567344,62140554245362686982718⟩,⟨0,1005733697832197931459⟩⟩
def cert630 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert630,⟨61318116824440573273611,61318118390384262336898⟩,⟨0,823213239551450450571⟩⟩
def cert631 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.cert631,⟨60495655503315394429233,60495657053884366982809⟩,⟨0,823239311961399362088⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert624,cert625,cert626,cert627,cert628,cert629,cert630,cert631]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0078.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell624,ReferenceCumulativeData.CoarseLowerShapeTime.cell625,ReferenceCumulativeData.CoarseLowerShapeTime.cell626,ReferenceCumulativeData.CoarseLowerShapeTime.cell627,ReferenceCumulativeData.CoarseLowerShapeTime.cell628,ReferenceCumulativeData.CoarseLowerShapeTime.cell629,ReferenceCumulativeData.CoarseLowerShapeTime.cell630,ReferenceCumulativeData.CoarseLowerShapeTime.cell631] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0078

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0079
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert632 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert632,⟨59675464915458495013738,59675466450783366636294⟩,⟨0,820966924286374895902⟩⟩
def cert633 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert633,⟨58855249279225186181488,58855250799393587457770⟩,⟨0,820992562042151943175⟩⟩
def cert634 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert634,⟨58139537712974467943980,58139539223070482087827⟩,⟨0,716305599789003604038⟩⟩
def cert635 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert635,⟨57423807261273149993771,57423808761348165565242⟩,⟨0,716324879793501257068⟩⟩
def cert636 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert636,⟨56777492656296965041028,56777494149038071960931⟩,⟨0,646799577381199105737⟩⟩
def cert637 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert637,⟨56131162836207210556510,56131164321648569754791⟩,⟨0,646815083071340783837⟩⟩
def cert638 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert638,⟨55045980798158162155211,55045982248724194870309⟩,⟨0,1086557007735727037591⟩⟩
def cert639 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.cert639,⟨53960756348300218912846,53960757764265401470279⟩,⟨0,1086600807492486486602⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert632,cert633,cert634,cert635,cert636,cert637,cert638,cert639]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0079.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell632,ReferenceCumulativeData.CoarseLowerShapeTime.cell633,ReferenceCumulativeData.CoarseLowerShapeTime.cell634,ReferenceCumulativeData.CoarseLowerShapeTime.cell635,ReferenceCumulativeData.CoarseLowerShapeTime.cell636,ReferenceCumulativeData.CoarseLowerShapeTime.cell637,ReferenceCumulativeData.CoarseLowerShapeTime.cell638,ReferenceCumulativeData.CoarseLowerShapeTime.cell639] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0079
