import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.StaticBinaryLateAreaModels.ConeQuadraticConeLeft
import OptimalG.Certificates.StaticBinaryData.LateBatch002
import OptimalG.Certificates.StaticBinaryData.LateBatch003

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeLeft
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000)) (hr : q+d∈Icc (2950935005377889/10000000000000000) (348541/1000000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaQuadratic q) (hupper : upper (q+d)≤upperLeft (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.ConeQuadraticConeLeft.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.ConeQuadraticConeLeft.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (59/1600) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf000.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (59/1600) (43/800) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (13439745588864823864071691230752831890739091138950862187416303590773030601684164590856595174803186715507390371616160693891/43621012752902027814295064944082584007510869081489332458340167886076017479849277899203323407246214304933840000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf001.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (59/1600) (29/640) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (13439745588864823864071691230752831890739091138950862187416303590773030601684164590856595174803186715507390371616160693891/43621012752902027814295064944082584007510869081489332458340167886076017479849277899203323407246214304933840000000000000000) (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf002.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (29/640) (43/800) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (13439745588864823864071691230752831890739091138950862187416303590773030601684164590856595174803186715507390371616160693891/43621012752902027814295064944082584007510869081489332458340167886076017479849277899203323407246214304933840000000000000000) (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (1/50) (91/3200) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) (42840308184320790610906565003064493511801416899874672264337576745988266383102577894919635151287135157032798531616160693891/130863038258706083442885194832247752022532607244467997375020503658228052439547833697609970221738642914801520000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf004.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (91/3200) (59/1600) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) (28140026886592807237489128116908662701270254019412767225876940168380648492393371242888115163045160936270094451616160693891/87242025505804055628590129888165168015021738162978664916680335772152034959698555798406646814492428609867680000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf005.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (91/3200) (59/1600) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (28140026886592807237489128116908662701270254019412767225876940168380648492393371242888115163045160936270094451616160693891/87242025505804055628590129888165168015021738162978664916680335772152034959698555798406646814492428609867680000000000000000) (42840308184320790610906565003064493511801416899874672264337576745988266383102577894919635151287135157032798531616160693891/130863038258706083442885194832247752022532607244467997375020503658228052439547833697609970221738642914801520000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (1/50) (91/3200) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (42840308184320790610906565003064493511801416899874672264337576745988266383102577894919635151287135157032798531616160693891/130863038258706083442885194832247752022532607244467997375020503658228052439547833697609970221738642914801520000000000000000) (86941152077504740731158875661531985943394905541260387379719486478811120055230197851014195116013057819320910771616160693891/261726076517412166885770389664495504045065214488935994750041007316456104879095667395219940443477285829603040000000000000000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeLeft.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeLeftLeaf007.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (1/50) (91/3200) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (86941152077504740731158875661531985943394905541260387379719486478811120055230197851014195116013057819320910771616160693891/261726076517412166885770389664495504045065214488935994750041007316456104879095667395219940443477285829603040000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (91/3200) (59/1600) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (42840308184320790610906565003064493511801416899874672264337576745988266383102577894919635151287135157032798531616160693891/130863038258706083442885194832247752022532607244467997375020503658228052439547833697609970221738642914801520000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (59/1600) (43/800) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (20789886237728815550780409673830747296004672579181814706646621879576839547038767916872355168924173825888742411616160693891/65431519129353041721442597416123876011266303622233998687510251829114026219773916848804985110869321457400760000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (43/800) (7/80) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeLeft
