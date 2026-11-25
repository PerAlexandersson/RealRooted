/-
Based on the certificate from scripts/gen_big_descents_certificate.py.
-/
module

public import RealRooted.CombinatorialExamples.BigDescents321.Certificate.Reflect
meta import RealRooted.CombinatorialExamples.BigDescents321.Certificate.Reflect
import Mathlib.Data.Nat.Choose.Basic
meta import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Eval

/-!
# Data of the universal kernel certificate

The reflected polynomials of the certificate in issue #1143, §11, with their kernel checks:

* `htildeE`, the polynomial `Htilde(R, X, k)`, built from `N = dP`, the numerator `p₀` and `L`;
* `htData`, the expanded coefficients of `Htilde`, split by the degree in `X`;
* `pplusE`, the polynomial `P₊(S, X, K, T)` with natural-number coefficients, split the same way;
* `htilde_check`: `Htilde` equals its expansion;
* `chunk_check_*`: `27720 R¹² Htilde = P₊(R - 7, X, k, R - k)`, one `X`-degree at a time;
* `prest_posB`: every coefficient of `P₊` other than `h₀₀₀ T¹²` is nonnegative.

The expanded coefficients and Horner trees are computed once and quoted as literal data.
These producers are untrusted: all polynomial identities and coefficient signs below are
still checked by kernel reduction. The quoted values agree with the original certificate.
-/

@[expose] public section

namespace RealRooted.BigDescents321.CertData

open Lean.Grind.CommRing RealRooted.BigDescents321.Reflect

/-- The variable `R`. -/
abbrev vR : Expr := .var 0
/-- The variable `X`. -/
abbrev vX : Expr := .var 1
/-- The variable `k`. -/
abbrev vk : Expr := .var 2
/-- An integer constant. -/
abbrev c (z : ℤ) : Expr := .num z

/-- `F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`. -/
def fE (r J k : Expr) : Expr :=
  .sub (.mul k (.add (.add (.add (.mul (c 4) J) (.mul (c 3) k)) (.mul (c 2) r)) (c 5)))
    (.mul r (.sub r (c 1)))

/-- The affine form `aR + bX + dk + e`. -/
def lin (a b d e : ℤ) : Expr :=
  .add (.add (.add (.mul (c a) vR) (.mul (c b) vX)) (.mul (c d) vk)) (c e)

/-- `A = (X + 3)(2X + 7)`. -/
def aE : Expr := .mul (lin 0 1 0 3) (lin 0 2 0 7)
/-- `B = (X + 2)(2X + 3)`. -/
def bE : Expr := .mul (lin 0 1 0 2) (lin 0 2 0 3)

/-- `N = dP`, an integer polynomial of total degree `10`. -/
def nE : Expr :=
  .add (.sub (.sub
    (List.foldr .mul (fE (.sub vR (c 1)) (.add vX (c 2)) vk)
      [aE, lin 1 0 (-1) 0, lin 1 2 1 2, lin 1 2 1 3, lin 1 2 1 4, lin 1 0 1 (-3), lin 1 2 1 1])
    (List.foldr .mul (fE (.sub vR (c 2)) (.add vX (c 2)) vk)
      [c 2, aE, lin 1 0 (-1) 0, lin 1 0 (-1) (-1), lin 1 2 1 2, lin 1 2 1 3, lin 1 1 1 2,
        lin 1 2 1 1]))
    (.mul bE (.mul (fE vR vX vk) (List.foldr .mul (c 1)
      [lin 1 0 1 (-3), lin 1 0 1 (-2), lin 0 2 2 5, lin 0 2 2 7, lin 1 1 1 2, lin 1 2 1 1]))))
    (List.foldr .mul (fE (.sub vR (c 1)) vX vk)
      [c 2, bE, lin 1 0 (-1) 0, lin 1 1 1 1, lin 1 0 1 (-3), lin 0 2 2 5, lin 0 2 2 7,
        lin 1 1 1 2])

/-- The terms of the certificate numerator `p₀`. -/
def p0Data : List (ℕ × ℕ × ℕ × ℤ) := [
  (0, 0, 0, 15449954510176233842643298149689032078124010229946269631908394970484),
  (0, 0, 1, -4975430576327197412754389785985456704349295885091901703813063962016),
  (0, 1, 0, -984117879732142942198493741603180347372822861017392544849349186510),
  (1, 0, 0, -5437232454232154238233874368950894658952205841815344162493404153240),
  (0, 0, 2, -399291884922375327511342123411851014298113706362569838451312231696),
  (0, 1, 1, -2393348714854229382252785920035641554207437435619534717356981181919),
  (0, 2, 0, -332877344654181477336311885918265231672850201144120850758359686733),
  (1, 0, 1, 1996709063952664204486460892563449153808812801694713612974382381068),
  (1, 1, 0, 746110788603982048305994148366198853356874058011389464214765253790),
  (2, 0, 0, 570202392213267832840779847620287437866323737199180394358613592092),
  (0, 0, 3, 17210495210916633798631790359936548900589862292875370710947070424),
  (0, 1, 2, -193829683270101777887668488917867471895357746622447542732024797050),
  (0, 2, 1, 434016348589765273292573187949828949761341978670666033537842111441),
  (0, 3, 0, -30015455847680751915564795248451912074834200314184618239585285237),
  (1, 0, 2, 93240456651409156362243293379415957688355973449066884766273039204),
  (1, 1, 1, 653114118772775310140105464198837027286000598260145752690530393898),
  (1, 2, 0, 30179277881403864581091753311190628692571600607164499867494462599),
  (2, 0, 1, -275154345793401454009643685808163481443127054641590986071118898500),
  (2, 1, 0, -97342395518294793995692164519890298367317196945018920433534847820),
  (3, 0, 0, -3992483943974889493522422751108656736963436313348778217159209620),
  (0, 0, 4, 9755470371303732996106779621095952476812586404439128851181184280),
  (0, 1, 3, -761639989326350032149575095547311503060815810920655458536740685),
  (0, 2, 2, -264413706551650397724872196819037066147694927678410107387816134940),
  (0, 3, 1, 12205879514974516420243472176316278281785688334030912449532062858),
  (0, 4, 0, -254859965528408460388476503343360142185717560316170719475774604),
  (1, 0, 3, -14435732900592152545457848943689879176795032988381017698938267780),
  (1, 1, 2, 36293004091619792215809279017771347442128679620800933040777627860),
  (1, 2, 1, 14657688533293942899954795127358059702284825494447429053126565880),
  (1, 3, 0, 24257102583156324708937224627731275497844655046689278547808570540),
  (2, 0, 2, 1413200328839950411078313274264499700313088473267581857704311100),
  (2, 1, 1, -59900599874564067988892170342334975769905144473481504374233491040),
  (3, 0, 1, 7194084075620136979565964576698722846501053660655057380427753740),
  (4, 0, 0, -403987241920228353831022324834163000618792813480033837138110080),
  (0, 0, 5, 527993678497307638806603517454626641890950400204605331136438180),
  (0, 1, 4, 1086187383657769603083418262623571841426197812201222995686387040),
  (0, 2, 3, -19661231622500050762692078455601790776669007233620700617144906640),
  (0, 3, 2, 2563741539350553030382939073361320188480798830717932117597057340),
  (0, 4, 1, -18885972156281012186417921007683517124996974030971700442452619248),
  (0, 5, 0, 661027966817030767947348972975804631626921072535439478259200000),
  (1, 0, 4, 470324152673512462356071908226339061255186121946767419779246880),
  (1, 1, 3, 13611002390649082259438913915289386802840441829296352470512361680),
  (1, 2, 2, 87669655564071635513294408777712714410067835283387176199228028360),
  (1, 3, 1, -14723384728918973626053204077188408693952751250770418649898410820),
  (1, 4, 0, 6447793801078969622673142562756725620896430456385444303715590116),
  (2, 0, 3, 2239445694540309725940460977394728293215157993143474134934561200),
  (2, 1, 2, -1781556441921743887166015293233983040129295379164329112590609000),
  (2, 2, 1, -53436016278846624032597342554128904926151770710189524914645470880),
  (3, 0, 2, -1328096076680852154536816847192175678075333136371171534750993440),
  (3, 1, 1, -8533171807961718573841055936032161825966658193985482269753175940),
  (3, 2, 0, 8831467563695891385281129944972628830619885775061604911812205140),
  (4, 0, 1, -433801324650673360816405959736655580663061815625008551981241300),
  (4, 1, 0, 2874800643410684677567463145388328354229689546169593203582141260),
  (5, 0, 0, 144599523455826096618290948594200504936810012262402106994471740),
  (0, 1, 5, -189295784486172074399431006867490360684884385895744656357902254),
  (0, 2, 4, 3962858336256752135356364485105241704594176547823957570845278507),
  (0, 3, 3, 1156791544090965100629572513190464062465033899746571207696773820),
  (0, 4, 2, 3443009396987940107984715395266369616517715730243444416262033940),
  (0, 5, 1, -1322055933634061535894697945951609263253842145070878956518400000),
  (1, 1, 4, 3126925047792475154162743674091184115767929643589662156516667138),
  (1, 2, 3, 5868997397615299234374266363554870870657517876937548489676480960),
  (1, 3, 2, 11400631942372139755052578754622147924701078165057404585254085740),
  (1, 4, 1, -2479155781002926882350051348139674063000975860037791779984499240),
  (1, 5, 0, 220342655605676922649116324325268210542307024178479826086400000),
  (2, 1, 3, -1544748314452589303525355949748808124329326187957569550041630724),
  (2, 2, 2, -3483052757070762599968240727001406908884359390512308695871637600),
  (2, 3, 1, -9088854983989873356680437312080826000828039195325366379784652880),
  (2, 4, 0, 2327025014435578625289651931428887242274145588159914288309340),
  (3, 1, 2, 418299530258015221567657347831859445588252571764601938466606540),
  (3, 3, 0, 1356281689472211455515746856760201822751062900665577172129454860),
  (4, 1, 1, -268370124534327430512599258898784757577371536000157571803941740),
  (4, 2, 0, -187920266689499715091873774933575268055743462634792356301971020),
  (5, 1, 0, -411765337663108749200536131082844968450936251433534174998960),
  (0, 2, 5, 123942743778193268990127932432963368430047701100394902173600000),
  (0, 3, 4, 319139385316421915085855439087166008366309967943372937319977800),
  (0, 4, 3, 718163161700982177860456475117603436852120256259644576038131780),
  (0, 5, 2, 661027966817030767947348972975804631626921072535439478259200000),
  (1, 2, 4, 289199735482450960976965175676914526336777969234254771738400000),
  (1, 3, 3, 1553678160517133264029722482277500265471625787964920975883698760),
  (1, 4, 2, 1123593303730028331664638872631840186018386208393322177162379520),
  (1, 5, 1, -220342655605676922649116324325268210542307024178479826086400000),
  (2, 2, 3, 137714159753548076655697702703292631588941890111549891304000000),
  (2, 3, 2, -545794266501651879324927363261797489218558056565698991211664960),
  (2, 4, 1, -514498379412258695034728421078217480458392039683123999538102700),
  (3, 2, 2, -82628495852128845993418621621975578953365134066929934782400000),
  (3, 3, 1, 28415251152748342396753385487283885138904324896166646822210840),
  (3, 4, 0, 27370689251017680235319918412279410528302200659670540896670000),
  (4, 2, 1, -41314247926064422996709310810987789476682567033464967391200000),
  (4, 3, 0, -23994626624659449136105489230508191664899290223585895311352440),
  (5, 2, 0, 13771415975354807665569770270329263158894189011154989130400000)]

/-- The certificate denominator `L`. -/
def lden : ℤ := 3442853993838701916392442567582315789723547252788747282600000

/-- `Htilde = 2LN - (R - k)(R + k - 3)(R + 2X + k + 1) p₀(k + 1)
+ 2k(2X + 2k + 7)(R + X + k + 2) p₀(k)`. -/
def htildeE : Expr :=
  .add (.sub (.mul (.mul (c 2) (c lden)) nE)
    (List.foldr .mul (termsExpr vR vX (.add vk (c 1)) p0Data)
      [lin 1 0 (-1) 0, lin 1 0 1 (-3), lin 1 2 1 1]))
    (List.foldr .mul (termsExpr vR vX vk p0Data) [c 2, vk, lin 0 2 2 7, lin 1 1 1 2])

/-- Expand once with the core normalizer; the exported data are still literal lists. -/
private def monomialDegrees : Mon → ℕ × ℕ × ℕ
  | .unit => (0, 0, 0)
  | .mult p m =>
    let (a, b, d) := monomialDegrees m
    (a + if p.x = 0 then p.k else 0, b + if p.x = 1 then p.k else 0,
      d + if p.x = 2 then p.k else 0)

private def polynomialTerms : Poly → List (ℕ × ℕ × ℕ × ℤ)
  | .num z => if z = 0 then [] else [(0, 0, 0, z)]
  | .add z m p =>
    let (a, b, d) := monomialDegrees m
    (a, b, d, z) :: polynomialTerms p

private def sortTerms (ts : List (ℕ × ℕ × ℕ × ℤ)) :=
  ts.mergeSort fun (a, b, d, _) (a', b', d', _) =>
    a < a' || (a == a' && (b < b' || (b == b' && d ≤ d')))

/-- Evaluate private producers but export only their quoted, kernel-readable values. -/
local elab "quoteWitness% " t:term : term => Lean.withoutExporting do
  Lean.Elab.Term.elabTerm (← `(eval% $t)) none

private def expandedTerms : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% sortTerms (polynomialTerms htildeE.toPoly)

/-- The terms of `Htilde` of degree `0` in `X`. -/
def ht0 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 0

/-- The terms of `Htilde` of degree `1` in `X`. -/
def ht1 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 1

/-- The terms of `Htilde` of degree `2` in `X`. -/
def ht2 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 2

/-- The terms of `Htilde` of degree `3` in `X`. -/
def ht3 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 3

/-- The terms of `Htilde` of degree `4` in `X`. -/
def ht4 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 4

/-- The terms of `Htilde` of degree `5` in `X`. -/
def ht5 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 5

/-- The terms of `Htilde` of degree `6` in `X`. -/
def ht6 : List (ℕ × ℕ × ℕ × ℤ) :=
  quoteWitness% expandedTerms.filter fun (_, x, _, _) => x == 6

/-- All terms of `Htilde`. -/
def htData : List (ℕ × ℕ × ℕ × ℤ) :=
  ht0 ++ ht1 ++ ht2 ++ ht3 ++ ht4 ++ ht5 ++ ht6

/-- The variable `S` of `P₊`. -/
abbrev aS : Expr := .var 0
/-- The variable `X` of `P₊`. -/
abbrev aX : Expr := .var 1
/-- The variable `K` of `P₊`. -/
abbrev aK : Expr := .var 2
/-- The variable `T` of `P₊`. -/
abbrev aT : Expr := .var 3

/-- The distinguished positive term `h₀₀₀ T¹²` of `P₊`. -/
def pTop : Expr := .mul (c 439806921759901945458935271868220264473959012718829971494799100139356160)
  (.pow aT 12)

/-- Homogenize the shifted polynomial in degree twelve, collecting equal monomials. -/
private def positiveTerms : List ((ℕ × ℕ × ℕ × ℕ) × ℤ) := quoteWitness% Id.run do
  let mut terms : Std.HashMap (ℕ × ℕ × ℕ × ℕ) ℤ := {}
  for (a, b, d, z) in htData do
    for j in List.range (a + d + 1) do
      for i in List.range (13 - d) do
        let i := i + d
        let key := (j, b, i, 12 - i)
        let value := z * (Nat.choose (a + d) j : ℤ) * 7 ^ (a + d - j) *
          (27720 / (Nat.choose 12 d : ℤ)) * (Nat.choose i d : ℤ) * Nat.choose 12 i
        terms := terms.insert key (terms.getD key 0 + value)
  return terms.toList.filter fun (_, z) => z != 0

/-- Horner's rule, in the original variable order `X, S, K, T`. -/
private def horner : List ℕ → List (List ℕ × ℤ) → Expr
  | [], ts => .num (ts.headD ([], 0)).2
  | v :: vs, ts => Id.run do
    let powers := ((ts.map fun t => t.1.headD 0).mergeSort (· ≥ ·)).eraseDups
    let mut acc : Option (Expr × ℕ) := none
    for e in powers do
      let coefficient := horner vs
        ((ts.filter fun t => t.1.headD 0 == e).map fun t => (t.1.tail, t.2))
      acc := some <| match acc with
        | none => (coefficient, e)
        | some (previous, n) =>
          (.add (.mul previous (if n - e = 1 then .var v else .pow (.var v) (n - e)))
            coefficient, e)
    let (result, e) := acc.getD (.num 0, 0)
    return if e = 0 then result
      else .mul result (if e = 1 then .var v else .pow (.var v) e)

private def positiveChunk (b : ℕ) : Expr :=
  horner [1, 0, 2, 3] <| positiveTerms.filterMap fun ((a, x, k, t), z) =>
    if x = b ∧ (a, x, k, t) ≠ (0, 0, 0, 12) then some ([x, a, k, t], z) else none

/-- Quote a reflected expression without adding any exported producer dependency. -/
private meta def quoteExpression : Expr → Lean.Expr
  | .num z => Lean.mkApp (Lean.mkConst ``Expr.num) (Lean.toExpr z)
  | .natCast n => Lean.mkApp (Lean.mkConst ``Expr.natCast) (Lean.toExpr n)
  | .intCast z => Lean.mkApp (Lean.mkConst ``Expr.intCast) (Lean.toExpr z)
  | .var n => Lean.mkApp (Lean.mkConst ``Expr.var) (Lean.toExpr n)
  | .neg a => Lean.mkApp (Lean.mkConst ``Expr.neg) (quoteExpression a)
  | .add a b => Lean.mkApp2 (Lean.mkConst ``Expr.add) (quoteExpression a) (quoteExpression b)
  | .sub a b => Lean.mkApp2 (Lean.mkConst ``Expr.sub) (quoteExpression a) (quoteExpression b)
  | .mul a b => Lean.mkApp2 (Lean.mkConst ``Expr.mul) (quoteExpression a) (quoteExpression b)
  | .pow a n => Lean.mkApp2 (Lean.mkConst ``Expr.pow) (quoteExpression a) (Lean.toExpr n)

local elab "quoteExpression% " t:term : term => Lean.withoutExporting do
  let e ← Lean.Elab.Term.elabTerm (← `(quoteExpression $t)) (some (Lean.mkConst ``Lean.Expr))
  unsafe Lean.Meta.evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) e

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `0` in `X`. -/
def pp0 : Expr :=
  quoteExpression% positiveChunk 0

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `1` in `X`. -/
def pp1 : Expr :=
  quoteExpression% positiveChunk 1

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `2` in `X`. -/
def pp2 : Expr :=
  quoteExpression% positiveChunk 2

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `3` in `X`. -/
def pp3 : Expr :=
  quoteExpression% positiveChunk 3

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `4` in `X`. -/
def pp4 : Expr :=
  quoteExpression% positiveChunk 4

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `5` in `X`. -/
def pp5 : Expr :=
  quoteExpression% positiveChunk 5

/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `6` in `X`. -/
def pp6 : Expr :=
  quoteExpression% positiveChunk 6

/-- `P₊ - h₀₀₀ T¹²`. -/
def prestE : Expr :=
  .add pp0 (.add pp1 (.add pp2 (.add pp3 (.add pp4 (.add pp5 pp6)))))

/-- `P₊(S, X, K, T)`, a polynomial with natural-number coefficients. -/
def pplusE : Expr := .add pTop prestE

/-- The substitution `S = R - 7`, `X = X`, `K = k`, `T = R - k`. -/
def σ : ℕ → Expr
  | 0 => .sub vR (c 7)
  | 1 => vX
  | 2 => vk
  | _ => .sub vR vk

/-! ### Kernel checks -/

theorem htilde_check : check htildeE (termsExpr vR vX vk htData) = true := by
  decide +kernel

theorem chunk_check_0 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht0)))
      (subst σ (.add pTop pp0)) = true := by
  decide +kernel

theorem chunk_check_1 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht1)))
      (subst σ pp1) = true := by
  decide +kernel

theorem chunk_check_2 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht2)))
      (subst σ pp2) = true := by
  decide +kernel

theorem chunk_check_3 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht3)))
      (subst σ pp3) = true := by
  decide +kernel

theorem chunk_check_4 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht4)))
      (subst σ pp4) = true := by
  decide +kernel

theorem chunk_check_5 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht5)))
      (subst σ pp5) = true := by
  decide +kernel

theorem chunk_check_6 :
    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht6)))
      (subst σ pp6) = true := by
  decide +kernel

theorem prest_posB : PosB prestE = true := by
  decide +kernel

end RealRooted.BigDescents321.CertData
