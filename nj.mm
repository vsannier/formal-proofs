$( NATURAL DEDUCTION SYSTEM FOR INTUITIONISTIC PROPOSITIONAL LOGIC $)
$( This work by Victor Sannier is licensed under CC BY 4.0. $)

$(
###############################################################################
  WELL-FORMED FORMULAS
###############################################################################
$)

$c wff $.

$c T. F. $.
wtru $a wff T. $.
wfal $a wff F. $.

$v ph ps ch $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

$c ( ) -> ~ /\ \/ $.
wi $a wff ( ph -> ps ) $.
wn $a wff ~ ph $.
wa $a wff ( ph /\ ps ) $.
wo $a wff ( ph \/ ps ) $.

$(
###############################################################################
  INTUITIONISTIC SEQUENTS
###############################################################################
$)

$c ctx , $.

$v Ga De $.
cGa $f ctx Ga $.
cDe $f ctx De $.

$( A well-formed formula is a context. $)
cf $a ctx ph $.
$( The concatenation of two contexts is a context. $)
cc $a ctx Ga , De $.

$c seq => $.
s $a seq Ga => ph $.

$(
###############################################################################
  IDENTITY AND STRUCTURAL RULES
###############################################################################
$)

$c |- $.

ax-id $a |- Ga , ps , De => ps $.

${
  ax-weak.1 $e |- Ga , De => ps $.
  $( Weakening rule $)
  ax-weak $e |- Ga , ph , De => ps $.
$}

${
  ax-contr.1 $e |- Ga , ph , ph , De => ps $.
  $( Contraction rule $)
  ax-contr $a |- Ga , ph , De => ps $.
$}

${
  ax-exch.1 $e |- Ga , ph , ps , De => ch $.
  $( Exchange rule $)
  ax-exch $a |- Ga , ps , ph , De => ch $.
$}

${
  ax-str.1 $e |- T. , Ga , T. => ph $.
  ax-str $a |- Ga => ph $.
$}

$(
###############################################################################
  LOGICAL RULES
###############################################################################
$)

${
  ax-iim.1 $e |- Ga , ph => ps $.
  ax-iim $a |- Ga => ( ph -> ps ) $.
$}

${
  ax-eim.1 $e |- Ga => ( ph -> ps ) $.
  ax-eim.2 $e |- Ga => ph $.
  ax-eim $a |- Ga => ps $.
$}

${
  ax-ian.1 $e |- Ga => ph $.
  ax-ian.2 $e |- De => ps $.
  ax-ian $a |- Ga , De => ( ph /\ ps ) $.
$}

${
  ax-eanl.1 $e |- Ga => ( ph /\ ps ) $.
  ax-eanl $a |- Ga => ph $.
$}

${
  ax-eanr.1 $e |- Ga => ( ph /\ ps ) $.
  ax-eanr $a |- Ga => ps $.
$}

${
  ax-iorl.1 $e |- Ga => ph $.
  ax-iorl $a |- Ga => ( ph \/ ps ) $.
$}

${
  ax-iorr.1 $e |- Ga => ps $.
  ax-iorr $a |- Ga => ( ph \/ ps ) $.
$}

${
  ax-eor.1 $e |- Ga => ( ph \/ ps ) $.
  ax-eor.2 $e |- Ga , ph => ch $.
  ax-eor.3 $e |- Ga , ps => ch $.
  ax-eor $a |- Ga => ch $.
$}

${
  ax-itru $a |- Ga => T. $.
$}

${
  ax-efal.1 $e |- Ga => F. $.
  $( Ex falso quodlibet sequitur $)
  ax-efal $a |- Ga => ph $.
$}

${
  ax-inot.1 $e |- Ga , ph => F. $.
  ax-inot $a |- Ga => ~ ph $.
$}

${
  ax-enot.1 $e |- Ga => ph $.
  ax-enot.2 $e |- Ga => ~ ph $.
  ax-enot $a |- Ga => F. $.
$}

$(
###############################################################################
  TAUTOLOGIES
###############################################################################
$)

$( Law of non-contradiction $)
lnc $p |- T. => ~ ( ph /\ ~ ph ) $=
  ( wn wa wtru cf cc ax-id ax-str ax-eanl ax-eanr ax-enot ax-inot )
  AABZCZDEZAONEFZAMPNPNOOFOGHZIAMPQJKL $.

$( Law of contraposition $)
con $p |- T. => ( ( ph -> ps ) -> ( ~ ps -> ~ ph ) ) $=
  ( wi wn wtru cf cc ax-id ax-str ax-eim ax-enot ax-inot ax-iim )
  ABCZBDZADZCEFZOPQNFZGZAQROFZGGZBQRTAFZGZGGZABUDNQUCHAUDAQUAGQHIJOSUBHKLMM $.

$( Conjunction is commutative. $)
ancom $p |- T. => ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
  ( wa wtru cf cc ax-id ax-str ax-eanr ax-eanl ax-ian ax-contr ax-iim )
  ABCZBACZDEZOPNEZFZNOPPFZPBAPRFZQPFZABTNTNPSFPGHIABUANUANPSGHJKLHM $.

$( Disjunction is commutative. $)
orcom $p |- T. => ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
  ( wo wtru cf cc ax-id ax-str ax-iorr ax-iorl ax-eor ax-iim )
  ABCZBACZDEZABNOMEZFZMQMOOFOGHBAOPAEFFZARAOQFZOGHIBAOPBEFFZBTBSOGHJKL $.

animor $p |- T. => ( ( ph /\ ps ) -> ( ps \/ ph ) ) $=
  ( wa wo wtru cf cc ax-id ax-str ax-eanr ax-iorl ax-iim )
  ABCZBADEFZBANMFGZABOMOMNNGNHIJKL $.

curry $p |- T. => ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
  ( wa wi wtru cf cc ax-id ax-str ax-ian ax-eim ax-iim )
  ABDZCEZABCEZEFGZAPQOGZHZBCQRAGZHHZNCQRTBGZHZHHOQUCIABUAUBAUAAQSHQIJBUBBQQIJKL
  MMM $.

$(
###############################################################################
  HYPOTHETICAL DEDUCTIONS
###############################################################################
$)

$( Modus ponens $)
mp $p |- ( ph -> ps ) , ph => ps $=
  ( wi cf cc wtru ax-id ax-str ax-eim ) ABABCZDZADZEZJMJFDZLNEGHAMANKENGHI $.

$( Modus tollendo ponens $)
mtp $p |- ( ph \/ ps ) , ~ ph => ps $=
  ( wo cf wn cc wtru ax-id ax-str ax-enot ax-efal ax-eor )
  ABBABCZDZAEZDZFZMQMGDZPRFHIBNPADZFFZATATARQFZRHIONSHJKBNPBDFFBUARHIL $.

$( Hypothetical syllogism $)
syl $p |- ( ph -> ps ) , ( ps -> ch ) => ( ph -> ch ) $=
  ( wi cf cc ax-id wtru ax-str ax-eim ax-iim )
  ACABDZEZBCDZEZFZBCMOAEZFFZNMQGABRLRLHEZOQSFFGIARASPFSGIJJK $.

notnot $p |- ( ph \/ ~ ph ) => ( ~ ~ ph -> ph ) $=
  ( wn wo cf cc wtru ax-id ax-str ax-enot ax-efal ax-eor ax-iim )
  ABZBZAAMCZDZAMAPNDZEZOROFDZQSEGHAPQADEEASREZSGHAPQMDZEEZMUBMUBMTSGHNPUAGIJKL
  $.

$(
###############################################################################
  TYPESETTING
###############################################################################
$)

$( $t
  htmldef "wff" as "<span class='typecode'>wff</span> ";
  htmldef "(" as "(";
  htmldef ")" as ")";
  htmldef "->" as " &rarr; ";
  htmldef "~" as "&not;";
  htmldef "/\" as " &and; ";
  htmldef "\/" as " &or; ";
  htmldef "T." as "&top;";
  htmldef "F." as "&bot;";
  htmldef "ph" as "&phi;";
  htmldef "ps" as "&psi;";
  htmldef "ch" as "&chi;";
  htmldef "cs" as "&ctx;";
  htmldef "ctx" as "<span class='typecode'>ctx</span> ";
  htmldef "," as ", ";
  htmldef "Ga" as "&Gamma;";
  htmldef "De" as "&Delta;";
  htmldef "seq" as "<span class='typecode'>seq</span> ";
  htmldef "=>" as " &rArr; ";
  htmldef "|-" as " &vdash; ";
$)
