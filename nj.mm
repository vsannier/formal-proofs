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
$( The negation of a wff is a wff. $)
wn $a wff ~ ph $.
$( The conjunction of two wff is a wff. $)
wa $a wff ( ph /\ ps ) $.
$( The disjunction of two wff is a wff. $)
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
  STRUCTURAL AND IDENTITY RULES
###############################################################################
$)

$c |- $.

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

ax-idc $a |- Ga , ps , De => ps $.

ax-id $p |- ps => ps $=
  ( cf wtru ax-idc ax-str ) AABACBZFDE $.
ax-idl $p |- ps , Ga => ps $=
  ( cf cc wtru ax-idc ax-str ) AACBDAECZBHDFG $.
ax-idr $p |- Ga , ps => ps $=
  ( cf cc wtru ax-idc ax-str ) ABACDAECZBDHFG $.

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

ax-itru $a |- Ga => T. $.

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

$( Not true implies false. $)
nottru $p |- T. => ( ~ T. -> F. ) $=
  ( wtru wn wfal cf cc ax-idl ax-idr ax-enot ax-iim ) ABZCADZAKJDZEALFJKGHI $.

$( Law of non-contradiction $)
lnc $p |- T. => ~ ( ph /\ ~ ph ) $=
  ( wn wa wtru cf cc ax-idr ax-eanl ax-eanr ax-enot ax-inot ) AABZCZDEZANMEFZAL
  OMNGZHALOPIJK $.

$( Law of contraposition $)
con $p |- T. => ( ( ph -> ps ) -> ( ~ ps -> ~ ph ) ) $=
  ( wi wn wtru cf cc ax-idc ax-idr ax-eim ax-enot ax-inot ax-iim ) ABCZBDZADZCE
  FZOPQNFZGZAQROFZGGZBQRTAFZGZGGZABUDNQUCHAUAIJOSUBHKLMM $.

$( Conjunction is commutative. $)
ancom $p |- T. => ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
  ( wa wtru cf cc ax-idc ax-str ax-eanr ax-eanl ax-ian ax-contr ax-iim ) ABCZBA
  CZDEZOPNEZFZNOPPFZPBAPRFZQPFZABTNTNPSFPGHIABUANUANPSGHJKLHM $.

$( Disjunction is commutative. $)
orcom $p |- T. => ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
  ( wo wtru cf cc ax-idr ax-iorr ax-iorl ax-eor ax-iim ) ABCZBACZDEZABMNLEZFZLN
  GBANOAEFFAPGHBANOBEFFBPGIJK $.

animor $p |- T. => ( ( ph /\ ps ) -> ( ps \/ ph ) ) $=
  ( wa wo wtru cf cc ax-idr ax-eanr ax-iorl ax-iim ) ABCZBADEFZBAMLFGZABNLMHIJK
  $.

$( Left-distributivity of conjunction over disjunction $)
andil $p |- T. => ( ( ph /\ ( ps \/ ch ) )
  -> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
  ( wo wa wtru cf ax-idr ax-eanr ax-eanl ax-ian ax-contr ax-iorl ax-iorr ax-eor
  cc ax-iim ) ABCDZEZABEZACEZDZFGZBCUBUCSGZPZARUESUCHZITUAUCUDBGZPZPSTUCUGABUEU
  HARUEUFJZBUDHKLMTUAUCUDCGZPZPSUAUCUJACUEUKUICUDHKLNOQ $.

curry $p |- T. => ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
  ( wa wi wtru cf cc ax-idc ax-str ax-ian ax-eim ax-iim ) ABDZCEZABCEZEFGZAPQOG
  ZHZBCQRAGZHHZNCQRTBGZHZHHOQUCIABUAUBAUAAQSHQIJBUBBQQIJKLMMM $.

$(
###############################################################################
  HYPOTHETICAL DEDUCTIONS
###############################################################################
$)

$( Modus ponens $)
mp $p |- ( ph -> ps ) , ph => ps $=
  ( wi cf cc ax-idl ax-idr ax-eim ) ABABCZDZADZEIKFAJGH $.

$( Modus tollendo ponens $)
mtp $p |- ( ph \/ ps ) , ~ ph => ps $=
  ( wo cf wn cc ax-idl ax-idr ax-idc ax-enot ax-efal ax-eor ) ABBABCZDZAEZDZFZM
  PGBNPADZFFZASAQHONRIJKBQHL $.

$( Hypothetical syllogism $)
syl $p |- ( ph -> ps ) , ( ps -> ch ) => ( ph -> ch ) $=
  ( wi cf cc ax-idc wtru ax-str ax-eim ax-iim ) ACABDZEZBCDZEZFZBCMOAEZFFZNMQGA
  BRLRLHEZOQSFFGIARASPFSGIJJK $.

notnot $p |- ( ph \/ ~ ph ) => ( ~ ~ ph -> ph ) $=
  ( wn wo cf cc ax-idl ax-idr ax-idc ax-enot ax-efal ax-eor ax-iim ) ABZBZAAMCZ
  DZAMAPNDZEZOQFARGAPQMDZEEZMTMRGNPSHIJKL $.

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
