$( NATURAL DEDUCTION SYSTEM FOR INTUITIONISTIC PROPOSITIONAL LOGIC $)
$( This work by Victor Sannier is released under the MIT License. $)

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

$v Ga De Si Pi $.
cGa $f ctx Ga $.
cDe $f ctx De $.
cSi $f ctx Si $.
cPi $f ctx Pi $.

$( A well-formed formula is a context. $)
cf $a ctx ph $.
$( The concatenation of two contexts is a context. $)
cc $a ctx Ga , De $.

$c seq => $.
s $a seq Ga => ph $.

$(
###############################################################################
  AXIOMS
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  IDENTITY AND STRUCTURAL RULES
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c |- $.

ax-idc $a |- Ga , ps , De => ps $.

${
  ax-strl.1 $e |- T. , Ga => ph $.
  $( Truth-strengthening (left) $)
  ax-strl $a |- Ga => ph $.
$}

${
  ax-strc.1 $e |- Ga , T. , De => ph $.
  $( Truth-strengthening (center) $)
  ax-strc $a |- Ga , De => ph $.
$}

${
  ax-strr.1 $e |- Ga , T. => ph $.
  $( Truth-strengthening (right) $)
  ax-strr $a |- Ga => ph $.
$}

${
  ax-weakl.1 $e |- Ga => ps $.
  ax-weakl $a |- De , Ga => ps $.
$}

${
  ax-weakr.1 $e |- Ga => ps $.
  ax-weakr $a |- Ga , De => ps $.
$}

${
  ax-contr.1 $e |- Ga , Si , Si , De => ps $.
  $( Contraction rule $)
  ax-contr $a |- Ga , Si , De => ps $.
$}

${
  ax-exch.1 $e |- Ga , Si , Pi , De => ch $.
  $( Exchange rule $)
  ax-exch $a |- Ga , Pi , Si , De => ch $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  LOGICAL RULES
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
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
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ADDITIONAL AXIOMS AND DEFINITIONS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

${
  ax-dup.1 $e |- Ga , Ga => ph $.
  ax-dup $a |- Ga => ph $.
$}

ax-id $p |- ps => ps $=
  ( cf wtru cc ax-idc ax-strr ax-strl ) AABZACBZHDAIIEFG $.

ax-idl $p |- ps , Ga => ps $=
  ( cf cc wtru ax-idc ax-strl ) AACBDAECBFG $.

ax-idr $p |- Ga , ps => ps $=
  ( cf cc wtru ax-idc ax-strr ) ABACDABECFG $.

$c <-> $.
wb $a wff ( ph <-> ps ) $.

${
  ax-ibi.1 $e |- Ga => ( ( ph -> ps ) /\ ( ps -> ph ) ) $.
  ax-ibi $a |- Ga => ( ph <-> ps ) $.
$}

${
  ax-ebi.1 $e |- Ga => ( ph <-> ps ) $.
  ax-ebi $a |- Ga => ( ( ph -> ps ) /\ ( ps -> ph ) ) $.
$}

$(
###############################################################################
  HYPOTHETICAL DEDUCTIONS
###############################################################################
$)

$( Ex falso quodlibet sequitur $)
efq $p |- F. =>  ps $= ( wfal cf ax-id ax-efal ) ABCBDE $.

$( Ex contradictione quodlibet sequitur $)
ecq $p |- ph , ~ ph =>  ps $=
  ( cf wn cc ax-idl ax-idr ax-enot ax-efal ) BACZADZCZEZAMALFKJGHI $.

$( Modus ponens $)
mp $p |- ( ph -> ps ) , ph => ps $=
  ( wi cf cc ax-idl ax-idr ax-eim ) ABABCZDZADZEIKFAJGH $.

$( Modus tollendo ponens $)
mtp $p |- ( ph \/ ps ) , ~ ph => ps $=
  ( wo cf wn cc ax-idl ax-idr ax-idc ax-enot ax-efal ax-eor ) ABBABCZDZAEZDZFZM
  PGBNPADZFFZASAQHONRIJKBQHL $.

$( Hypothetical syllogism $)
syl $p |- ( ph -> ps ) , ( ps -> ch ) => ( ph -> ch ) $=
  ( wi cf cc ax-idc ax-idl ax-idr ax-eim ax-iim ) ACABDZEZBCDZEZFZBCMOAEZFZFZNM
  QGABSLRHAPIJJK $.

notnot $p |- ( ph \/ ~ ph ) => ( ~ ~ ph -> ph ) $=
  ( wn wo cf cc ax-idl ax-idr ax-idc ax-enot ax-efal ax-eor ax-iim ) ABZBZAAMCZ
  DZAMAPNDZEZOQFARGAPQMDZEEZMTMRGNPSHIJKL $.

$(
###############################################################################
  TAUTOLOGIES
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF NEGATION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Law of non-contradiction $)
lnc $p |- Ga => ~ ( ph /\ ~ ph ) $=
  ( wn wa cf cc ax-idr ax-eanl ax-eanr ax-enot ax-inot ) AACZDZBABMEFZALNMBGZHA
  LNOIJK $.

$( Law of contraposition $)
con $p |- Ga => ( ( ph -> ps ) -> ( ~ ps -> ~ ph ) ) $=
  ( wi wn cf cc ax-idc ax-idr ax-eim ax-enot ax-inot ax-iim ) ABDZBEZAEZDCOPCNF
  ZGZACQOFZGGZBCQSAFZGZGGZABUCNCUBHATIJORUAHKLMM $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF CONJUNCTION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

${
  jca.1 $e |- Ga => ps $.
  jca.2 $e |- Ga => ph $.
  jca $p |- Ga => ( ps /\ ph ) $= ( wa ax-ian ax-dup ) BAFCBACCDEGH $.
$}

$( Conjunction is idempotent. $)
anidm $p |- Ga => ( ( ph /\ ph ) <-> ph ) $=
  ( wa wi cf cc ax-idr ax-eanl ax-iim ax-ian ax-dup ax-ibi ) AACZABMADZAMDZCBNO
  BBMABAABMEFMBGHIAMBMBAEFZAAPPABGZQJKIJKL $.

$( Conjunction is commutative. $)
ancom $p |- Ga => ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
  ( wa cf cc ax-idr ax-eanr ax-eanl ax-ian ax-dup ax-iim ) ABDZBADZCNCMEFZBAOOA
  BOMCGZHABOPIJKL $.

$( Conjunction is associative. $)
anass $p |- Ga => ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
  ( wa wi cf cc ax-idr ax-eanl ax-eanr jca ax-iim ax-ibi ) ABEZCEZABCEZEZDRPFPR
  FDPRDQADPGHZABSOCSPDIZJZJCBSABSUAKOCSTKLLMRPDCODRGHZBAUBAQUBRDIZJBCUBAQUBUCKZ
  JLBCUBUDKLMLN $.

$( Conjunction is monotonic with respect to implication. $)
anmonl $p |- Ga => ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
  ( wi wa cf cc ax-idc ax-idr ax-eanl ax-eim ax-eanr jca ax-iim ) ABEZACFZBCFZE
  DQRDPGZHZCBDSQGZHHZABUBPDUAIACUBQTJZKLACUBUCMNOO $.

curry $p |- Ga => ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
  ( wa wi cf cc ax-idc ax-idr ax-id ax-ian ax-eim ax-iim ) ABEZCFZABCFZFDAQDPGZ
  HZBCDRAGZHHZOCDRTBGZHZHHPDUCIABUAUBASJBKLMNNN $.

uncurry $p |- Ga => ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
  ( wi wa cf cc ax-idc ax-idr ax-eanl ax-eim ax-eanr ax-iim ) ABCEZEZABFZCEDQCD
  PGZHZBCDRQGZHHZAOUAPDTIABUAQSJZKLABUAUBMLNN $.

$( Law of exportation $)
export $p |- Ga => ( ( ph -> ( ps -> ch ) ) <-> ( ( ph /\ ps ) -> ch ) ) $=
  ( wi wa uncurry curry ax-ian ax-dup ax-ibi ) ABCEEZABFCEZDLMEZMLEZFDNODDABCDG
  ABCDHIJK $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF DISJUNCTION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

truorfal $p |- Ga => ( ( T. \/ F. ) <-> T. ) $=
  ( wtru wfal wo wi cf cc ax-idr ax-strr ax-iim ax-iorl jca ax-ibi ) BCDZBABNEN
  BEANBABANFGZBOHIJBNABCABFGBAHKJLM $.

$( Disjunction is idempotent. $)
oridm $p |- Ga => ( ( ph \/ ph ) <-> ph ) $=
  ( wo wi wa cf cc ax-idr ax-eor ax-iim ax-iorl ax-ian ax-dup ax-ibi ) AACZABOA
  DZAODZEBPQBBOABAAABOFGZOBHARHZSIJAOBAABAFGABHKJLMN $.

$( Disjunction is commutative. $)
orcom $p |- Ga => ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
  ( wo cf cc ax-idr ax-iorr ax-iorl ax-eor ax-iim ) ABDZBADZCABMCLEZFZLCGBACNAE
  FFAOGHBACNBEFFBOGIJK $.

$( Disjunction is monotonic with respect to implication. $)
ormonl $p |- Ga => ( ( ph -> ps ) -> ( ( ph \/ ch ) -> ( ps \/ ch ) ) ) $=
  ( wi wo cf cc ax-idr ax-idc ax-eim ax-iorl ax-iorr ax-eor ax-iim ) ABEZACFZBC
  FZEDQRDPGZHZACRDSQGZHHZQTIBCDSUAAGHZHHZABUDPDUCJAUBIKLBCDSUACGHHHCUBIMNOO $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  COMPLEX PROPERTIES
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Conjunction implies disjunction. $)
animor $p |- Ga => ( ( ph /\ ps ) -> ( ps \/ ph ) ) $=
  ( wa wo cf cc ax-idr ax-eanr ax-iorl ax-iim ) ABDZBAECBACLFGZABMLCHIJK $.

$( Left-distributivity of conjunction over disjunction $)
andil $p |- Ga => ( ( ph /\ ( ps \/ ch ) )
  -> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
  ( wo wa cf ax-idr ax-eanr ax-eanl ax-id ax-ian ax-iorl ax-iorr ax-eor ax-iim
  cc ) ABCEZFZABFZACFZEZDBCUBDSGZQZARUDSDHZITUADUCBGZQQABUDUFARUDUEJZBKLMTUADUC
  CGZQQACUDUHUGCKLNOP $.

$( Left-distributivity of disjunction over conjunction $)
ordil $p |- Ga => ( ( ph \/ ( ps /\ ch ) )
  -> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
  ( wa wo cf ax-idr ax-iorl ax-eanl ax-iorr ax-eor ax-eanr ax-ian ax-dup ax-iim
  cc ) ABCEZFZABFZACFZEZDUBDSGZQZTUAUDUDARTUDSDHZABDUCAGQQZAUDHZIABDUCRGQQZBCUH
  RUDHZJKLARUAUDUEACUFUGIACUHBCUHUIMKLNOP $.

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
  htmldef "Si" as "&Sigma;";
  htmldef "Pi" as "&Pi;";
  htmldef "seq" as "<span class='typecode'>seq</span> ";
  htmldef "=>" as " &rArr; ";
  htmldef "|-" as " &vdash; ";
$)
