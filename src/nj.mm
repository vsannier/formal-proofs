$( NATURAL DEDUCTION SYSTEM FOR INTUITIONISTIC PROPOSITIONAL LOGIC $)
$( This work by Victor SANNIER is released under the MIT License. $)

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
$( $j syntax '|-' as 'wff'; $)

$( Identity (center) $)
ax-idc $a |- Ga , ps , De => ps $.

${
  ax-strl.1 $e |- T. , Ga => ph $.
  $( Truth-strengthening rule (left) $)
  ax-strl $a |- Ga => ph $.
$}

${
  ax-strc.1 $e |- Ga , T. , De => ph $.
  $( Truth-strengthening rule (center) $)
  ax-strc $a |- Ga , De => ph $.
$}

${
  ax-strr.1 $e |- Ga , T. => ph $.
  $( Truth-strengthening rule (right) $)
  ax-strr $a |- Ga => ph $.
$}

${
  ax-weakl.1 $e |- Ga => ps $.
  $( Context weakening rule (left) $)
  ax-weakl $a |- De , Ga => ps $.
$}

${
  ax-weakr.1 $e |- Ga => ps $.
  $( Context weakening rule (right) $)
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
  $( Implication introduction rule $)
  ax-iim $a |- Ga => ( ph -> ps ) $.
$}

${
  ax-eim.1 $e |- Ga => ( ph -> ps ) $.
  ax-eim.2 $e |- Ga => ph $.
  $( Implication elimination rule $)
  ax-eim $a |- Ga => ps $.
$}

${
  ax-ian.1 $e |- Ga => ph $.
  ax-ian.2 $e |- De => ps $.
  $( Conjunction introduction rule $)
  ax-ian $a |- Ga , De => ( ph /\ ps ) $.
$}

${
  ax-eanl.1 $e |- Ga => ( ph /\ ps ) $.
  $( Conjunction elimination rule (left) $)
  ax-eanl $a |- Ga => ph $.
$}

${
  ax-eanr.1 $e |- Ga => ( ph /\ ps ) $.
  $( Conjunction elimination rule (right) $)
  ax-eanr $a |- Ga => ps $.
$}

${
  ax-iorl.1 $e |- Ga => ph $.
  $( Disjunction introduction rule (left) $)
  ax-iorl $a |- Ga => ( ph \/ ps ) $.
$}

${
  ax-iorr.1 $e |- Ga => ps $.
  $( Disjunction introduction rule (right) $)
  ax-iorr $a |- Ga => ( ph \/ ps ) $.
$}

${
  ax-eor.1 $e |- Ga => ( ph \/ ps ) $.
  ax-eor.2 $e |- Ga , ph => ch $.
  ax-eor.3 $e |- Ga , ps => ch $.
  $( Disjunction elimination rule $)
  ax-eor $a |- Ga => ch $.
$}

$( Verum introduction rule $)
ax-itru $a |- Ga => T. $.

${
  ax-efal.1 $e |- Ga => F. $.
  $( Falsum elimination rule $)
  ax-efal $a |- Ga => ph $.
$}

${
  ax-inot.1 $e |- Ga , ph => F. $.
  $( Negation introduction rule $)
  ax-inot $a |- Ga => ~ ph $.
$}

${
  ax-enot.1 $e |- Ga => ph $.
  ax-enot.2 $e |- Ga => ~ ph $.
  $( Negation elimination rule $)
  ax-enot $a |- Ga => F. $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ADDITIONAL RULES AND DEFINITIONS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

${
  dup.1 $e |- Ga , Ga => ph $.
  dup $p |- Ga => ph $=
    ( wtru cf cc ax-weakr ax-weakl ax-contr ax-strr ax-strl ) ABADEZBFALLBABBLF
    FLABBFLCGHIJK $.
$}

id $p |- ps => ps $=
  ( cf cc ax-idc dup ) AABZAFFCZAFGDEE $.

idl $p |- ps , Ga => ps $=
  ( cf cc ax-idc dup ) AACBDZAGBEF $.

idr $p |- Ga , ps => ps $=
  ( cf cc ax-idc dup ) ABACDZABGEF $.

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
efq $p |- F. => ps $=
  ( wfal cf id ax-efal ) ABCBDE $.

$( Ex contradictione quodlibet sequitur $)
ecq $p |- ph , ~ ph => ps $=
  ( cf wn cc idl idr ax-enot ax-efal ) BACZADZCZEZAMALFKJGHI $.

$( Modus ponens $)
mp $p |- ( ph -> ps ) , ph => ps $=
  ( wi cf cc idl idr ax-eim ) ABABCZDZADZEIKFAJGH $.

$( Modus tollendo ponens $)
mtp $p |- ( ph \/ ps ) , ~ ph => ps $=
  ( wo cf wn cc idl idr ax-idc ax-enot ax-efal ax-eor ) ABBABCZDZAEZDZFZMPGBNPA
  DZFFZASAQHONRIJKBQHL $.

$( Hypothetical syllogism $)
syl $p |- ( ph -> ps ) , ( ps -> ch ) => ( ph -> ch ) $=
  ( wi cf cc ax-idc idl idr ax-eim ax-iim ) ACABDZEZBCDZEZFZBCMOAEZFZFZNMQGABSL
  RHAPIJJK $.

enotnot $p |- ( ph \/ ~ ph ) => ( ~ ~ ph -> ph ) $=
  ( wn wo cf cc idl idr ax-idc ax-enot ax-efal ax-eor ax-iim ) ABZBZAAMCZDZAMAP
  NDZEZOQFARGAPQMDZEEZMTMRGNPSHIJKL $.

$(
###############################################################################
  TAUTOLOGIES
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF IMPLICATION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Positive paradox $)
simp $p |- Ga => ( ph -> ( ps -> ph ) ) $=
  ( wi cf cc ax-idc ax-iim ) ABADCBACAEFACBEGHH $.

$( Frege's theorem $)
frege $p |- Ga => ( ( ph -> ( ps -> ch ) )
  -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
  ( wi cf cc ax-idc idr ax-eim ax-iim ) ABCEZEZABEZACEZEDNODMFZGZACDPNFZGGZBCDP
  RAFZGZGGZALUBMDUAHASIZJABUBNQTHUCJJKKK $.

biid $p |- Ga => ( ph <-> ph ) $=
  ( wi wa idr ax-iim ax-ian dup ax-ibi ) AABAACZJDBJJBBAABABEFZKGHI $.

bicom $p |- Ga => ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
  ( wb cf cc ax-idc ax-ebi ax-eanr idr ax-eim ax-iim ax-eanl ax-ian ax-ibi dup
  wi ) ABDZBADZCSCREZFZBACTUAFFBAQZABQZUAUABAUABACTBEZFFZUCUBUEABUERCUDGHIBUAJK
  LABUAABCTAEZFFZUCUBUGABUGRCUFGHMAUAJKLNOPL $.

bitr $p |- Ga => ( ( ph <-> ps ) -> ( ( ps <-> ch ) -> ( ph <-> ch ) ) ) $=
  ( wb wi cf ax-idc ax-ebi ax-eanl idr ax-eim ax-iim ax-eanr ax-ian dup ax-ibi
  cc wa ) ABEZBCEZACEZFDUAUBDTGZRZACDUCUAGZRRZACFZCAFZSUFUGUHUFUFACUFBCDUCUEAGZ
  RZRRZBCFZCBFZUKBCUKUAUDUIHIJABUKABFZBAFZUKABUKTDUJHIJAUFKLLMCAUFBADUCUECGZRZR
  RZUNUOURABURTDUQHINCBURULUMURBCURUAUDUPHINCUFKLLMOPQMM $.

$( Biconditional implies forward implication. $)
biimp $p |- Ga => ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
  ( wb wi cf cc ax-idc ax-ebi ax-eanl idr ax-eim ax-iim ) ABDZABEZCABCNFZGZABCP
  AFZGGZOBAESABSNCRHIJAQKLMM $.

$( Biconditional implies reverse implication. $)
biimpr $p |- Ga => ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
  ( wb wi cf cc ax-idc ax-ebi ax-eanr idr ax-eim ax-iim ) ABDZBAEZCBACNFZGZBACP
  BFZGGZABEOSABSNCRHIJBQKLMM $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF NEGATION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Law of non-contradiction $)
lnc $p |- Ga => ~ ( ph /\ ~ ph ) $=
  ( wn wa cf cc idr ax-eanl ax-eanr ax-enot ax-inot ) AACZDZBABMEFZALNMBGZHALNO
  IJK $.

$( Law of contraposition $)
con $p |- Ga => ( ( ph -> ps ) -> ( ~ ps -> ~ ph ) ) $=
  ( wi wn cf cc ax-idc idr ax-eim ax-enot ax-inot ax-iim ) ABDZBEZAEZDCOPCNFZGZ
  ACQOFZGGZBCQSAFZGZGGZABUCNCUBHATIJORUAHKLMM $.

con2 $p |- Ga => ( ( ph -> ~ ps ) -> ( ps -> ~ ph ) ) $=
  ( wn wi cf cc ax-idc idr ax-eim ax-enot ax-inot ax-iim ) ABDZEZBADZECBPCOFZGZ
  ACQBFZGGZBCQSAFZGZGGZBRUAHANUCOCUBHATIJKLMM $.

$( Double negation introduction $)
inotnot $p |- Ga => ( ph -> ~ ~ ph ) $=
  ( wn cf cc ax-idc idr ax-enot ax-inot ax-iim ) AACZCBKBADZEZABLKDZEEABNFKMGHI
  J $.

$( A weak version of the law of excluded middle. $)
exmidw $p |- Ga => ~ ~ ( ph \/ ~ ph ) $=
  ( wn wo cf cc idr ax-iorl ax-idc ax-enot ax-inot ax-iorr ) AACZDZCZBNBOEZFZAM
  QAQNBPAEZFFZAMSAQGHOBRIJKLOBGJK $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF CONJUNCTION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

${
  jca.1 $e |- Ga => ps $.
  jca.2 $e |- Ga => ph $.
  jca $p |- Ga => ( ps /\ ph ) $=
    ( wa ax-ian dup ) BAFCBACCDEGH $.
$}

$( Conjunction is idempotent. $)
anidm $p |- Ga => ( ( ph /\ ph ) <-> ph ) $=
  ( wa wi cf cc idr ax-eanl ax-iim jca ax-ibi ) AACZABALDLADBLABAABLEFLBGHIALBA
  ABAEFABGZMJIJK $.

$( Conjunction is commutative. $)
ancom $p |- Ga => ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
  ( wa cf cc idr ax-eanr ax-eanl jca ax-iim ) ABDZBADCABCLEFZABMLCGZHABMNIJK $.

$( Conjunction is associative. $)
anass $p |- Ga => ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
  ( wa wi cf cc idr ax-eanl ax-eanr jca ax-iim ax-ibi ) ABEZCEZABCEZEZDRPFPRFDP
  RDQADPGHZABSOCSPDIZJZJCBSABSUAKOCSTKLLMRPDCODRGHZBAUBAQUBRDIZJBCUBAQUBUCKZJLB
  CUBUDKLMLN $.

$( Conjunction is monotonic with respect to implication. $)
anmonl $p |- Ga => ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
  ( wi wa cf cc ax-idc idr ax-eanl ax-eim ax-eanr jca ax-iim ) ABEZACFZBCFZEDQR
  DPGZHZCBDSQGZHHZABUBPDUAIACUBQTJZKLACUBUCMNOO $.

curry $p |- Ga => ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
  ( wa wi cf cc ax-idc idr id ax-ian ax-eim ax-iim ) ABEZCFZABCFZFDAQDPGZHZBCDR
  AGZHHZOCDRTBGZHZHHPDUCIABUAUBASJBKLMNNN $.

uncurry $p |- Ga => ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
  ( wi wa cf cc ax-idc idr ax-eanl ax-eim ax-eanr ax-iim ) ABCEZEZABFZCEDQCDPGZ
  HZBCDRQGZHHZAOUAPDTIABUAQSJZKLABUAUBMLNN $.

$( Law of exportation $)
export $p |- Ga => ( ( ph -> ( ps -> ch ) ) <-> ( ( ph /\ ps ) -> ch ) ) $=
  ( wi wa uncurry curry jca ax-ibi ) ABCEEZABFCEZDLKEKLEDABCDGABCDHIJ $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PROPERTIES OF DISJUNCTION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

truorfal $p |- Ga => ( ( T. \/ F. ) <-> T. ) $=
  ( wtru wfal wo wi cf cc ax-itru ax-iim idr ax-iorl jca ax-ibi ) BCDZBABNENBEA
  NBAANFGHIBNABCABFGBAJKILM $.

$( Disjunction is idempotent. $)
oridm $p |- Ga => ( ( ph \/ ph ) <-> ph ) $=
  ( wo wi cf cc idr ax-eor ax-iim ax-iorl jca ax-ibi ) AACZABAMDMADBMABAAABMEFZ
  MBGANGZOHIAMBAABAEFABGJIKL $.

$( Disjunction is commutative. $)
orcom $p |- Ga => ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
  ( wo cf cc idr ax-iorr ax-iorl ax-eor ax-iim ) ABDZBADZCABMCLEZFZLCGBACNAEFFA
  OGHBACNBEFFBOGIJK $.

$( Disjunction is associative. $)
orass $p |- Ga => ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
  ( wo wi cf cc idr ax-iorl ax-iorr ax-eor ax-iim jca ax-ibi ) ABEZCEZABCEZEZDS
  QFQSFDQSDPCSDQGZHZQDIABSDTPGZHHZPUAIARDTUBAGZHHHAUCIJARDTUBBGZHHHZBCUFBUCIJKL
  ARDTCGZHHZBCUHCUAIKKLMSQDARQDSGZHZSDIPCDUIUDHHZABUKAUJIJJBCQDUIRGZHHZRUJIPCDU
  IULUEHHHZABUNBUMIKJPCDUIULUGHHHCUMIKLLMNO $.

$( Disjunction is monotonic with respect to implication. $)
ormonl $p |- Ga => ( ( ph -> ps ) -> ( ( ph \/ ch ) -> ( ps \/ ch ) ) ) $=
  ( wi wo cf cc idr ax-idc ax-eim ax-iorl ax-iorr ax-eor ax-iim ) ABEZACFZBCFZE
  DQRDPGZHZACRDSQGZHHZQTIBCDSUAAGHZHHZABUDPDUCJAUBIKLBCDSUACGHHHCUBIMNOO $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  COMPLEX TAUTOLOGIES
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

imor $p |- Ga => ( ( ~ ph \/ ps ) -> ( ph -> ps ) ) $=
  ( wn wo wi cf cc ax-idc idr ax-enot ax-efal ax-eor ax-iim ) ADZBEZABFCABCPGZH
  ZOBBCQAGZHHZPCSIBCQSOGZHHHZAUBARUAIOTJKLBTJMNN $.

$( Conjunction implies disjunction. $)
animor $p |- Ga => ( ( ph /\ ps ) -> ( ps \/ ph ) ) $=
  ( wa wo cf cc idr ax-eanr ax-iorl ax-iim ) ABDZBAECBACLFGZABMLCHIJK $.

$( Left-distributivity of conjunction over disjunction $)
andil $p |- Ga => ( ( ph /\ ( ps \/ ch ) )
  -> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
  ( wo wa cf cc idr ax-eanr ax-eanl id ax-ian ax-iorl ax-iorr ax-eor ax-iim ) A
  BCEZFZABFZACFZEZDBCUBDSGZHZARUDSDIZJTUADUCBGZHHABUDUFARUDUEKZBLMNTUADUCCGZHHA
  CUDUHUGCLMOPQ $.

anabs $p |- Ga => ( ( ph /\ ( ph \/ ps ) ) <-> ph ) $=
  ( wo wa wi cf cc idr ax-eanl ax-iim ax-iorl jca ax-ibi ) AABDZEZACAPFPAFCPACA
  OCPGHPCIJKAPCOACAGHZACIZABQRLMKMN $.

$( Left-distributivity of disjunction over conjunction $)
ordil $p |- Ga => ( ( ph \/ ( ps /\ ch ) )
  -> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
  ( wa wo cf cc idr ax-iorl ax-eanl ax-iorr ax-eor ax-eanr jca ax-iim ) ABCEZFZ
  ABFZACFZEDTSDRGZHZAQSUBRDIZABDUAAGHHZAUBIZJABDUAQGHHZBCUFQUBIZKLMAQTUBUCACUDU
  EJACUFBCUFUGNLMOP $.

orabs $p |- Ga => ( ( ph \/ ( ph /\ ps ) ) <-> ph ) $=
  ( wa wo wi cf cc idr ax-eanl ax-eor ax-iim ax-iorl jca ax-ibi ) AABDZEZACAQFQ
  AFCQACAPACQGZHZQCIASIABCRPGHHPSIJKLAQCAPCAGHACIMLNO $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  CLASSICAL TAUTOLOGIES
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Peirce's law $)
peirce $p |- Ga , ( ph \/ ~ ph ) => ( ( ( ph -> ps ) -> ph ) -> ph ) $=
  ( wi wn wo cf cc ax-idc idr ax-enot ax-efal ax-iim ax-eim ax-eor ) ABDZADZACA
  AEZFZGZHZARACTQGZHHZSCUBIAUCJPACTUBRGZHHHZQUAUDIABUEBCTUBUDAGZHHHHZAUGAUEJRUC
  UFIKLMNOM $.

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
