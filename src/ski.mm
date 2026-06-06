$( SKI COMBINATOR CALCULUS $)
$( This work by Victor SANNIER is released under the MIT License. $)
$( See <https://dallaylaen.github.io/ski-interpreter/quest.html>. $)

$(
###############################################################################
  SYNTAX
###############################################################################
$)

$c ( ) term wff |- $.
$( $j syntax '|-' as 'wff'; $)
$v f g h x y z $.

tf $f term f $.
tg $f term g $.
th $f term h $.

tx $f term x $.
ty $f term y $.
tz $f term z $.

tap $a term ( f x ) $.

$(
###############################################################################
  AXIOMS
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  DEFINITIONAL EQUALITY
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c := $.
weq $a wff x := y $.
ax-eqid $a |- x := x $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  MULTI-STEP REDUCTION
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c => $.
wss $a wff x => y $.

${
  ax-bseq.1 $e |- x := y $.
  ax-bseq $a |- x => y $.
$}

${
  ax-bstr.1 $e |- x => y $.
  ax-bstr.2 $e |- y => z $.
  ax-bstr $a |- x => z $.
$}

${
  ax-ap.1 $e |- f => g $.
  ax-ap.2 $e |- x => y $.
  ax-ap $a |- ( f x ) => ( g y ) $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  JOINABILITY (OBSERVATIONAL EQUALITY)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c =><= $.
wjn $a wff x =><= y $.

${
  ax-ijn.1 $e |- x => z $.
  ax-ijn.2 $e |- y => z $.
  ax-ijn $a |- x =><= y $.
$}

${
  ax-ejnl.1 $e |- x =><= y $.
  ax-ejnl $a |- x => y $.
$}

${
  ax-ejnr.1 $e |- x =><= y $.
  ax-ejnr $a |- y => x $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  BASE COMBINATORS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c S K I $.

$( Starling combinator $)
tS $a term S $.
ax-S $a |- ( ( ( S x ) y ) z ) => ( ( x z ) ( y z ) ) $.

$( Kestrel combinator $)
tK $a term K $.
ax-K $a |- ( ( K x ) y ) => x $.

$( Identity combinator $)
tI $a term I $.
ax-I $a |- ( I x ) => x $.

$(
###############################################################################
  THEOREMS
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  EQUALITY, REDUCTION AND JOINABILITY
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

bsid $p |- x => x $=
  ( ax-eqid ax-bseq ) AAABC $.

${
  apl.1 $e |- f => g $.
  apl $p |- ( f x ) => ( g x ) $=
    ( bsid ax-ap ) ABCCDCEF $.
$}

${
  apll.1 $e |- f => g $.
  apll $p |- ( ( f x ) y ) => ( ( g x ) y ) $=
    ( tap apl ) ACFBCFDABCEGG $.
$}

${
  apr.1 $e |- x => y $.
  apr $p |- ( f x ) => ( f y ) $=
    ( bsid ax-ap ) AABCAEDF $.
$}

${
  aplr.1 $e |- x => z $.
  aplr $p |- ( ( f x ) y ) => ( ( f z ) y ) $=
    ( tap apr apl ) ABFADFCABDEGH $.
$}

${
  apeql.1 $e |- f := g $.
  apeql $p |- ( f x ) => ( g x ) $=
    ( ax-bseq apl ) ABCABDEF $.
$}

${
  apeqll.1 $e |- f := g $.
  apeqll $p |- ( ( f x ) y ) => ( ( g x ) y ) $=
    ( tap apeql apl ) ACFBCFDABCEGH $.
$}

${
  apeqlll.1 $e |- f := g $.
  apeqlll $p |- ( ( ( f x ) y ) z ) => ( ( ( g x ) y ) z ) $=
    ( tap apeqll apl ) ACGDGBCGDGEABCDFHI $.
$}

${
  apeqr.1 $e |- x := y $.
  apeqr $p |- ( f x ) => ( f y ) $=
    ( ax-bseq apr ) ABCBCDEF $.
$}

jnid $p |- x =><= x $=
  ( bsid ax-ijn ) AAAABZDC $.

${
  jneq.1 $e |- x := y $.
  jneq $p |- x =><= y $=
    ( ax-bseq bsid ax-ijn ) ABBABCDBEF $.
$}

${
  jntr.1 $e |- x =><= y $.
  jntr.2 $e |- y =><= z $.
  jntr $p |- x =><= z $=
    ( ax-ejnl ax-ejnr ax-ijn ) ACBABDFBCEGH $.
$}

${
  jnsym.1 $e |- x =><= y $.
  jnsym $p |- y =><= x $=
    ( bsid ax-ejnl ax-ijn ) BABBDABCEF $.
$}

${
  jnbs.1 $e |- x => y $.
  jnbs $p |- x =><= y $=
    ( bsid ax-ijn ) ABBCBDE $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  BASE COMBINATORS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

SKK $p |- ( ( ( S K ) K ) x ) =><= ( I x ) $=
  ( tS tK tap tI ax-S ax-K ax-bstr ax-I ax-ijn ) BCDCDADZEADAKCADZLDACCAFALGHAI
  J $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  BOOLEAN LOGIC
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c FALSE TRUE NOT OR AND IMPLIES $.

tTRU $a term TRUE $.
df-TRU $a |- TRUE := K $.

TRUval $p |- ( ( TRUE x ) y ) => x $=
  ( tTRU tap tK df-TRU apeqll ax-K ax-bstr ) CADBDEADBDACEABFGABHI $.

tFAL $a term FALSE $.
df-FAL $a |- FALSE := ( S K ) $.

FALval $p |- ( ( FALSE x ) y ) => y $=
  ( tFAL tap tS tK df-FAL apeqll ax-S ax-K ax-bstr ) CADBDEFDZADBDZBCLABGHM
  FBDABDZDBFABIBNJKK $.

tNOT $a term NOT $.
df-NOT $a |- NOT := ( ( S ( ( S I ) ( K FALSE ) ) ) ( K TRUE ) ) $.

NOTval $p |- ( NOT x ) => ( ( x FALSE ) TRUE ) $=
  ( tNOT tap tS tI tFAL tTRU df-NOT apeql ax-S apl ax-I ax-K ax-ap ax-bstr
  tK ) BACDDECPFCZCZCPGCZCZACZAFCZGCZBTAHIUARACZSACZCZUCRSAJUFEACZQACZCZUECUCUD
  UIUEEQAJKUIUBUEGUGAUHFALFAMNGAMNOOO $.

nottru $p |- ( NOT TRUE ) => FALSE $=
  ( tNOT tTRU tap tFAL NOTval TRUval ax-bstr ) ABCBDCBCDBEDBFG $.

notfal $p |- ( NOT FALSE ) => TRUE $=
  ( tNOT tFAL tap tTRU NOTval FALval ax-bstr ) ABCBBCDCDBEBDFG $.

tOR $a term OR $.
df-OR $a |- OR := ( ( S I ) ( K TRUE ) ) $.

ORval $p |- ( ( OR x ) y ) => ( ( x TRUE ) y ) $=
  ( tOR tap tS tI tK tTRU df-OR apeqll ax-S ax-I ax-K ax-ap ax-bstr apl ) CADB
  DEFDGHDZDZADZBDAHDZBDCRABIJSTBSFADZQADZDTFQAKUAAUBHALHAMNOPO $.

ortru $p |- ( ( OR TRUE ) y ) => TRUE $=
  ( tOR tTRU tap ORval TRUval ax-bstr ) BCDADCCDADCCAECAFG $.

orfal $p |- ( ( OR FALSE ) y ) => y $=
  ( tOR tFAL tap tTRU ORval FALval ax-bstr ) BCDADCEDADACAFEAGH $.

tAND $a term AND $.
df-AND $a |- AND := ( ( S S ) ( K ( K FALSE ) ) ) $.

ANDval $p |- ( ( AND x ) y ) => ( ( x y ) FALSE ) $=
  ( tAND tap tS tK tFAL df-AND apeqll ax-S apl ax-K ax-bstr apr ) CADBDEEDFFG
  DZDZDZADZBDZABDZGDZCQABHISEADPADZDZBDZUARUCBEPAJKUDTUBBDZDUAAUBBJTUEGUEOBDGUB
  OBOALKGBLMNMMM $.

antru $p |- ( ( AND TRUE ) y ) => y $=
  ( tAND tTRU tap tFAL ANDval TRUval ax-bstr ) BCDADCADEDACAFAEGH $.

anfal $p |- ( ( AND FALSE ) y ) => FALSE $=
  ( tAND tFAL tap ANDval FALval ax-bstr ) BCDADCADCDCCAEACFG $.

tIMP $a term IMPLIES $.
df-IMP $a |- IMPLIES := ( ( S ( K OR ) ) ( ( S ( K NOT ) ) I ) ) $.

IMPval $p |- ( ( IMPLIES x ) y ) => ( ( OR ( NOT x ) ) y ) $=
  ( tIMP tap tS tK tOR tNOT df-IMP apeqll ax-S apl ax-K ax-I ax-ap ax-bstr apr
  tI ) CADBDEFGDZDEFHDZDRDZDZADZBDZGHADZDZBDZCUBABIJUDSADZUAADZDZBDZUGUCUJBSUAA
  KLUKGUIDZBDUGUJULBUHGUIGAMLLULUFBGUIUEUITADZRADZDUETRAKUMHUNAHAMANOPQLPPP $.

imptru $p |- ( ( IMPLIES TRUE ) x ) => x $=
  ( tIMP tTRU tap tOR tNOT IMPval tFAL nottru aplr orfal ax-bstr ) BCDADEFCDZDA
  DZACAGNEHDADAEMAHIJAKLL $.

impfal $p |- ( ( IMPLIES FALSE ) x ) => TRUE $=
  ( tIMP tFAL tap tOR tNOT tTRU IMPval notfal aplr ortru ax-bstr ) BCDADEFCDZDA
  DZGCAHNEGDADGEMAGIJAKLL $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  AVIARY COMBINATORS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c B C W T V M Y $.

$( Bluebird combinator (compose) $)
tB $a term B $.
df-B $a |- B := ( ( S ( K S ) ) K ) $.

Bval $p |- ( ( ( B f ) g ) x ) => ( f ( g x ) ) $=
  ( tB tap tS tK df-B apeqlll ax-S apll ax-K apl ax-bstr ) DAEBECEFGFEZEGEZAEZB
  ECEZABCEZEZDPABCHIROAEZGAEZEZBECEZTQUCBCOGAJKUDFUBEZBECEZTUCUEBCUAFUBFALMKUFU
  BCEZSETUBBCJUGASACLMNNNN $.

$( Cardinal combinator (flip) $)
tC $a term C $.
df-C $a |- C := ( ( S ( ( B B ) S ) ) ( K K ) ) $.

Cval $p |- ( ( ( C f ) x ) y ) => ( ( f y ) x ) $=
  ( tC tap tS tB tK df-C apeqlll ax-S apll Bval ax-K ax-ap apl apr ax-bstr ) DA
  EBECEFGGEFEZEHHEZEZAEZBECEZACEZBEZDUAABCIJUCSAEZTAEZEZBECEZUEUBUHBCSTAKLUIGFA
  EZEZHEZBEZCEZUEUHULBCUFUKUGHGFAMHANOLUNUJHBEZEZCEZUEUMUPCUJHBMPUQUDUOCEZEUEAU
  OCKUDURBBCNQRRRRR $.

$( Warbler combinator (duplicate) $)
tW $a term W $.
df-W $a |- W := ( ( S S ) ( K I ) ) $.

Wval $p |- ( ( W f ) x )  => ( ( f x ) x ) $=
  ( tW tap tS tK tI df-W apeqll ax-S apl ax-K ax-I ax-bstr apr ) CADBDEEDFGDZDZ
  ADZBDZABDZBDZCQABHISEADPADZDZBDZUARUCBEPAJKUDTUBBDZDUAAUBBJTUEBUEGBDBUBGBGALK
  BMNONNN $.

$( Thrush combinator $)
tT $a term T $.
df-T $a |- T := ( C I ) $.

Tval $p |- ( ( T x ) f ) => ( f x ) $=
  ( tT tap tC tI df-T apeqll Cval ax-I apl ax-bstr ) CBDADEFDZBDADZABDZCMBAGHNF
  ADZBDOFBAIPABAJKLL $.

$( Vireo combinator $)
tV $a term V $.
df-V $a |- V := ( ( B C ) ( C I ) ) $.

Vval $p |- ( ( ( V x ) y ) f ) => ( ( f x ) y ) $=
  ( tV tap tB tC tI df-V apeqlll Bval apll Cval ax-I apl ax-bstr ) DBECEAEFGEGH
  EZEZBEZCEAEZABEZCEZDRBCAIJTGQBEZEZCEAEZUBSUDCAGQBKLUEUCAEZCEUBUCCAMUFUACUFHAE
  ZBEUAHBAMUGABANOPOPPP $.

$( Mockingbird combinator (self-apply) $)
tM $a term M $.
df-M $a |- M := ( ( S I ) I ) $.

Mval $p |- ( M x ) => ( x x ) $=
  ( tM tap tS tI df-M apeql ax-S ax-I ax-ap ax-bstr ) BACDECECZACZAACZBLAFGMEAC
  ZOCNEEAHOAOAAIZPJKK $.

mi $p |- ( M I ) => I $=
  ( tM tI tap Mval ax-I ax-bstr ) ABCBBCBBDBEF $.

wi $p |- ( ( W I ) x ) =><= ( M x ) $=
  ( tW tI tap tM Wval ax-I apl ax-bstr Mval ax-ijn ) BCDADZEADAADZLCADZADMCAFNA
  AAGHIAJK $.

$( Why combinator $)
tY $a term Y $.
df-Y $a |- Y := ( ( B M ) ( ( C B ) M ) ) $.

Yval $p |- ( Y f ) => ( M ( ( ( C B ) M ) f ) ) $=
  ( tY tap tB tM tC df-Y apeql Bval ax-bstr ) BACDECFDCECZCZACEKACCBLAGHEKAIJ
  $.

fix $p |- ( ( Y f ) x ) =><= ( ( f ( Y f ) ) x ) $=
  ( tY tap tB tM tC df-Y apeqll Bval apl Cval aplr Mval ax-bstr apeql apr
  ax-ijn ) CADZBDZASDBDZAEADFDZUBDZDBDZTEFDGEDFDZDZADZBDZUDCUFABHIUHFUEADZDZBDZ
  UDUGUJBFUEAJZKUKFUBDZBDZUDFUIBUBEFALZMUNUCBDZUDUMUCBUBNZKUPAUMDZBDZUDUCURBAFU
  BJKAUMBUCUQMZOOOOOUAAUGDBDZUDASBUGCUFAHPMVAAUJDBDZUDAUGBUJULMVBUSUDAUJBUMFUIU
  BUOQMUTOOOR $.

$( The fixed point of a constant function is the function itself. $)
YK $p |- ( ( Y ( K f ) ) x ) => ( f x ) $=
  ( tY tK tap tM tC tB df-Y apeqll Bval apl ax-bstr Mval Cval ax-K ) CDAEZEBEZF
  GHEFEZQEZEZBEZABEZRHFESEZQEZBEUBCUDQBIJUEUABFSQKLMUBTTEZBEZUCUAUFBTNLUGHQEFEZ
  TEZBEZUCUFUIBTUHTHFQOLLUJQUAEZBEUCUIUKBQFTKLUKABAUAPLMMMM $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ARITHMETIC
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c 0 1 2 SUCC ADD MUL $.

t0 $a term 0 $.
df-0 $a |- 0 := ( K I ) $.

e0 $p |- ( ( 0 f ) x ) => x $=
  ( t0 tap tK tI df-0 apeqll ax-K apl ax-I ax-bstr ) CADBDEFDZADZBDZBCMABGHOFBD
  BNFBFAIJBKLL $.

tSUCC $a term SUCC $.
df-SUCC $a |- SUCC := ( S B ) $.

SUCCval $p |- ( ( ( SUCC x ) f ) y ) => ( f ( ( x f ) y ) ) $=
  ( tSUCC tap tS tB df-SUCC apeqlll ax-S apl Bval ax-bstr ) DBEAECEFGEZBEAEZCEZ
  ABAEZCEEZDNBACHIPGAEQEZCEROSCGBAJKAQCLMM $.

t1 $a term 1 $.
df-1 $a |- 1 := ( SUCC 0 ) $.

e1 $p |- ( ( 1 f ) x ) => ( f x ) $=
  ( t1 tap tSUCC t0 df-1 apeqll SUCCval e0 apr ax-bstr ) CADBDEFDZADBDZABDZCMAB
  GHNAFADBDZDOAFBIAPBABJKLL $.

t2 $a term 2 $.
df-2 $a |- 2 := ( SUCC 1 ) $.

2val $p |- ( ( 2 f ) x ) => ( f ( f x ) ) $=
  ( t2 tap tSUCC t1 df-2 apeqll SUCCval e1 apr ax-bstr ) CADBDEFDZADBDZAABDZDZC
  MABGHNAFADBDZDPAFBIAQOABJKLL $.

tADD $a term ADD $.
df-ADD $a |- ADD := ( ( S I ) ( K SUCC ) ) $.

ADDval $p |- ( ( ADD x ) y ) => ( ( x SUCC ) y ) $=
  ( tADD tap tS tI tK tSUCC df-ADD apeqll ax-S apl ax-I ax-K ax-ap ax-bstr ) CA
  DBDEFDGHDZDZADZBDZAHDZBDZCRABIJTFADZQADZDZBDUBSUEBFQAKLUEUABUCAUDHAMHANOLPP
  $.

add0 $p |- ( ( ADD 0 ) x ) => x $=
  ( tADD t0 tap tSUCC ADDval e0 ax-bstr ) BCDADCEDADACAFEAGH $.

1p1 $p |- ( ( ADD 1 ) 1 ) =><= 2 $=
  ( tADD t1 tap t2 tSUCC ADDval e1 ax-bstr df-2 ax-bseq ax-ijn ) ABCBCZDEBCZLBE
  CBCMBBFEBGHDMIJK $.

tMUL $a term MUL $.
df-MUL $a |- MUL := B $.

MULval $p |- ( ( ( MUL x ) y ) f ) => ( x ( y f ) ) $=
  ( tMUL tap tB df-MUL apeqlll Bval ax-bstr ) DBECEAEFBECEAEBCAEEDFBCAGHBCAIJ $.

$c ISZERO $.

tISZR $a term ISZERO $.
df-ISZR $a |- ISZERO := ( ( S ( ( S I ) ( K ( K FALSE ) ) ) ) ( K TRUE ) ) $.

ISZRval $p |- ( ISZERO x ) => ( ( x ( K FALSE ) ) TRUE ) $=
  ( tISZR tap tS tI tFAL tTRU df-ISZR apeql ax-S ax-K ax-ap ax-I ax-bstr
  tK apl ) BACDDECOOFCZCZCZCOGCZCZACZAQCZGCZBUAAHIUBSACZTACZCZUDSTAJUGEACZRACZC
  ZGCUDUEUJUFGERAJGAKLUJUCGUHAUIQAMQAKLPNNN $.

0eq0 $p |- ( ISZERO 0 ) => TRUE $=
  ( tISZR t0 tap tK tFAL tTRU ISZRval e0 ax-bstr ) ABCBDECZCFCFBGJFHI $.

1ne0 $p |- ( ISZERO 1 ) => FALSE $=
  ( tISZR t1 tap tK tFAL tTRU ISZRval e1 ax-K ax-bstr ) ABCBDECZCFCZEBGLKF
  CEKFHEFIJJ $.

sne0 $p |- ( ISZERO ( SUCC x ) ) => FALSE $=
  ( tISZR tSUCC tap tK tFAL tTRU ISZRval SUCCval ax-K ax-bstr ) BCADZDLEFDZD
  GDZFLHNMAMDGDZDFMAGIFOJKK $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  PAIRS AND LISTS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c NIL CONS FST SND ISEMPTY $.

tNIL $a term NIL $.
df-NIL $a |- NIL := ( K I ) $.

NILval $p |- ( ( NIL x ) y ) => y $=
  ( tNIL tap tK tI df-NIL apeqll ax-K apl ax-I ax-bstr ) CADBDEFDZADZBDZBCMABGH
  OFBDBNFBFAIJBKLL $.

tCONS $a term CONS $.
df-CONS $a |- CONS := V $.

CONSval $p |- ( ( ( CONS x ) y ) f ) => ( ( f x ) y ) $=
  ( tCONS tap tV df-CONS apeqlll Vval ax-bstr ) DBECEAEFBECEAEABECEDFBCAGHABCIJ
  $.

tFST $a term FST $.
df-FST $a |- FST := TRUE $.

tSND $a term SND $.
df-SND $a |- SND := FALSE $.

tISMT $a term ISEMPTY $.
df-ISMT $a |- ISEMPTY := ( ( B ( T TRUE ) ) ( T ( K ( K ( K FALSE ) ) ) ) ) $.

ISMTval $p |- ( ISEMPTY x ) => ( ( x ( K ( K ( K FALSE ) ) ) ) TRUE ) $=
  ( tISMT tap tB tT tTRU tK tFAL df-ISMT apeql Bval Tval apl ax-bstr ) BAC
  DEFCZCEGGGHCCCZCZCZACZAPCZFCZBRAIJSOQACZCZUAOQAKUCUBFCUAUBFLUBTFAPLMNNN $.

nilempty $p |- ( ISEMPTY NIL ) => TRUE $=
  ( tISMT tNIL tap tK tFAL tTRU ISMTval NILval ax-bstr ) ABCBDDDECCCZCFCFB
  GJFHI $.

consnempty $p |- ( ISEMPTY ( ( CONS x ) y ) ) => FALSE $=
  ( tISMT tCONS tap tK tFAL tTRU ISMTval CONSval apl ax-K apll ax-bstr ) C
  DAEBEZEOFFFGEZEZEZEZHEZGOITRAEZBEZHEZGSUBHRABJKUCQBEZHEZGUAQBHQALMUEPHEGUDPHP
  BLKGHLNNNN $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  INFINITE STREAMS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c ZEROS $.
tZEROS $a term ZEROS $.
df-ZEROS $a |- ZEROS := ( Y ( CONS 0 ) ) $.

zhead $p |- ( ZEROS FST ) => 0 $=
  ( tZEROS tFST tap tY tCONS t0 df-ZEROS apeql tM tC tB Yval apl Mval Cval apll
  Bval CONSval tTRU ax-bstr df-FST apeqll TRUval ) ABCDEFCZCZBCZFAUEBGHUFIJKCIC
  UDCZCZBCZFUEUHBUDLMUIUGUGCZBCZFUHUJBUGNMUKKUDCICZUGCZBCZFUGULUGBKIUDOPUNUDUHC
  ZBCZFUMUOBUDIUGQMUPBFCUHCZFBFUHRUQSFCUHCFBSFUHUAUBFUHUCTTTTTTT $.

ztail $p |- ( ZEROS SND ) =><= ZEROS $=
  ( tZEROS tSND tap tCONS t0 tY df-ZEROS apeql fix ax-ejnl ax-bstr ax-bseq aplr
  ax-ijn CONSval tFAL df-SND apeqll FALval jnbs jntr ) ABCZDECZACBCZAUBUDUCFUCC
  ZCBCZUBUEBCZUFAUEBGHUGUFUCBIJKUCABUEAUEGLMNUDAUDBECACZABEAOUHPECACABPEAQREASK
  KTUA $.
