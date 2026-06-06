$( SKI COMBINATOR CALCULUS $)
$( This work by Victor SANNIER is released under the MIT License. $)

$(
###############################################################################
  SYNTAX
###############################################################################
$)

$c ( ) term wff |- $.
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
  ax-eqbs.1 $e |- x := y $.
  ax-eqbs $a |- x => y $.
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
  ( ax-eqid ax-eqbs ) AAABC $.

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
  eqapl.1 $e |- f := g $.
  eqapl $p |- ( f x ) => ( g x ) $=
    ( ax-eqbs apl ) ABCABDEF $.
$}

${
  eqapll.1 $e |- f := g $.
  eqapll $p |- ( ( f x ) y ) => ( ( g x ) y ) $=
    ( tap eqapl apl ) ACFBCFDABCEGH $.
$}

${
  eqaplll.1 $e |- f := g $.
  eqaplll $p |- ( ( ( f x ) y ) z ) => ( ( ( g x ) y ) z ) $=
    ( tap eqapll apl ) ACGDGBCGDGEABCDFHI $.
$}

${
  eqapr.1 $e |- x := y $.
  eqapr $p |- ( f x ) => ( f y ) $=
    ( ax-eqbs apr ) ABCBCDEF $.
$}

jnid $p |- x =><= x $=
  ( bsid ax-ijn ) AAAABZDC $.

${
  eqjn.1 $e |- x := y $.
  eqjn $p |- x =><= y $=
    ( ax-eqbs bsid ax-ijn ) ABBABCDBEF $.
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

$c F T NOT OR AND IMP $.

tT $a term T $.
df-T $a |- T := K $.

etru $p |- ( ( T x ) y ) => x $=
  ( tT tap tK df-T eqapll ax-K ax-bstr ) CADBDEADBDACEABFGABHI $.

tF $a term F $.
df-F $a |- F := ( S K ) $.

efal $p |- ( ( F x ) y ) => y $=
  ( tF tap tS tK df-F eqapll ax-S ax-K ax-bstr ) CADBDEFDZADBDZBCLABGHMFBDABDZD
  BFABIBNJKK $.

tNOT $a term NOT $.
df-NOT $a |- NOT := ( ( S ( ( S I ) ( K F ) ) ) ( K T ) ) $.

eNOT $p |- ( NOT x ) => ( ( x F ) T ) $=
  ( tNOT tap tS tI tK tF tT df-NOT eqapl ax-S apl ax-I ax-K ax-ap ax-bstr ) BAC
  DDECFGCZCZCFHCZCZACZAGCZHCZBTAIJUARACZSACZCZUCRSAKUFEACZQACZCZUECUCUDUIUEEQAK
  LUIUBUEHUGAUHGAMGANOHANOPPP $.

nottru $p |- ( NOT T ) => F $=
  ( tNOT tT tap tF eNOT etru ax-bstr ) ABCBDCBCDBEDBFG $.

notfal $p |- ( NOT F ) => T $=
  ( tNOT tF tap tT eNOT efal ax-bstr ) ABCBBCDCDBEBDFG $.

tOR $a term OR $.
df-OR $a |- OR := ( ( S I ) ( K T ) ) $.

eOR $p |- ( ( OR x ) y ) => ( ( x T ) y ) $=
  ( tOR tap tS tI tK tT df-OR eqapll ax-S ax-I ax-K ax-ap ax-bstr apl ) CADBDEF
  DGHDZDZADZBDAHDZBDCRABIJSTBSFADZQADZDTFQAKUAAUBHALHAMNOPO $.

ortru $p |- ( ( OR T ) y ) => T $=
  ( tOR tT tap eOR etru ax-bstr ) BCDADCCDADCCAECAFG $.

orfal $p |- ( ( OR F ) y ) => y $=
  ( tOR tF tap tT eOR efal ax-bstr ) BCDADCEDADACAFEAGH $.

tAND $a term AND $.
df-AND $a |- AND := ( ( S S ) ( K ( K F ) ) ) $.

eAND $p |- ( ( AND x ) y ) => ( ( x y ) F ) $=
  ( tAND tap tS tK tF df-AND eqapll ax-S apl ax-K ax-bstr apr ) CADBDEEDFFGDZDZ
  DZADZBDZABDZGDZCQABHISEADPADZDZBDZUARUCBEPAJKUDTUBBDZDUAAUBBJTUEGUEOBDGUBOBOA
  LKGBLMNMMM $.

antru $p |- ( ( AND T ) y ) => y $=
  ( tAND tT tap tF eAND etru ax-bstr ) BCDADCADEDACAFAEGH $.

anfal $p |- ( ( AND F ) y ) => F $=
  ( tAND tF tap eAND efal ax-bstr ) BCDADCADCDCCAEACFG $.

tIMP $a term IMP $.
df-IMP $a |- IMP := ( ( S ( K OR ) ) ( ( S ( K NOT ) ) I ) ) $.

eIMP $p |- ( ( IMP x ) y ) => ( ( OR ( NOT x ) ) y ) $=
  ( tIMP tap tS tK tOR tNOT df-IMP eqapll ax-S apl ax-K ax-I ax-ap ax-bstr apr
  tI ) CADBDEFGDZDEFHDZDRDZDZADZBDZGHADZDZBDZCUBABIJUDSADZUAADZDZBDZUGUCUJBSUAA
  KLUKGUIDZBDUGUJULBUHGUIGAMLLULUFBGUIUEUITADZRADZDUETRAKUMHUNAHAMANOPQLPPP $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  AVIARY COMBINATORS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c B C W $.

$( Bluebird combinator $)
tB $a term B $.
df-B $a |- B := ( ( S ( K S ) ) K ) $.

eB $p |- ( ( ( B f ) g ) x ) => ( f ( g x ) ) $=
  ( tB tap tS tK df-B eqaplll ax-S apll ax-K apl ax-bstr ) DAEBECEFGFEZEGEZAEZB
  ECEZABCEZEZDPABCHIROAEZGAEZEZBECEZTQUCBCOGAJKUDFUBEZBECEZTUCUEBCUAFUBFALMKUFU
  BCEZSETUBBCJUGASACLMNNNN $.

$( Cardinal combinator $)
tC $a term C $.
df-C $a |- C := ( ( S ( ( B B ) S ) ) ( K K ) ) $.

eC $p |- ( ( ( C f ) x ) y ) => ( ( f y ) x ) $=
  ( tC tap tS tB tK df-C eqaplll ax-S apll eB ax-K ax-ap apl apr ax-bstr ) DAEB
  ECEFGGEFEZEHHEZEZAEZBECEZACEZBEZDUAABCIJUCSAEZTAEZEZBECEZUEUBUHBCSTAKLUIGFAEZ
  EZHEZBEZCEZUEUHULBCUFUKUGHGFAMHANOLUNUJHBEZEZCEZUEUMUPCUJHBMPUQUDUOCEZEUEAUOC
  KUDURBBCNQRRRRR $.

$( Warbler combinator $)
tW $a term W $.
df-W $a |- W := ( ( S S ) ( K I ) ) $.

eW $p |- ( ( W f ) x )  => ( ( f x ) x ) $=
  ( tW tap tS tK tI df-W eqapll ax-S apl ax-K ax-I ax-bstr apr ) CADBDEEDFGDZDZ
  ADZBDZABDZBDZCQABHISEADPADZDZBDZUARUCBEPAJKUDTUBBDZDUAAUBBJTUEBUEGBDBUBGBGALK
  BMNONNN $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ARITHMETIC
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c 0 1 2 SUCC ADD MUL $.

t0 $a term 0 $.
df-0 $a |- 0 := ( K I ) $.

e0 $p |- ( ( 0 f ) x ) => x $=
  ( t0 tap tK tI df-0 eqapll ax-K apl ax-I ax-bstr ) CADBDEFDZADZBDZBCMABGHOFBD
  BNFBFAIJBKLL $.

tSUCC $a term SUCC $.
df-SUCC $a |- SUCC := ( S B ) $.

eSUCC $p |- ( ( ( SUCC x ) f ) y ) => ( f ( ( x f ) y ) ) $=
  ( tSUCC tap tS tB df-SUCC eqaplll ax-S apl eB ax-bstr ) DBEAECEFGEZBEAEZCEZAB
  AEZCEEZDNBACHIPGAEQEZCEROSCGBAJKAQCLMM $.

t1 $a term 1 $.
df-1 $a |- 1 := ( SUCC 0 ) $.

e1 $p |- ( ( 1 f ) x ) => ( f x ) $=
  ( t1 tap tSUCC t0 df-1 eqapll eSUCC e0 apr ax-bstr ) CADBDEFDZADBDZABDZCMABGH
  NAFADBDZDOAFBIAPBABJKLL $.

t2 $a term 2 $.
df-2 $a |- 2 := ( SUCC 1 ) $.

e2 $p |- ( ( 2 f ) x ) => ( f ( f x ) ) $=
  ( t2 tap tSUCC t1 df-2 eqapll eSUCC e1 apr ax-bstr ) CADBDEFDZADBDZAABDZDZCMA
  BGHNAFADBDZDPAFBIAQOABJKLL $.

tADD $a term ADD $.
df-ADD $a |- ADD := ( ( S I ) ( K SUCC ) ) $.

eADD $p |- ( ( ADD x ) y ) => ( ( x SUCC ) y ) $=
  ( tADD tap tS tI tK tSUCC df-ADD eqapll ax-S apl ax-I ax-K ax-ap ax-bstr ) CA
  DBDEFDGHDZDZADZBDZAHDZBDZCRABIJTFADZQADZDZBDUBSUEBFQAKLUEUABUCAUDHAMHANOLPP
  $.

add0 $p |- ( ( ADD 0 ) x ) => x $=
  ( tADD t0 tap tSUCC eADD e0 ax-bstr ) BCDADCEDADACAFEAGH $.

1p1 $p |- ( ( ADD 1 ) 1 ) =><= 2 $=
  ( tADD t1 tap t2 tSUCC eADD e1 ax-bstr df-2 ax-eqbs ax-ijn ) ABCBCZDEBCZLBECB
  CMBBFEBGHDMIJK $.

tMUL $a term MUL $.
df-MUL $a |- MUL := B $.

eMUL $p |- ( ( ( MUL x ) y ) f ) => ( x ( y f ) ) $=
  ( tMUL tap tB df-MUL eqaplll eB ax-bstr ) DBECEAEFBECEAEBCAEEDFBCAGHBCAIJ $.

$c ISZERO $.

tISZERO $a term ISZERO $.
df-ISZERO $a |- ISZERO := ( ( S ( ( S I ) ( K ( K F ) ) ) ) ( K T ) ) $.

eISZERO $p |- ( ISZERO x ) => ( ( x ( K F ) ) T ) $=
  ( tISZERO tap tS tI tK tF tT df-ISZERO eqapl ax-S ax-K ax-ap ax-I apl ax-bstr
  ) BACDDECFFGCZCZCZCFHCZCZACZAQCZHCZBUAAIJUBSACZTACZCZUDSTAKUGEACZRACZCZHCUDUE
  UJUFHERAKHALMUJUCHUHAUIQANQALMOPPP $.

0eq0 $p |- ( ISZERO 0 ) => T $=
  ( tISZERO t0 tap tK tF tT eISZERO e0 ax-bstr ) ABCBDECZCFCFBGJFHI $.

1ne0 $p |- ( ISZERO 1 ) => F $=
  ( tISZERO t1 tap tK tF tT eISZERO e1 ax-K ax-bstr ) ABCBDECZCFCZEBGLKFCEKFHEF
  IJJ $.

succne0 $p |- ( ISZERO ( SUCC x ) ) => F $=
  ( tISZERO tSUCC tap tK tF tT eISZERO eSUCC ax-K ax-bstr ) BCADZDLEFDZDGDZFLHN
  MAMDGDZDFMAGIFOJKK $.
