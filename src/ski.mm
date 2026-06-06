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

tS $a term S $.
ax-S $a |- ( ( ( S x ) y ) z ) => ( ( x z ) ( y z ) ) $.

tK $a term K $.
ax-K $a |- ( ( K x ) y ) => x $.

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

bsid $p |- x => x $= ( ax-eqid ax-eqbs ) AAABC $.

${
  apl.1 $e |- f => g $.
  apl $p |- ( f x ) => ( g x ) $= ( bsid ax-ap ) ABCCDCEF $.
$}

${
  apr.1 $e |- x => y $.
  apr $p |- ( f x ) => ( f y ) $= ( bsid ax-ap ) AABCAEDF $.
$}

${
  eqapl.1 $e |- f := g $.
  eqapl $p |- ( f x ) => ( g x ) $= ( ax-eqbs bsid ax-ap ) ABCCABDECFG $.
$}

${
  eqapr.1 $e |- x := y $.
  eqapr $p |- ( f x ) => ( f y ) $= ( bsid ax-eqbs ax-ap ) AABCAEBCDFG $.
$}

jnid $p |- x =><= x $= ( bsid ax-ijn ) AAAABZDC $.

${
  eqjn.1 $e |- x := y $.
  eqjn $p |- x =><= y $= ( ax-eqbs bsid ax-ijn ) ABBABCDBEF $.
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
  ( tT tap tK df-T eqapl apl ax-K ax-bstr ) CADZBDEADZBDAKLBCEAFGHABIJ $.

tF $a term F $.
df-F $a |- F := ( S K ) $.

efal $p |- ( ( F x ) y ) => y $=
  ( tF tap tS tK df-F eqapl apl ax-S ax-K ax-bstr ) CADZBDEFDZADZBDZBMOBCNAGHIP
  FBDABDZDBFABJBQKLL $.

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
  ( tOR tap tS tI tK tT df-OR eqapl apl ax-S ax-I ax-K ax-ap ax-bstr ) CADZBDEF
  DGHDZDZADZBDZAHDZBDZQTBCSAIJKUAFADZRADZDZBDUCTUFBFRALKUFUBBUDAUEHAMHANOKPP $.

ortru $p |- ( ( OR T ) y ) => T $=
  ( tOR tT tap eOR etru ax-bstr ) BCDADCCDADCCAECAFG $.

orfal $p |- ( ( OR F ) y ) => y $=
  ( tOR tF tap tT eOR efal ax-bstr ) BCDADCEDADACAFEAGH $.

tAND $a term AND $.
df-AND $a |- AND := ( ( S S ) ( K ( K F ) ) ) $.

eAND $p |- ( ( AND x ) y ) => ( ( x y ) F ) $=
  ( tAND tap tS tK tF df-AND eqapl apl ax-S ax-K ax-bstr apr ) CADZBDEEDFFGDZDZ
  DZADZBDZABDZGDZOSBCRAHIJTEADQADZDZBDZUBSUDBEQAKJUEUAUCBDZDUBAUCBKUAUFGUFPBDGU
  CPBPALJGBLMNMMM $.

antru $p |- ( ( AND T ) y ) => y $=
  ( tAND tT tap tF eAND etru ax-bstr ) BCDADCADEDACAFAEGH $.

anfal $p |- ( ( AND F ) y ) => F $=
  ( tAND tF tap eAND efal ax-bstr ) BCDADCADCDCCAEACFG $.
