$( SKI COMBINATOR CALCULUS $)
$( This work by Victor SANNIER is released under the MIT License. $)

$(
###############################################################################
  SYNTAX
###############################################################################
$)

$c S K I ( ) term => = wff |- $.

$v f g h x y z $.
tf $f term f $.
tg $f term g $.
th $f term h $.
tx $f term x $.
ty $f term y $.
tz $f term z $.

tS $a term S $.
tK $a term K $.
tI $a term I $.

tap $a term ( f x ) $.

wss $a wff x => y $.
weq $a wff x = y $.

$(
###############################################################################
  AXIOMS
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  EQUALITY
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

ax-eqid $a |- x = x $.

${
  ax-eqsym.1 $e |- x = y $.
  ax-eqsym $a |- y = x $.
$}

${
  ax-eqtr.1 $e |- x = y $.
  ax-eqtr.2 $e |- y = z $.
  ax-eqtr $a |- x = z $.
$}

${
  ax-eqap.1 $e |- f = g $.
  ax-eqap.2 $e |- x = y $.
  ax-eqap $a |- ( f x ) = ( g y ) $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  REDUCTION (BIG-STEP)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

${
  ax-eqbs.1 $e |- x = y $.
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
  BASE COMBINATORS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

ax-S $a |- ( ( ( S x ) y ) z ) => ( ( x z ) ( y z ) ) $.
ax-K $a |- ( ( K x ) y ) => x $.
ax-I $a |- ( I x ) => x $.

$(
###############################################################################
  THEOREMS
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  EQUALITY AND REDUCTION
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
  eqapl.1 $e |- f = g $.
  eqapl $p |- ( f x ) => ( g x ) $= ( ax-eqbs bsid ax-ap ) ABCCABDECFG $.
$}

${
  eqapr.1 $e |- x = y $.
  eqapr $p |- ( f x ) => ( f y ) $= ( bsid ax-eqbs ax-ap ) AABCAEBCDFG $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  BOOLEAN LOGIC
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c F T NOT $.

tT $a term T $.
df-T $a |- T = K $.

etru $p |- ( ( T x ) y ) => x $=
  ( tT tap tK df-T eqapl apl ax-K ax-bstr ) CADZBDEADZBDAKLBCEAFGHABIJ $.

tF $a term F $.
df-F $a |- F = ( S K ) $.

efal $p |- ( ( F x ) y ) => y $=
  ( tF tap tS tK df-F eqapl apl ax-S ax-K ax-bstr ) CADZBDEFDZADZBDZBMOBCNAGHIP
  FBDABDZDBFABJBQKLL $.

tNOT $a term NOT $.
df-NOT $a |- NOT = ( ( S ( ( S I ) ( K F ) ) ) ( K T ) ) $.

nottru $p |- ( NOT T ) => F $=
  ( tNOT tT tap tS tI tK tF df-NOT eqapl ax-S ax-K ax-ap ax-I apl etru ax-bstr
  ) ABCDDECFGCZCZCFBCZCZBCZGATBHIUARBCZSBCZCZGRSBJUDEBCZQBCZCZBCZGUBUGUCBEQBJBB
  KLUHBUFCZBCZGUGUIBUEBUFBMNNUJUFGUFBOGBKPPPPP $.

notfal $p |- ( NOT F ) => T $=
  ( tNOT tF tap tS tI tK tT df-NOT eqapl ax-S ax-K ax-ap ax-I apl efal ax-bstr
  ) ABCDDECFBCZCZCFGCZCZBCZGATBHIUARBCZSBCZCZGRSBJUDEBCZQBCZCZGCZGUBUGUCGEQBJGB
  KLUHBBCZGCGUGUIGUEBUFBBMBBKLNBGOPPPP $.
