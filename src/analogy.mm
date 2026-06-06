$( FOUR-TERMS ANALOGIES AND DISANALOGIES $)
$( This work by Victor SANNIER is released under the MIT License. $)

$c wff |- : $.
$( $j syntax '|-' as 'wff'; $)

$(
###############################################################################
  ANALOGIES
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  SYNTAX
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c term $.

$v a b c d $.
ta $f term a $.
tb $f term b $.
tc $f term c $.
td $f term d $.

$v a' b' c' d' $.
tap $f term a' $.
tbp $f term b' $.
tcp $f term c' $.
tdp $f term d' $.

$v e f $.
te $f term e $.
tf $f term f $.

$c :: $.
wa $a wff a : b :: c : d $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  AXIOMS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Reflexivity $)
ax-refl $a |- a : b :: a : b $.

${
  ax-sym.1 $e |- a : b :: c : d $.
  $( Symmetry $)
  ax-sym $a |- c : d :: a : b $.
$}

${
  ax-exch.1 $e |- a : b :: c : d $.
  $( Central permutation $)
  ax-exch $a |- a : c :: b : d $.
$}

${
  ax-tr.1 $e |- a : b :: c : d $.
  ax-tr.2 $e |- c : d :: e : f $.
  $( Transitivity $)
  ax-tr $a |- a : b :: e : f $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  THEOREMS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

id $p |- a : a :: b : b $= ( ax-refl ax-exch ) ABABABCD $.

${
  ext.1 $e |- a : b :: c : d $.
  $( Extreme permutation $)
  ext $p |- d : b :: c : a $= ( ax-sym ax-exch ) CADBCDABABCDEFGF $.
$}

${
  inv.1 $e |- a : b :: c : d $.
  $( Internal reversal $)
  inv $p |- b : a :: d : c $= ( ax-exch ax-sym ) BDACACBDABCDEFGF $.
$}

${
  rev.1 $e |- a : b :: c : d $.
  $( Complete reversal $)
  rev $p |- d : c :: b : a $= ( inv ax-sym ) BADCABCDEFG $.
$}

${
  trc.1 $e |- a : b :: b : c $.
  trc.2 $e |- b : c :: c : d $.
  $( Central transitivity $)
  trc $p |- a : b :: c : d $= ( ax-tr ) ABBCCDEFG $.
$}

${
  trin.1 $e |- a : b :: c : d $.
  trin.2 $e |- b : e :: d : f $.
  $( Inner transitivity $)
  trin $p |- a : e :: c : f $= ( ax-exch ax-tr ) ACEFACBDEFABCDGIBEDFHIJI $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  EXAMPLE
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c nj nk lj lk $.
tnj $a term nj $.
tnk $a term nk $.
tlj $a term lj $.
tlk $a term lk $.

jkjk $a |- nj : nk :: lj : lk $.

$c intuitionistic classical $.
tj $a term intuitionistic $.
tk $a term classical $.

ijck $a |- intuitionistic : nj :: classical : nk $.

$c heyting peano $.
th $a term heyting $.
tp $a term peano $.

ihcp $a |- intuitionistic : heyting :: classical : peano $.

jhkp $p |- lj : heyting :: lk : peano $=
  ( tlj tj tlk tk th tp tnj tnk jkjk ax-exch inv ijck trin ihcp ) ABCDEFAGCHBDG
  AHCGHACIJKBGDHLKMNM $.

$(
###############################################################################
  DISANALOGIES
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  SYNTAX
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c >< $.
wd $a wff a : b >< c : d $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  AXIOMS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

ax-didl $a |- a : a >< c : d $.

${
  ax-dsym.1 $e |- a : b >< c : d $.
  $( Symmetry $)
  ax-dsym $a |- c : d >< a : b $.
$}

${
  ax-dinvl.1 $e |- a : b >< c : d $.
  ax-dinvl $a |- b : a >< c : d $.
$}

${
  ax-dtrl.1 $e |- a : b >< c : d $.
  ax-dtrl.2 $e |- a : b :: a' : b' $.
  $( Transport a disanalogy across an analogy on the left side. $)
  ax-dtrl $a |- a' : b' >< c : d $.
$}

${
  ax-dsep.1 $e |- a : b >< a : b $.
  ax-dsep $a |- a : b :: c : c $.
$}

$(
  @{
    ax-daddr.1 @e |- a : b >< c : d @.
    ax-daddr.2 @e |- a : b >< d : e @.
    @( Additivity of disanalogy on the right side. @)
    ax-daddr @a |- a : b >< c : e @.
  @}
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  THEOREMS
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

didr $p |- a : b >< c : c $= ( ax-didl ax-dsym ) CCABCABDE $.

${
  dinvr.1 $e |- a : b >< c : d $.
  dinvr $p |- a : b >< d : c $= ( ax-dsym ax-dinvl ) DCABCDABABCDEFGF $.
$}

${
  dinv.1 $e |- a : b >< c : d $.
  dinv $p |- b : a >< d : c $= ( dinvr ax-dinvl ) ABDCABCDEFG $.
$}

${
  dtrr.1 $e |- a : b >< c : d $.
  dtrr.2 $e |- c : d :: c' : d' $.
  $( Transport a disanalogy across an analogy on the right side. $)
  dtrr $p |- a : b >< c' : d' $= ( ax-dsym ax-dtrl ) EFABCDABEFABCDGIHJI $.
$}

${
  dtr.1 $e |- a : b >< c : d $.
  dtr.2 $e |- a : b :: a' : b' $.
  dtr.3 $e |- c : d :: c' : d' $.
  $( Transport a disanalogy across two analogies. $)
  dtr $p |- a' : b' >< c' : d' $= ( dtrr ax-dtrl ) ABGHEFABCDGHIKLJM $.
$}
