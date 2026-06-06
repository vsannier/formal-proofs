$( FOUR-TERMS ANALOGIES $)
$( This work by Victor Sannier is released under the MIT License. $)

$(
###############################################################################
  SYNTAX
###############################################################################
$)

$c term $.

$v a b c d e f $.
ta $f term a $.
tb $f term b $.
tc $f term c $.
td $f term d $.
te $f term e $.
tf $f term f $.

$c wff : :: $.
wa $a wff a : b :: c : d $.

$c |- $.

$(
###############################################################################
  AXIOMS
###############################################################################
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
###############################################################################
  THEOREMS
###############################################################################
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
###############################################################################
  EXAMPLE
###############################################################################
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
