
! (register-module! ../../../../hyperon-miner)
! (import! &self hyperon-miner:experiments:frequent-pattern-miner:conjunction-expansion)
! (import! &self hyperon-miner:experiments:utils:common-utils)
! (import! &self hyperon-miner:experiments:frequent-pattern-miner:conj-exp)


!(assertEqual (get_variable_for_pattern (link $x $y)) ($x $y))
!(assertEqual (get_variable_for_pattern (link $x (link $y $z))) ($x $y $z))
!(assertEqual (get_variable_for_pattern (link $x (link $y (link $z $t)))) ($x $y $z $t))
!(assertEqual (get_variable_for_pattern  (link (link (link $s $k) (link $n $m)) (link (link $g $t) (link $p $r)))) ($s $k $n $m $g $t $p $r))


!(assertEqual (substitute (link $x $y) ($a $b)) ((link $a $b) ()))
!(assertEqual (substitute ($LIST_LINK (INHERITANCE_LINK (INHERITANCE_LINK $S $K) (INHERITANCE_LINK $n $m)) (INHERITANCE_LINK (INHERITANCE_LINK $g $t) (INHERITANCE_LINK $p $r))) ($R-D1737102179 $A $b $c $d $e $f $h)) (($R-D1737102179 (INHERITANCE_LINK (INHERITANCE_LINK $A $b) (INHERITANCE_LINK $c $d)) (INHERITANCE_LINK (INHERITANCE_LINK $e $f) (INHERITANCE_LINK $h $r))) ()))


(INHERITANCE_LINK A B)
(LIST_LINK A B)
(LIST_LINK A C)
(LIST_LINK B C)
(INHERITANCE_LINK A D)
(INHERITANCE_LINK X Y)
(LIST_LINK Y C)
(INHERITANCE_LINK X D)

!(expand_conjunction (,(INHERITANCE_LINK $X $Y) (LIST_LINK A $D)) (LIST_LINK $G $F) &self 5 2 False)
; expected:
    ; (, (, (INHERITANCE_LINK $X $Y) (LIST_LINK A $D)) (LIST_LINK $X $G)),
    ; (, (, (INHERITANCE_LINK $X $Y) (LIST_LINK A $D)) (LIST_LINK $X $F)), 
    ; (, (, (INHERITANCE_LINK $X $Y) (LIST_LINK A $D)) (LIST_LINK $G $D)),
    ; (, (, (INHERITANCE_LINK $X $Y) (LIST_LINK A $D)) (LIST_LINK $F $D))