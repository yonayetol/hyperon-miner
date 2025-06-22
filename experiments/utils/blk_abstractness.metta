
; Function to replace a variable with @var throughout a pattern
; Usage: (erase $pattern $var)
; Example: (erase ((Man $x Eyob) (Student $x Newyork)) $x)
; Result: ((Man @eyob Eyob) (Student @eyob Newyork))

(= (erase $pattern $var)
   (replace-var $pattern $var @eyob))

; Main replacement function using collapse and superpose
(= (replace-var $expr $var $replacement) 
   (collapse (replace-var-exp (superpose $expr) $var $replacement)))



; Replace variable in an expression (handles binary expressions)
(= (replace-var-exp $exp $var $replacement)  
   (let* (
       (($link $var1 $var2) $exp)
       ($subvar1 (sub-var $var1 $var $replacement))
       ($subvar2 (sub-var $var2 $var $replacement)) 
   )
   ($link $subvar1 $subvar2)))


; Substitute variable in a single atom
(= (sub-var $atom $var $replacement)  
   (if (== (get-metatype $atom) Variable)
       (if (== $atom $var)
           $replacement
           $atom)
       $atom))


; Check if variable exists in a single expression
(= (var-exist-exp $exp $var)  
   (let ($link $var1 $var2) $exp
       (or (== $var1 $var) (== $var2 $var))))

; Check if variable exists in the entire pattern
(= (is-var-exist $exp $var) 
   (if (== $exp ())
       False
       (if (var-exist-exp (car-atom $exp) $var) 
           True
           (is-var-exist (cdr-atom $exp) $var))))

; Get all variables from a pattern
(= (get-variables $pattern)
   (collapse (get-vars-exp (superpose $pattern))))

(= (get-vars-exp $exp)
   (let (($link $var1 $var2) $exp)
       (superpose ($var1 $var2))))

; Check if two patterns can be unified after treating var as constant
(= (can-unify $l_body $r_body)
   ; Simplified unification check - in practice this would be more complex
   (unify $l_body $r_body True False))

; Main function: check if l_pat is more abstract than r_pat with respect to var
(= (is-pat-syntax-more-abstract $l_pat $r_pat $var)
   (let* (
       ; Check if var exists in both patterns
       ($l_has_var (is-var-exist $l_pat $var))
       ($r_has_var (is-var-exist $r_pat $var))
       
       ; If var is not in both patterns, return False
       ($both_have_var (and $l_has_var $r_has_var))
   )
   (if (not $both_have_var)
       False
       (let* (
           ; Convert var to constant (@eyob) in both patterns
           ($l_body (erase $l_pat $var))
           ($r_body (erase $r_pat $var))
           
           ; Try to unify the modified patterns
           ($can_unify_result (can-unify $l_body $r_body))
       )
       $can_unify_result))))






(= (powerset-without-empity $list) 
    (collapse 
        (subtraction 
            (superpose (powerset $list)) 
            (superpose (()))
        )
    )
)


(= (partition $conj-pattern)  
    ; (
    ;     let $part_wout-patt (generet-partition-without-pattern $conj-pattern)
    ;         (cons-atom $conj-pattern $part_wout-patt )
    ; )

    (((Man $x $y)))
)





(= (is-blk-more-abstract $l_blk $r_blk $var)
   (let* (($rps (powerseq-without-empty $r_blk))
         ($l_partitions (partition $l_blk)))
   ))


(= (check-partitions $partitions $rps $var)
   (if (== $partitions ())
       False  ; No more partitions, return False
       (let $lp (car-atom $partitions)
         (if (check-subsets $lp $rps $var)
             True  ; Found valid combination
             (check-partitions (cdr-atom $partitions) $rps $var)))))  ; Try next partition

;; Check each subset in rps for current partition lp (flat list)
(= (check-subsets $lp $subsets $var)
   (if (== $subsets ())
       False  ; No more subsets, return False
       (let $rs (car-atom $subsets)
         (if (check-all-blocks $lp $rs $var)
             True  ; All blocks match with this subset
             (check-subsets $lp (cdr-atom $subsets) $var)))))  ; Try next subset

;; Check if all blocks in partition match the current subset (flat list)
(= (check-all-blocks $blocks $rs $var)
   (if (== $blocks ())
       True   ; All blocks checked, return True
       (let $lb (car-atom $blocks)
         (if (is-blk-syntax-more-abstract $lb $rs $var)
             (check-all-blocks (cdr-atom $blocks) $rs $var)  ; Continue checking
             False))))  ; One block failed, return False


(: is-membership (-> $a Expression Bool))
(= (is-membership $elem $list) (
    if (== $list ())
    False
    (let ($head $tail) (decons-atom $list)
        (if (== $head $elem)
            True
            (is-membership $elem $tail)
        ) 

    )

))
; (: merge-list (-> Expression Expression Expression))
(= (merge-list $list1 $list2)  (unique-list (union-atom  $list1 $list2)))
; (: unique-list (-> Expression Expression))
(= (unique-list $list)
    (uniq $list ())
)
; (: uniq (-> Expression Exprssion Expression))
(= (uniq $list1  $acc)
    (if (== $list1 ())
        $acc
        (let* (
            (($head $tail) (decons-atom $list1))
        )
            (if (is-membership $head $acc)
                (uniq $tail $acc)
                (let $newAcc (union-atom  $acc ($head))
                    (uniq $tail $newAcc) 
                )
            )
        )
    )

)





! (is-blk-more-abstract ((Man $x $y)) ((Man $x Job)) $x)