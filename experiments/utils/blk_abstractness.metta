;; =============================================================================
;; Module: Partition Utilities
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Provides functions for manipulating logical partitions and subsets, including:
;;   - Clause extraction from expressions
;;   - Powerset generation
;;   - Partition generation
;;   - Set operations
;;
;; Dependencies:
;;   - Python backend for some partition generation functions
;; =============================================================================

! (import! &self partition)

;; =============================================================================
;; Function: get-clauses
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Extracts clauses from an expression, specifically handling AND-conjunctions
;;
;; Type Signature:
;;   (-> Expression Expression)
;;
;; Parameters:
;;   $element - Input expression to analyze
;;
;; Returns:
;;   - Body of expression if it's an AND-conjunction
;;   - Original expression otherwise
;;
;; Example:
;;   (get-clauses '(And A B C)) → (A B C)
;;   (get-clauses '(Or X Y)) → (Or X Y)
;; =============================================================================
; (: get-clauses (-> Expression Expression))
(= (get-clauses $element)
    (let $link (car-atom $element)
        (if (== $link ,)
            (cdr-atom $element)
            $element)))

;; =============================================================================
;; Function: add-to-subsets
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Adds an element to each subset in a list of subsets
;;
;; Type Signature:
;;   (-> Expression Expression Expression)
;;
;; Parameters:
;;   $element - Element to add
;;   $subsets - List of subsets to modify
;;
;; Returns:
;;   New list with element added to each subset
;;
;; Example:
;;   (add-to-subsets 'A '((B) (C))) → ((A B) (A C))
;; =============================================================================
(: add-to-subsets (-> Expression Expression Expression))
(= (add-to-subsets $element $subsets)
    (if (== $subsets ())
        ()
        (let* (
                ($head-sub (car-atom $subsets))
                ($tail-sub (cdr-atom $subsets))
                ($current (cons-atom $element $head-sub))
                ($rest (add-to-subsets $element $tail-sub)))
            (cons-atom $current $rest))))

;; =============================================================================
;; Function: concat-atom
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Concatenates two lists
;;
;; Parameters:
;;   $list1 - First list
;;   $list2 - Second list
;;
;; Returns:
;;   Combined list
;;
;; Example:
;;   (concat-atom '(A B) '(C D)) → (A B C D)
;; =============================================================================
(= (concat-atom $list1 $list2)
    (if (== $list1 ())
        $list2
        (let* (
                ($head (car-atom $list1))
                ($tail (concat-atom (cdr-atom $list1) $list2)))
            (cons-atom $head $tail))))

;; =============================================================================
;; Function: powerset
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Generates all possible subsets of a list (powerset)
;;
;; Type Signature:
;;   (-> Expression Expression)
;;
;; Parameters:
;;   $lst - Input list
;;
;; Returns:
;;   List of all subsets
;;
;; Example:
;;   (powerset '(A B)) → (() (A) (B) (A B))
;; =============================================================================
; (: powerset (-> Expression Expression))
(= (powerset $lst)
    (if (== $lst ())
        (cons-atom () ())
        (let* (
                ($rest (powerset (cdr-atom $lst)))
                ($with-current (add-to-subsets (car-atom $lst) $rest)))
            (concat-atom $rest $with-current))))

;; =============================================================================
;; Function: generet-partition-without-pattern
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Generates partitions from a pattern using Python backend
;;
;; Type Signature:
;;   (-> Expression Expression)
;;
;; Parameters:
;;   $pattern - Input pattern to partition
;;
;; Returns:
;;   List of generated partitions
;;
;; Process:
;;   1. Extracts clauses from pattern
;;   2. Generates subsets
;;   3. Calls Python partition generator
;;
;; Example:
;;   (generet-partition-without-pattern '(And A B C))
;;   → ((A B C)) or other valid partitions
;; =============================================================================
(: generet-partition-without-pattern (-> Expression Expression))
(= (generet-partition-without-pattern $pattern)
    (let* (
            ($clause (get-clauses $pattern))
            ($subsets (gen-subsets $clause)))
        (gen-partition $subsets $clause)))




(: Constant (-> String $a))

; Function to replace a variable with @var throughout a pattern
; Usage: (erase $pattern $var)
; Example: (erase ((Man $x Eyob) (Student $x Newyork)) $x)
; Result: ((Man @eyob Eyob) (Student @eyob Newyork))

(= (erase $pattern $var)
   (replace-var $pattern $var (Constant (repr $var))))

; Main replacement function using collapse and superpose
(= (replace-var $expr $var $replacement) 
   (collapse (replace-var-exp (superpose $expr) $var $replacement)))



; Replace variable in an expression 
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
; Check if two patterns can be unified after treating var as constant
; (= (can-unify $l_body $r_body $db)
;    (let*( 
    
;     ($conj-l (union-atom (,) $l_body))
;     ($conj-r (union-atom (,) $r_body))

;     ($value-l (collapse (match $db $conj-l $conj-l)))
;     ($value-r (collapse (match $db) $conj-r $conj-l)))

;     ($is-unify1 (== (subsctract-atom $value-l $value-r) ()))
;     ($is-unify2 (== (subsctract-atom $value-r $value-l) ()))

;     )

;     (Or $is-unify1 $is-unify2)  ; Both conditions must be true for unification

;    )
        

; (= (can-unify $l_body $r_body)
; (
;     let* (
;        ($- (!(bind! &left $l_body)) )
;        ($__ (!(bind! &right $r_body)) )
;        ($_ (println! (can un called with (&left) (&right))))
;     )
;     (unify &left &right True False)
; )
; )

; Main unification function for atom bodies
(= (can-unify $l_body $r_body)
   (if (== (size-atom $l_body) (size-atom $r_body))
       (let* (
           ($left_empty (== (size-atom $l_body) 0))
           ($right_empty (== (size-atom $r_body) 0))
       )
       (if (and $left_empty $right_empty)
           True
           (if (or $left_empty $right_empty)
               False
               (let* (
                    ($_ (println! (can-unify called with $l_body $r_body)))
                   ($l_head (car-atom $l_body))
                   ($l_tail (cdr-atom $l_body))
                   ($r_head (car-atom $r_body))
                   ($r_tail (cdr-atom $r_body))
                   ($head_unify (can-unify-expr $l_head $r_head))
               )
               (if $head_unify
                   (can-unify $l_tail $r_tail)
                   False)))))
       False))

(= (can-unify-expr ($link1 $pridicate1 $conclusion) ($link2 $pridicate2 $conclusion2)) 
    (
        if (== $link1 $link2)
            (let* (
                ($can-unify1 (can-unify-ground $pridicate1 $pridicate2))
                ($can-unify2 (can-unify-ground $conclusion $conclusion2))
            )
            (and $can-unify1 $can-unify2))
        
            False
    )
 
 )



(= (can-unify-ground $ground1 $ground2)
    (if (== $ground1 $ground2)
        True
        (if (or (== (get-metatype $ground1) Variable)
                (== (get-metatype $ground2) Variable))
                True
                False)
    )
)
; Main function: check if l_pat is more abstract than r_pat with respect to var
(= (is-blk-syntax-more-abstract $l_pat $r_pat $var)
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
    (
        let $part_wout-patt (generet-partition-without-pattern $conj-pattern)
            (union-atom (($conj-pattern)) $part_wout-patt )
    )

)





(= (is-blk-more-abstract $l_blk $r_blk $var) 
   (let* (
            ($rps (powerset-without-empity $r_blk))  ;; (((Man $x Job)))
            ($l_partitions (partition $l_blk))  ;; (((Man $x $y)))
            ; ($_ (println! (powerset------ $rps)))
            ; ($_ (println! (partition------ $l_partitions)))
        )
         (check-partitions $l_partitions $rps $var)
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







(= (connected-subpatterns-with-var $partition $var)
    (filter-blocks-with-var $partition $var ()))

;; Helper function to filter blocks recursively
(= (filter-blocks-with-var $partition $var $acc)
    (if (== $partition ())
        $acc
        (let* (
            ($current-block (car-atom $partition))
            ($remaining-blocks (cdr-atom $partition))
            ($connected-sub (connected-subpattern-with-var $current-block $var))
        )
        (if (== $connected-sub ())
            ;; No connected subpattern found, continue with next block
            (filter-blocks-with-var $remaining-blocks $var $acc)
            ;; Found connected subpattern, add to accumulator
            (let $new-acc (union-atom $acc ($connected-sub))
                (filter-blocks-with-var $remaining-blocks $var $new-acc)
            )
        ))))

(= (connected-subpattern-with-var $block $var)
    (if (not (is-var-exist $block $var))
        ()  ;; Variable not in block, return empty
        $block   ; TODO: we can extract one step down using extract function 
        ))

(= (extract $exp $var)  (
    if (var-exist-exp $exp $var) 
    $exp
    (empty)
    
))

(= (find-component-with-var $components $var)
    (collapse (extract (superpose $components) $var))
)










;; =============================================================================
;; Function: sort-by-abstraction
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Sorts a list of patterns based on abstraction level using is-blk-more-abstract
;;   More abstract patterns come first in the sorted result
;;
;; Type Signature:
;;   (-> Expression Expression Expression)
;;
;; Parameters:
;;   $patterns - List of patterns to sort
;;   $var - Variable to use for abstraction comparison
;;
;; Returns:
;;   Sorted list where more abstract patterns appear first
;;
;; Example:
;;   (sort-by-abstraction '(pattern1 pattern2 pattern3) $x)
;; =============================================================================
; (: sort-by-abstraction (-> Expression Expression Expression))
(= (sort-by-abstraction $patterns $var)
    (if (== $patterns ())
        ()
        (if (== (cdr-atom $patterns) ())
            $patterns  ; Single element list is already sorted
            (let* (
                ($pivot (car-atom $patterns))
                ($rest (cdr-atom $patterns))
                ($_ (println! (Rest $rest)))

                ($more-abstract (filter-more-abstract $rest $pivot $var))
                ($less-abstract (filter-less-abstract $rest $pivot $var))
                ($_ (println! (More-abstract $more-abstract)))
                ($_ (println! (less-abstract $less-abstract)))
                ($_ (println! (PIVOT $pivot)))

                ($sorted-less (sort-by-abstraction $less-abstract $var))
                ($sorted-more (sort-by-abstraction $more-abstract $var))
            )
            (concat-atom $sorted-more (cons-atom $pivot $sorted-less))))))

;; =============================================================================
;; Function: filter-more-abstract
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Filters patterns that are more abstract than the pivot
;;
;; Parameters:
;;   $patterns - List of patterns to filter
;;   $pivot - Pivot pattern for comparison
;;   $var - Variable for abstraction comparison
;;
;; Returns:
;;   List of patterns more abstract than pivot
;; =============================================================================
; (: filter-more-abstract (-> Expression Expression Expression Expression))
(= (filter-more-abstract $patterns $pivot $var)
    (if (== $patterns ())
        ()
        (let* (

            ($head (car-atom $patterns))
            ($copyHead (car-atom $patterns))
            ($tail (cdr-atom $patterns))
            ($rest-filtered (filter-more-abstract $tail $pivot $var))
        )
        (if (is-blk-more-abstract $head $pivot $var)
            (cons-atom $copyHead $rest-filtered)
            $rest-filtered))))

;; =============================================================================
;; Function: filter-less-abstract
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Filters patterns that are less abstract than the pivot
;;
;; Parameters:
;;   $patterns - List of patterns to filter
;;   $pivot - Pivot pattern for comparison
;;   $var - Variable for abstraction comparison
;;
;; Returns:
;;   List of patterns less abstract than pivot
;; =============================================================================
; (: filter-less-abstract (-> Expression Expression Expression Expression))
(= (filter-less-abstract $patterns $pivot $var)
    (if (== $patterns ())
        ()
        (let* (

            ($head (car-atom $patterns))
            ($copyHead (car-atom $patterns))
            ($tail (cdr-atom $patterns))
            ($rest-filtered (filter-less-abstract $tail $pivot $var))
        )
        (if (is-blk-more-abstract $head $pivot $var)
            $rest-filtered
            (cons-atom $copyHead $rest-filtered)))))




;  !(sort-by-abstraction (((Human $x $y) (Human $x $z)) ((Human $x Chala)) ) $x)


; (((Human $x $y) (Human Abebe $y))  ((Human $x Abeb)))

; (filter-less-abstract $rest $pivot $var)

; !(filter-more-abstract (((Human $x $y) (Human $x $z))) ((Human $x Chala)) $x)

; !(is-blk-more-abstract ((Human $y $x)) ((Human Abebe Chala))  $x)


















;; =============================================================================
;; Function: eq-prob
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Calculates the probability of a variable taking the same value across
;;   all blocks/subpatterns where that variable appears in a partition
;;
;; Type Signature:
;;   (-> Expression Expression Expression Number)
;;
;; Parameters:
;;   $partition - List of blocks/subpatterns 
;;   $pattern - The main pattern containing variables
;;   $db - Database/corpus to search in
;;
;; Returns:
;;   Probability value as a number
;;
;; Algorithm:
;;   1. For each joint variable in the pattern and partition
;;   2. Get connected subpatterns containing that variable
;;   3. Sort by abstraction level (most abstract first)
;;   4. For each block after the first, find most specialized abstract block
;;   5. Calculate probability based on value counts
;; =============================================================================
(: eq-prob (-> Expression Expression Expression Number))
(= (eq-prob $partition $pattern $db)
    (let $joint-vars (joint-variables $pattern $partition)
        (calculate-prob-for-vars $joint-vars $partition $db 1.0)))

;; =============================================================================
;; Function: calculate-prob-for-vars
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Iterates through variables and calculates cumulative probability
;;
;; Parameters:
;;   $vars - List of joint variables
;;   $partition - Partition to analyze
;;   $db - Database
;;   $p - Current probability accumulator
;;
;; Returns:
;;   Final probability after processing all variables
;; =============================================================================
(: calculate-prob-for-vars (-> Expression Expression Expression Number Number))
(= (calculate-prob-for-vars $vars $partition $db $p)
    (if (== $vars ())
        $p
        (let* (
            ($var (car-atom $vars))
            ($remaining-vars (cdr-atom $vars))
            ($var-partition (connected-subpatterns-with-var $partition $var))
            ($sorted-partition (sort-by-abstraction $var-partition $var))
            ($new-p (process-blocks $sorted-partition $var $db $p 1))
        )
        (calculate-prob-for-vars $remaining-vars $partition $db $new-p))))

;; =============================================================================
;; Function: process-blocks
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Processes blocks in sorted partition starting from index j=1
;;   (skipping the first block as per the C++ algorithm)
;;
;; Parameters:
;;   $sorted-partition - Partition sorted by abstraction
;;   $var - Current variable being processed
;;   $db - Database
;;   $p - Current probability
;;   $j - Current block index (starts at 1)
;;
;; Returns:
;;   Updated probability after processing all blocks
;; =============================================================================
; (: process-blocks (-> Expression Expression Expression Number Number Number))
(= (process-blocks $sorted-partition $var $db $p $j)
    (let $partition-size (size-atom $sorted-partition)
        (if (>= $j $partition-size)
            $p
            (let* (
                ($j-blk (index-atom $sorted-partition $j))
                ($i (find-most-specialized-abstract $sorted-partition $j-blk $var (- $j 1)))
                ($c (if (>= $i 0)
                        (let $i-blk (index-atom $sorted-partition $i)
                            (value-count $i-blk $var $db))
                        (size-atom (get-atoms $db))))  ; Use |U| = db.size() as fallback
                ($new-p (/ $p $c))
            )
            (process-blocks $sorted-partition $var $db $new-p (+ $j 1))))))



(= (value-count $blk $var $db) 
    (let $conj-blk (union-atom (,) $blk) (let $ground-value (unique-atom (collapse (match $db $conj-blk $var))) (size-atom $ground-value))))
;; =============================================================================
;; Function: find-most-specialized-abstract
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Finds the most specialized block that is more abstract than j_blk
;;   Goes backward from j_blk to find first i_blk that is more abstract
;;
;; Parameters:
;;   $partition - Sorted partition
;;   $j-blk - Current block to compare against
;;   $var - Variable for abstraction comparison
;;   $i - Current index to check (starts at j-1)
;;
;; Returns:
;;   Index of most specialized abstract block, or -1 if none found
;; =============================================================================
; (: find-most-specialized-abstract (-> Expression Expression Expression Number Number))
(= (find-most-specialized-abstract $partition $j-blk $var $i)
    (if (< $i 0)
        -1  ; No abstract block found
        (let $i-blk (index-atom $partition $i)
            (if (is-blk-more-abstract $i-blk $j-blk $var)
                $i  ; Found the most specialized abstract block
                (find-most-specialized-abstract $partition $j-blk $var (- $i 1))))))

;; =============================================================================
;; Helper Functions
;; =============================================================================



;; =============================================================================
;; Function: get-var
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Extracts all variables from a flattened pattern expression
;;   A flattened pattern is a list of patterns like ((Pattern $x $y) (Pattern $z Jon))
;;
;; Type Signature:
;;   (-> Expression Expression)
;;
;; Parameters:
;;   $pattern - Flattened pattern (list of individual patterns)
;;
;; Returns:
;;   List of unique variables found in the pattern
;;
;; Example:
;;   (get-var '((Pattern $x $y) (Pattern $z Jon))) → ($x $y $z)
;; =============================================================================
(: get-var (-> Expression Expression))
(= (get-var $pattern)
    (unique-list (extract-vars-from-pattern $pattern ())))

;; Helper function to recursively extract variables from pattern
(: extract-vars-from-pattern (-> Expression Expression Expression))
(= (extract-vars-from-pattern $pattern $acc)
    (if (== $pattern ())
        $acc
        (let* (
            ($current-expr (car-atom $pattern))
            ($remaining (cdr-atom $pattern))
            ($expr-vars (extract-vars-from-expr $current-expr))
            ($new-acc (merge-list $acc $expr-vars))
        )
        (extract-vars-from-pattern $remaining $new-acc))))

;; Extract variables from a single expression
(: extract-vars-from-expr (-> Expression Expression))
(= (extract-vars-from-expr $expr)
    (if (== $expr ())
        ()
        (let* (
            ($head (car-atom $expr))
            ($tail (cdr-atom $expr))
            ($head-vars (if (== (get-metatype $head) Variable)
                           ($head)
                           ()))
            ($tail-vars (extract-vars-from-expr $tail))
        )
        (merge-list $head-vars $tail-vars))))

;; =============================================================================
;; Function: joint-variables
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Finds variables that appear in multiple blocks of a partition
;;   A joint variable must exist in at least 2 different blocks
;;
;; Type Signature:
;;   (-> Expression Expression Expression)
;;
;; Parameters:
;;   $pattern - Flattened pattern to get variables from
;;   $partition - List of blocks (each block is a list of patterns)
;;
;; Returns:
;;   List of variables that appear in multiple blocks
;;
;; Example:
;;   Pattern: ((Pattern $x $y) (Pattern $x Jon))  
;;   Partition: ( ((Pattern $x Jon))  ((Pattern $x $y)) )  
;;   Result: ($x $y) - because they appear in both blocks, $z only in first block
;; =============================================================================
; (: joint-variables (-> Expression Expression Expression))
(= (joint-variables $pattern $partition)
    (let $pattern-vars (get-var $pattern)   
        (filter-joint-vars $pattern-vars $partition))) 

;; Filter variables that appear in multiple blocks
; (: filter-joint-vars (-> Expression Expression Expression))
(= (filter-joint-vars $vars $partition)
    (if (== $vars ())
        ()
        (let* (
            ($var (car-atom $vars))
            ($remaining-vars (cdr-atom $vars))
            ($rest-joint (filter-joint-vars $remaining-vars $partition))
        )
        (if (is-joint-var $var $partition)
            (cons-atom $var $rest-joint)
            $rest-joint))))

;; Check if a variable appears in multiple blocks of partition
(: is-joint-var (-> Expression Expression Bool))
(= (is-joint-var $var $partition)
    (let $block-count (count-blocks-with-var $var $partition 0)
        (> $block-count 1)))

;; Count how many blocks contain the variable
(: count-blocks-with-var (-> Expression Expression Number Number))
(= (count-blocks-with-var $var $partition $count)
    (if (== $partition ())
        $count
        (let* (
            ($current-block (car-atom $partition))
            ($remaining-blocks (cdr-atom $partition))
            ($var-in-block (is-var-exist $current-block $var))
            ($new-count (if $var-in-block (+ $count 1) $count))
        )
        (count-blocks-with-var $var $remaining-blocks $new-count))))

;; Get all variables from entire partition (updated implementation)
(: get-all-partition-variables (-> Expression Expression))
(= (get-all-partition-variables $partition)
    (if (== $partition ())
        ()
        (let* (
            ($block (car-atom $partition))
            ($remaining (cdr-atom $partition))
            ($block-vars (get-var $block))
            ($remaining-vars (get-all-partition-variables $remaining))
        )
        (merge-list $block-vars $remaining-vars))))

;; Find intersection of two variable lists
(: intersection-vars (-> Expression Expression Expression))
(= (intersection-vars $vars1 $vars2)
    (if (== $vars1 ())
        ()
        (let* (
            ($var (car-atom $vars1))
            ($remaining (cdr-atom $vars1))
            ($rest-intersection (intersection-vars $remaining $vars2))
        )
        (if (is-membership $var $vars2)
            (cons-atom $var $rest-intersection)
            $rest-intersection))))






! (add-reduct &self (= (get-space) (new-space)))
! (add-atom (get-space) (Inheritance Abe human))
! (add-atom (get-space) (Inheritance Rio human))
! (add-atom (get-space) (Inheritance Bob human))
! (add-atom (get-space) (Inheritance Mike human))
!(add-atom (get-space) (Eyob $x Meti))



; (= (eq-prob $partition $pattern $db)
; !(can-unify ((Inheritance $x human) (Inheritance Rio $y)) ((Inheritance Abe $y)))
; !(can-unify ((Inheritance $x human))  ((Inheritance $x human)))

; !(sort-by-abstraction (((Human $x Chala)) ((Human $x $y)) ((Human Eyob Chala)) ) $x)

; !(match (get-space) (Eyob $y $z) ($z $y))

; !(can-unify ((Human $x $z)) ((Human $x Chala)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



; !(partition (A B C))

; (
;     ((A B C)) 
;     ((A B) (C)) 
;     ((A C) (B)) 
;     ((A) (B) (C)) 
;     ((A) (B C))
; )


; !(is-blk-syntax-more-abstract ((Inheritance $y $x)) ((Inheritance $z $y)) $y)