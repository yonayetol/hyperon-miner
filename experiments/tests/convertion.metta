; ;; Helper function to check if a variable appears in a single expression
; (= (var-in-expr $var $expr)
;    (if (== $var $expr) 
;        True
;        (if (== () $expr)
;            False
;            (if (== $expr (quote $expr))  ;; If it's atomic and not the variable
;                False
;                (or (var-in-expr $var (car $expr))
;                    (var-in-expr $var (cdr $expr)))))))

; ;; Helper function to check if a variable appears in any expression within a bulk
; (= (var-in-bulk $var $bulk)
;    (if (== () $bulk)
;        False
;        (or (var-in-expr $var (car $bulk))
;            (var-in-bulk $var (cdr $bulk)))))

; ;; Helper function to count how many bulks contain a variable
; (= (count-bulks-with-var $var $partitions)
;    (if (== () $partitions)
;        0
;        (+ (if (var-in-bulk $var (car $partitions)) 1 0)
;           (count-bulks-with-var $var (cdr $partitions)))))

; ;; Helper function to check if a variable appears in more than one bulk
; (= (is-common-var $var $partitions)
;    (> (count-bulks-with-var $var $partitions) 1))

; ;; Main function to find common variables using filter-like approach
; (= (find-common-variables $partitions $variables)
;    (filter-vars $partitions $variables))

; ;; Filter implementation for variables
; (= (filter-vars $partitions ())
;    ())
; (= (filter-vars $partitions $variables)
;    (if (== () $variables)
;        ()
;        (if (is-common-var (car $variables) $partitions)
;            (cons (car $variables) (filter-vars $partitions (cdr $variables)))
;            (filter-vars $partitions (cdr $variables)))))

; ;; Example usage:
; ;; Test with your example
; (= test-partitions ((Inheritance $x man) (Inheritance $x ugly) (Inheritance $x sodaDrinker)))
                  

; (= test-variables ($x $y $z))

; ;; This should return ($x $y) since both appear in multiple partitions
; ; !(find-common-variables test-partitions test-variables)

; ; // single experesion checking if it has the same var 
; (= (has-var $var $expr)
;    (if (== $var $expr)
;        True
;       (or (has-var $var (car-atom $expr))
;       (has-var $var (cdr-atom $expr)))))

; !(has-var $x (Inheritance $x job))

;; Function to get all variables from an expression and use metta-type so that each valueinside the expression are a variable if it is we collect them and return 

; (= (merge-list $list1 $list2) (collapse (unique (union (superpose $list1) (superpose $list2)))))
(= (merge-list $list1 $list2)  (let $x (union-atom $list1  $list2) (unique-atom $x)))


(= (get-variables-from-expression $expression)
    (let ($link $x $y) $expression
        (
            (if (== (get-metatype $x) Variable) $x ())
            (if (== (get-metatype $y) Variable) $y ())))
)
    
;; Function to get all variables from a partition which are unique 
;; partition is a list of expressions so I want to extract all 

(= (get-variables $partition) (
    if (== ($partition) ()) ()
    (let* (
        ($out1 (get-variables-from-expression (car-atom $partition)))
        ($_ (println! $out1))
        ($out2 (get-variables-from-expression (cdr-atom $partition)))
    ) (merge-list $out1 $out2) )
))


; !(get-variables ((Inheritance $X $y)))
!(merge-list (A $x $x) (C D D $b $x))

; !(unique (superpose ($x $y $z $x)))
; !((== $X $X))
; ; !(union (superpose ()) (superpose (b c c d)))


