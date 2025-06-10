
!(import! &self  emp-tv-bs)


;; =============================================================================
;; Function: subsample-py
;; -----------------------------------------------------------------------------
;; Purpose:
;;   Creates a random subsample from a database by selecting a specified number
;;   of atoms and placing them in a new space.
;;
;; Inputs:
;;   - `$db`: The source database/space to subsample
;;   - `$subsize`: The number of atoms to include in the subsample
;;
;; Output:
;;   - A new space containing the randomly selected atoms
;;
;; How it works:
;;   1. Extracts all atoms from the source database using `get-atoms`
;;   2. Collapses the result into a flat list
;;   3. Randomly selects `$subsize` atoms using `generet_random_subsample`
;;   4. Creates a copy of the selected atoms in a new space
;;

;; =============================================================================
(= (subsample-py $db $subsize)
    (let* (
            ($db-content (collapse (get-atoms $db)))
            ($random-selected (generet_random_subsample $db-content $subsize))
            ($space (copy-db (new-space) $random-selected)))
        $space
    )
)

(= (avrg-tv-py $x) (mean-tv $x))

(= (get-element-by-Index $list $index)
       (index-atom $list $index)
)
      

(= (random-element $db)
   (let* (
           ($list (collapse (get-atoms $db)))
           ($length (size-atom $list))
           ($index (random-int 0 $length))
           ($element (get-element-by-Index $list $index))
         )
         $element))

(= (generet-random-subsample $db $subsize)
   (if (== $subsize 0)
       ()
       (let* (             
               ($elements (random-element $db))
               ($_ (println "Selected element: " $elements))
               ($tail-elements (generet-random-subsample $db (- $subsize 1)))
             )
             (cons-atom $elements $tail-elements)
       )
   )
)

