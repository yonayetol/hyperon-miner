; !(import! &self ../../data/ugly_man_sodaDrinker)
!(import! &self ../../data/small-ugly)

;; lets transfer this data to other space
!(bind! dataBase (new-space))
!(let* 
    (
        ($x (get-atoms &self))
        ($debug1 (remove-atom &self $x))
        ($debug2 (add-atom dataBase $x))
    ) ())
; !(get-atoms dataBase)

!(import! &self ../Updated-frequent-pattern-miner)
!(import! &self ../Updated-conjunction-expansion)
!(import! &self ../frequentMinerHelperFunctions)
; !(get-atoms &self)

;; space for the final conjuncts
!(bind! conjunctSpace (new-space))

; !(frequency-pattern-miner dataBase-space conjunct-Space min-Support number-of-pattern-in-one-conjunct minus 2)
!(frequency-pattern-miner dataBase conjunctSpace 2 1)

