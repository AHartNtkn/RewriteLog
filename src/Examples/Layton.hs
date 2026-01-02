module Examples.Layton (runLayton, runLaytonSmall) where

import Control.Monad.Free (Free(..))
import Constraint
import RelExp
import SExpF

a :: Free SExpF Int -> Free SExpF Int
a = cons (atom "a")

b :: Free SExpF Int -> Free SExpF Int
b = cons (atom "b")

s :: Free SExpF Int -> Free SExpF Int
s = cons (atom "s")

laytonCheck :: RelExp SExpF EmptyConstraint
laytonCheck = 
    mkOr [
        rw (cons (atom "z") (cons (atom "nil") (atom "nil")))
           (atom "ok"),

        mkComp [
            mkOr [
                rw (cons (s (var 2)) (cons (a (var 0)) (a (var 1))))
                   (cons (var 2) (cons (var 0) (var 1))),
                rw (cons (s (var 2)) (cons (b (var 0)) (b (var 1))))
                   (cons (var 2) (cons (var 0) (var 1)))
            ],
            laytonCheck
        ],

        mkComp [
            mkOr [
                rw (cons (var 2) (cons (a (var 0)) (b (var 1))))
                   (cons (var 2) (cons (var 0) (var 1))),
                rw (cons (var 2) (cons (b (var 0)) (a (var 1))))
                   (cons (var 2) (cons (var 0) (var 1)))
            ],
            laytonCheck
        ]
    ]

-- bbababbabb = 7
stA1 = b (b (a (b (a (b (b (a (b (b (atom "nil"))))))))))
scA1 = s (s (s (s (s (s (s (atom "z")))))))

-- baaababaaa = 5
stA2 = b (a (a (a (b (a (b (a (a (a (atom "nil"))))))))))
scA2 = s (s (s (s (s (atom "z")))))

-- baaabbbaba = 3
stA3 = b (a (a (a (b (b (b (a (b (a (atom "nil"))))))))))
scA3 = s (s (s (atom "z")))

-- bbaaabbaaa
stA4 = b (b (a (a (a (b (b (a (a (a (atom "nil"))))))))))

laytonCase :: Free SExpF Int -> Free SExpF Int -> RelExp SExpF EmptyConstraint
laytonCase st sc = 
    mkComp [
        rw (var 0) (cons sc (cons (var 0) st)),
        laytonCheck,
        rw (atom "ok") (var 0)
    ]

layton :: RelExp SExpF EmptyConstraint
layton = 
    mkAnd [
        laytonCase stA1 scA1,
        laytonCase stA2 scA2,
        laytonCase stA3 scA3,
        mkComp [
            rw (var 0) (cons (var 1) (cons (var 0) stA4)),
            mkAnd [ 
                mkComp [laytonCheck, rw (atom "ok") (var 0)],
                rw (cons (var 1) (cons (var 0) stA4)) (var 1)
            ]
        ]
    ]

laytonSmall :: RelExp SExpF EmptyConstraint
laytonSmall = 
    mkAnd [
        laytonCase (b (a (atom "nil"))) (atom "z"),
        laytonCase (a (a (atom "nil"))) (s (atom "z")),
        laytonCase (b (b (atom "nil"))) (s (atom "z")),
        rw (var 0) (var 0)
    ]

runLayton :: [RelExp SExpF EmptyConstraint]
runLayton = run layton

runLaytonSmall :: [RelExp SExpF EmptyConstraint]
runLaytonSmall = run laytonSmall