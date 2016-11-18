#lang typed/racket
(require/typed "simp1.rkt"
               [id (-> Integer Integer)])
(id 2)