#lang typed/racket
(require/typed "simp1.rkt"
               [id (-> Integer String)])
(id 2)