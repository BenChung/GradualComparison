#lang typed/racket

(module u racket
  (define (id x) x)
  (provide id))

(require/typed 'u [id (-> Any Any)]
                  [{id id2} (-> Integer Integer)])
