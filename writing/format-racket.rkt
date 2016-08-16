#lang racket

(require pict
         pict/code
         racket/cmdline
         racket/draw)

(define-values (inp out) (command-line
 #:program "racket-formatter"
 #:args (input output)
 (values input output)))

(current-code-font "CMU Typewriter Text")

(define src (string-replace (file->string inp) "\r\n" "\n"))
(define pic (codeblock-pict src))


(define lnums (apply vl-append
       (for/list ([i (in-range 1 (+ (length (regexp-match* "\n" src)) 2))])
         ((current-code-tt) (number->string i)))))
(define outpict (hc-append 5 lnums pic))


(define psopts (new ps-setup%))
(send psopts set-margin 0 0)
(current-ps-setup psopts)

(define output (new pdf-dc%
                    [interactive #f]
                    [parent #f]
                    [width (pict-width outpict)]
                    [height (pict-height outpict)]
                    [use-paper-bbox #f]
                    [output out]))

(send output start-doc "")
(send output start-page)
(draw-pict outpict output 0 0)
(send output end-page)
(send output end-doc)

