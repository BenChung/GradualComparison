#lang racket
(require parser-tools/lex)

(define lex (lexer
             [(concatenation alphabetic (repetition 0 +inf.0 (union alphabetic numeric)))
              (cons `(ID ,(string->symbol lexeme))
                    (lex input-port))]
             [numeric
              (cons `(NUM ,(string->symbol lexeme))
                    (lex input-port))]
             [#\{
              (cons `(OC) (lex input-port))]
             [#\}
              (cons `(CC) (lex input-port))]
             [#\:
              (cons `(COLON) (lex input-port))]
             ["class"
              (cons `(CLASS) (lex input-port))]
             ["if0"
              (cons `(IF0) (lex input-port))]
             ["then"
              (cons `(THEN) (lex input-port))]
             ["else"
              (cons `(ELSE) (lex input-port))]
             ["end"
              (cons `(END) (lex input-port))]
             [whitespace (lex input-port)]
             ))