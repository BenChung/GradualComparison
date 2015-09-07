#lang racket
(require parser-tools/lex)
(require parser-tools/yacc)

(define-tokens a (NUM ID))
(define-empty-tokens b (OC CC OP CP COLON CLASS IF0 THEN ELSE END EOF EQUALS ANY INT PLUS DOT COMMA))

(define lex (lexer
             [(concatenation alphabetic (repetition 0 +inf.0 (union alphabetic numeric)))
              (cons `(token-ID ,(string->symbol lexeme))
                    (lex input-port))]
             [numeric
              (cons `(token-NUM ,(string->symbol lexeme))
                    (lex input-port))]
             [#\{
              (cons `(token-OC) (lex input-port))]
             [#\}
              (cons `(token-CC) (lex input-port))]
             [#\(
              (cons `(token-OP) (lex input-port))]
             [#\)
              (cons `(token-CP) (lex input-port))]
             [#\:
              (cons `(token-COLON) (lex input-port))]
             [#\=
              (cons `(token-EQUALS) (lex input-port))]
             [#\+
              (cons `(token-PLUS) (lex input-port))]
             [#\.
              (cons `(token-DOT) (lex input-port))]
             [#\,
              (cons `(token-COMMA) (lex input-port))]
             ["class"
              (cons `(token-CLASS) (lex input-port))]
             ["if0"
              (cons `(token-IF0) (lex input-port))]
             ["then"
              (cons `(token-THEN) (lex input-port))]
             ["else"
              (cons `(token-ELSE) (lex input-port))]
             ["end"
              (cons `(token-END) (lex input-port))]
             ["any"
              (cons `(token-ANY) (lex input-port))]
             ["int"
              (cons `(token-INT) (lex input-port))]
             [whitespace (lex input-port)]
             [(eof) (token-EOF)]
             ))

(define parse (parser
               (start classes)
               (end EOF)
               (tokens a b)
               (error void)
               (precs (left PLUS DOT))
               (grammar
                (classes ((class classes) (cons $1 $2))
                         ((class) (cons $1 null)))
                (class [(CLASS ID OC classbody CC) $2])
                (classbody
                 [(classelem classbody)(cons $1 $2)]
                 [(classelem) (cons $1 null)]
                 )
                (classelem
                 [(field) $1]
                 [(method) $1]
                 )
                (field
                 [(ID COLON type EQUALS exp) 2]
                 [(ID EQUALS exp) 2]
                 )
                (method
                 [(ID argdecls COLON type OC body CC) 2]
                 [(ID argdecls OC body CC) 2]
                 )
                (type [(ANY) 1] [(INT) 2] [(ID) 3])
                (argdecls
                 [(OP iargs CP) 1]
                 [(OP CP) 2]
                 )
                (iargs
                 [(arg COMMA iargs) 1]
                 [(arg) 2])
                (arg
                  [(ID COLON type) 1]
                  [(ID) 2]
                  )
                (body
                 [(bodyexpr body) 1]
                 [(bodyexpr) 1]
                 )
                (bodyexpr
                 [(exp) 1]
                 [(ID EQUALS exp) 2]
                 )
                (exp
                 [(NUM) $1]
                 [(exp PLUS exp) 2]
                 [(ID) 3]
                 [(exp DOT ID OP args CP) 4]
                 [(OP exp CP) 5]
                 )
                (args
                 [(arg COMMA args) 1]
                 [(arg) 2]
                 [() 3])
                )))