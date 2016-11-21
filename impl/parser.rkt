#lang racket
(require parser-tools/lex)
(require parser-tools/yacc)

(define-tokens a (NUM ID STRING))
(define-empty-tokens b (OC CC OA CA OP CP COLON CLASS IF0 THEN ELSE END
                           EOF EQUALS ANY INT PLUS DOT COMMA BANG SEMICOLON IMPLEMENTS NEW
                           STR))

(define lex (lexer
             [(union (concatenation #\- numeric) numeric)
              (token-NUM (string->number lexeme))]
             [#\{ (token-OC)]
             [#\} (token-CC)]
             [#\< (token-OA)]
             [#\> (token-CA)]
             [#\( (token-OP)]
             [#\) (token-CP)]
             [#\: (token-COLON)]
             [#\= (token-EQUALS)]
             [#\+ (token-PLUS)]
             [#\. (token-DOT)]
             [#\, (token-COMMA)]
             [#\! (token-BANG)]
             [#\; (token-SEMICOLON)]
             ["class" (token-CLASS)]
             ["implements" (token-IMPLEMENTS)]
             ["if0" (token-IF0)]
             ["then" (token-THEN)]
             ["else" (token-ELSE)]
             ["end" (token-END)]
             ["any" (token-ANY)]
             ["int" (token-INT)]
             ["str" (token-STR)]
             ["new" (token-NEW)]
             [(concatenation alphabetic (repetition 0 +inf.0 (union alphabetic numeric #\_)))
              (token-ID lexeme)]
             [(concatenation #\" (repetition 0 +inf.0 (char-complement #\")) #\")
              (token-STRING (substring lexeme 1 (- (string-length lexeme) 1)))]
             [whitespace (lex input-port)]
             [(eof) (token-EOF)]
             ))

(define-struct class-decl (name implements body) #:transparent)
(define-struct method-decl (name args type body) #:transparent)
(define-struct field-decl (name type) #:transparent)
(define-struct arg-decl (name type) #:transparent)

(define-struct tany ())
(define-struct tint ())
(define-struct tstr ())
(define-struct tclass (name) #:transparent)
(define-struct tsclass (name) #:transparent)

(define-struct exp-assign (target value) #:transparent)
(define-struct exp-plus (left right) #:transparent)
(define-struct exp-var (name) #:transparent)
(define-struct exp-call (target name args) #:transparent)
(define-struct exp-self-call (name args) #:transparent)
(define-struct exp-if0 (cond then else) #:transparent)
(define-struct exp-cast (type value) #:transparent)
(define-struct exp-new (name args) #:transparent)

(define parse (parser
               (start classes)
               (end EOF)
               (tokens a b)
               
               (error (lambda (a b c) (write (list "error" a b c)) (newline)))
               (precs (left PLUS DOT CA))
               (debug "debug-parser.txt")
               (yacc-output "yacc-parser.txt")
               (grammar
                (classes ((class classes) (cons $1 $2))
                         ((class) (cons $1 null)))
                (class [(CLASS ID OC classbody CC) (class-decl $2 null $4)]
                  [(CLASS ID IMPLEMENTS ids OC classbody CC) (class-decl $2 $4 $6)])
                (ids [(ID COMMA ids) (cons $1 $3)] [(ID) (cons $1 null)])
                (classbody
                 [(classelem classbody)(cons $1 $2)]
                 [() null]
                 )
                (classelem
                 [(field) $1]
                 [(method) $1]
                 )
                (field
                 [(ID COLON type) (field-decl $1 $3)]
                 [(ID) (field-decl $1 (tany))]
                 )
                (method
                 [(ID argdecls COLON type OC body CC) (method-decl $1 $2 $4 $6)]
                 [(ID argdecls OC body CC) (method-decl $1 $2 (tany) $4)]
                 )
                (type [(ANY) (tany)] [(INT) (tint)] [(ID) (tclass $1)]
                      [(STR) (tstr)] [(BANG ID) (tsclass $2)])
                (argdecls
                 [(OP iargs CP) $2]
                 [(OP CP) null]
                 )
                (iargs
                 [(arg COMMA iargs) (cons $1 $3)]
                 [(arg) (cons $1 null)])
                (arg
                  [(ID COLON type) (arg-decl $1 $3)]
                  [(ID) (arg-decl $1 (tany))]
                  )
                (body
                 [(bodyexpr SEMICOLON body) (cons $1 $3)]
                 [(bodyexpr) (cons $1 null)]
                 )
                (bodyexpr
                 [(exp) $1]
                 [(ID EQUALS exp) (exp-assign $1 $3)]
                 )
                (exp
                 [(NUM) $1]
                 [(STRING) $1]
                 [(ID) (exp-var $1)] 
                 [(exp PLUS exp) (exp-plus $1 $3)]
                 [(ID OP args CP) (exp-self-call $1 $3)]
                 [(ID DOT ID OP args CP) (exp-call $1 $3 $5)]
                 [(OP exp CP) $2]
                 [(IF0 exp THEN exp ELSE exp END) (exp-if0 $2 $4 $6)]
                 [(OA type CA exp) (exp-cast $2 $4)]
                 [(NEW ID OP args CP) (exp-new $2 $4)]
                 )
                (args
                 [(exp COMMA args) (cons $1 $3)]
                 [(exp) (cons $1 null)]
                 [() null])
                )))

(define (do-parse path)
  (define test-input (open-input-file path))
  (parse (λ () (lex test-input))))

(define/match (type->strongstring type)
  [(tany) "any"]
  [(tint) "!number"]
  [(tstr) "!string"]
  [((tclass name)) "name"]
  [((tsclass name)) (string-append "!" name) ]
  )

(define/match (exp->strongstring body)
  [((exp-assign target value)) (string-append "this." target " = " (exp->strongstring value) "")]
  [((exp-plus left right)) (string-append (exp->strongstring left) "+" (exp->strongstring right))]
  [((exp-var name)) (string-append "this." name)]
  [((exp-call target name args)) (string-append target "." name "(" (string-join (map exp->strongstring args) ",") ")")]
  [((exp-self-call name args)) (string-append "this." name "(" (string-join (map exp->strongstring args) ",") ")")]
  [((exp-if0 cond then else)) (string-append "if (" (exp->strongstring cond) " == 0) {" (exp->strongstring then) "} else {" (exp->strongstring else) "}")]
  [((exp-cast type value)) (string-append "<" (type->strongstring type) ">" (exp->strongstring value))]
  [((exp-new name args)) (string-append "new " name "(" (string-join (map exp->strongstring args) ",") ")")]
  [((? number? num)) (number->string num)] 
  )

(define (generate-strongscript-fields decls)
  (string-append "constructor("
                 (string-join (map (match-lambda [(field-decl name type) (string-append "public " name ":" (type->strongstring type))])
                                   decls)
                              ", ")
                 ") {}\n")
  )


(define/match (generate-strongscript-method decl)
  [((method-decl name args type body))
   (string-append name ":" (type->strongstring type) " { "
                  (if (> (length body) 1) (string-append (string-join (map exp->strongstring (take body (- (length body) 1))) ";\n") ";\n") "")
                  "return " (exp->strongstring (last body)) ";\n" " }")
   ]
  )

(define/match (generate-strongscript-class class)
  [((class-decl name implements body))
   (define-values (fields methods) (partition field-decl? body))
   (string-append
    "class "
    name
    (if (empty? implements) "" (string-append " implements " (string-join implements ", ")))
    " {\n"
    (generate-strongscript-fields fields)
    (string-join (map generate-strongscript-method methods) "\n")
    "\n}"
    )])
  
(define (generate-strongscript tree)
  (map generate-strongscript-class tree)
  )