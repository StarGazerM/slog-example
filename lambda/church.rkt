#lang racket

;; Assignment 4: A church-compiler for Scheme, to Lambda-calculus

(provide church-compile
         ; provided conversions:
         church->nat
         church->bool
         church->listof)
;; Input language:
;
; e ::= (letrec ([x (lambda (x ...) e)]) e)    
;     | (let ([x e] ...) e)  
;     | (let* ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (e e ...)    
;     | x  
;     | (and e ...) | (or e ...)
;     | (if e e e)
;     | (prim e) | (prim e e)
;     | datum
; datum ::= nat | (quote ()) | #t | #f 
; nat ::= 0 | 1 | 2 | ... 
; x is a symbol
; prim is a primitive operation in list prims
; The following are *extra credit*: -, =, sub1

;; Definition of core scheme
(define (expr? e)
  (match e
    [(? symbol? var) #t]
    [(? lit?) #t]
    [`(λ (,xs ...) ,body) #t]
    [`(if ,(? expr? guard)
          ,(? expr? etrue)
          ,(? expr? efalse)) #t]
    [`(let* ([,(? symbol? xs) ,(? expr? x-bodies)] ...)
        ,(? expr? body)) #t]
    [`(letrec ([,(? symbol?) (λ (,xs ...) ,(? expr?))] ...)
        ,(? expr? body)) #t]
    [`(,(? builtin?) ,(? expr? args) ...) #t]
    [`(,(? expr? e0) ,(? expr? e1) ...) #t]))

(define (lit? e)
  (match e
    [(? number?) #t]
    [(? string?) #t]
    [(? boolean?) #t]
    [else #f]))

(define (builtin? x)
  (set-member? (set '+ '- '* '/ 'cons 'car 'cdr 'list 'list? '= 'empty? 'number? 'string? 'string-append 'string-length 'length) x))

; Mapping from symbols to the primitive built-in functions within
; Racket.
(define builtins 
  (make-hash (list (cons '+ +)
                   (cons '- -)
                   (cons '* *)
                   (cons '/ /)
                   (cons 'cons cons)
                   (cons 'car car)
                   (cons 'cdr cdr)
                   (cons 'list list)
                   (cons '= equal?)
                   (cons 'empty? empty)
                   (cons 'number? number?)
                   (cons 'string? string?)
                   (cons 'string-append string-append)
                   (cons 'string-length string-length)
                   (cons 'length length)
                   (cons 'or (λ (a b) (or a b)))
                   (cons 'zero? zero?)
                   (cons 'list? list?))))
;; input predicate

; This input language has semantics identical to Scheme / Racket, except:
;   + You will not be provided code that yields any kind of error in Racket
;   + You do not need to treat non-boolean values as #t at if, and, or forms
;   + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr), 
;                                           or binary (+ - * = cons)
;   + There will be no variadic functions or applications---but any fixed arity is allowed

;; Output language:

; e ::= (lambda (x) e)
;     | (e e)
;     | x
;
; also as interpreted by Racket

;; Using the following decoding functions:

; A church-encoded nat is a function taking an f, and x, returning (f^n x)
(define (church->nat c-nat)
  ((c-nat add1) 0))

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
(define (church->bool c-bool)
  ((c-bool (lambda (_) #t)) (lambda (_) #f)))

; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning when-cons applied on the car and cdr elements
; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning the when-null thunk, applied on a dummy value (arbitrary value that will be thrown away)
(define ((church->listof T) c-lst)
  ; when it's a pair, convert the element with T, and the tail with (church->listof T)
  ((c-lst (lambda (a) (lambda (b) (cons (T a) ((church->listof T) b)))))
   ; when it's null, return Racket's null
   (lambda (_) '())))


;; Write your church-compiling code below:

;; Nat
(define church:zro
  '(λ (f) (λ (x) x)))

(define (church:scc n)
  (match n
    [`(λ (f) (λ (x) ,f-n)) ; =>
     `(λ (f) (λ (x) (f ,f-n)))]))

;; boolean
(define church:tru
  '(λ (t) (λ (f) (t (λ (x) x)))))

(define church:fls
  '(λ (t) (λ (f) (f (λ (x) x)))))

(define church:zero? `(λ (n0) ((n0 (λ (b) ,church:fls)) ,church:tru)))

;; arithmetic
(define church:+
  `(λ (n) (λ (m)
             (λ (f) (λ (x)
                       ((n f) ((m f) x)))))))

(define church:prd
  `(λ (n)
     (λ (f)
       (λ (x)
         (((n (λ (g)
                (λ (h)
                  (h (g f)))))
           (λ (u) x))
          (λ (u) u))))))

(define church:-
  `(λ (m) (λ (n)
             ((n ,church:prd) m))))

(define church:*
  '(λ (m) (λ (n)
             (λ (f) (λ (x)
                       ((m (n f)) x))))))

(define church:= `(λ (n0)
                    (λ (n1)
                      (and (,church:zero? (,church:- n0 n1)) (,church:zero? (,church:- n1 n0))))))


;; list
(define church:null
  `(λ (wcons) (λ (wnull) (wnull (λ (x) x)))))

(define church:cons
  `(λ (a) (λ (b) (λ (wcons) (λ (wnull) ((wcons a) b))))))

(define church:car
  `(λ (l) ((l (λ (a) (λ (b) a))) (λ (x) x))))

(define church:cdr
  `(λ (l) ((l (λ (a) (λ (b) b))) (λ (x) x))))

;; Y combinator
(define y-comb
  '(λ (b) ((λ (f) (b (λ (x) ((f f) x))))
            (λ (f) (b (λ (x) ((f f) x)))))))

;; churh encode nat
(define (churchify-nat num)
  (match num
    [0 church:zro]
    [n (church:scc (churchify-nat (- n 1)))]))

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)
(define (churchify expr)
  ;; (displayln expr)
  (match expr
    ;; desuger all muti arguments lambda and no args lambda to
    ;; single arg lambda which can fit λ-calulas def well
    ;; anonymous lambda, we just put a dummy arg _ there, since
    ;; church require all function be curify
    [`(λ () ,e)
     `(churchify e)]
    [`(λ (,arg) ,e)
     `(λ (,arg) ,(churchify e))]
    [`(λ (,arg . ,res) ,e) ;=>
     `(λ (,arg) ,(churchify `(λ (,res) ,e)))]
    ;; variable
    [(? symbol? var) ;=>
     var]
    ;; let binding is a lambda
    [`(let* ([,(? symbol? name) ,(? expr? bind-body)])
        ,(? expr? body))
     `((λ (,name) ,(churchify body)) ,(churchify bind-body))]
    [`(let* ([,(? symbol? name) ,(? expr? bind-body)] . ,res)
        ,(? expr? body))
     `((λ (,name) ,(churchify `(let* (,res) ,body))) ,(churchify bind-body))]
    [`(letrec ([,(? symbol? name) ,(? expr? bind-body)])
         ,(? expr? body))
     (churchify `(let* ([,name (((λ (x) (x x)) (λ (y) (λ (f) (f (λ (x) (((y y) f) x))))))
                                (λ (,name) ,bind-body))])
                    ,body))]
    ;; condition
    [`(if ,e0 ,e1 ,e2) ;=>
     `((,(churchify e0) (λ (_) ,(churchify e1))) (λ (_) ,(churchify e2)))]
    ;; just desugar or/and to if
    [`(and ,e0 ,e1) ;=>
     (churchify `(if ,e0 (if ,e1 #t #f) #f))]
    [`(or ,e0 ,e1) ;=>
     (churchify `(if ,e0 #t ,e1))]
    ;; datum
    [(? number? nat) ;=>
     (churchify-nat nat)]
    [`(zero? ,n0)  `(,church:zero? ,(churchify n0))]
    ;; the arith
    [`(+ ,n0 ,n2) ;=>
     `((,church:+ ,(churchify n0)) ,(churchify n2))]
    [`(sub1 ,n0)
     `(,church:prd ,(churchify n0))]
    [`(- ,n0 ,n2) ;=>
     `((,church:- ,(churchify n0)) ,(churchify n2))]
    [`(= ,n0 ,n2)
     `((,(churchify church:=) ,(churchify n0)) ,(churchify n2))]
    [`(add1 ,n)
     `((λ (n) (λ (f) (λ (x) (n (f x))))) ,(churchify n))]
    ['#t
     church:tru]
    ['#f
     church:fls]
    ;; list
    ['(quote ())
     church:null]
    [`(cons ,a ,b) `((,church:cons ,(churchify a)) ,(churchify b))]
    [`(car ,l) `(,church:car ,(churchify l))]
    [`(cdr ,l) `(,church:cdr ,(churchify l))]
    ;; untagged operations
    ;; procedure in scheme, can just use a id function to close it
    [`(,f) ;=>
     `(,(churchify f) (λ (x) x))]
    [`(,f ,arg) ;=>
     `(,(churchify f) ,(churchify arg))]
    [`(,f ,arg . ,res) ;=>
     (churchify `(,(churchify `(,f ,arg)) ,@res))]
    ))



; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (define todo `(lambda (x) x))
  (churchify program)
  #;(churchify
   `(let ([add1 ,todo]
          [+ ,church:+]
          [* ,church:*]
          [zero? ,church:zero?])
      ,program)))
