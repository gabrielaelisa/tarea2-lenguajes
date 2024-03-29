#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}

<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | (<constr-id> <attr-id>*)

<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}


<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>

|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes
(deftype Variant
  (variant name params))

; estructuras de datos
(deftype Struct
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal 
  (constrP ctr patterns)) ; constructor y sub-patrones

;; parse :: s-expr -> Expr
;; parses from concrete syntax to abstract
(define(parse s-expr)

 (define (parse-list args)
  (match args
    ['() (app (id 'Empty) '())]
    [(list head tail ...) (app (id 'Cons) (list (parse head) (parse-list tail)))]
    ))
  
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]    
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    ;list como azúcar sintáctico de Cons
    [(list 'list args ...)(parse-list args) ]
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]))

; parse-def :: s-expr -> Def
(define(parse-def s-expr)  
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))


; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern
(define(parse-pattern p)
 
  (match p
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]
    [(list 'list arg ...) (begin
                            (define (parse-pattern-list l)
                              (match l
                                [(list) (constrP 'Empty '())]
                                [(list head tail ...) (constrP 'Cons (list (parse-pattern head)
                                                                           (parse-pattern-list tail))) ]
                                ))(parse-pattern-list arg ))]
    [(list ctr patterns ...) (constrP (first p) (map parse-pattern patterns))]))

;; interp :: Expr Env -> number/boolean/procedure/Struct
(define(interp expr env)
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; identifier
    [(id x) (env-lookup x env)]
    
    [(fun ids body)
     
    (closureV ids (λ (arg-vals id)
       (interp body (extend-env id arg-vals env))) env)]
    ; application
    [(app fun-expr arg-expr-list)
     ; problema guardar en la funcion el closure del ambiente
     (match (strict(interp fun-expr env))
       [(closureV ids body cl-env)(body
           (map (λ (id a)
             (match id
               [(list 'lazy x) (exprV a env (box #f))]
               [ _ (strict(interp a env))])) ids arg-expr-list)
           (map (λ (id)
                  (match id [(list 'lazy x) x]
                            [_ id])) ids))]
       [_
       (match fun-expr
         [(id i) ((interp fun-expr env)
                  (match (env-lookup i env)
                   [(list 'lazy x) (exprV arg-expr-list env (box #f))]
                   [ _ (map (lambda(x) (interp x env)) arg-expr-list) ]))])])]
    
    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a) (interp a env)) arg-expr-list))]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))            
     (for-each (λ (d) (interp-def d new-env)) defs) 
     (interp body new-env)]
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     ;(def (list head tail ...) ()
     (interp body (extend-env (map car alist) (map cdr alist) env))]))

; interp-def :: Def Env -> Void
(define(interp-def d env)
  (match d
    [(dfine id val-expr)
     ;;; agregado
     (match id
       ;;; no se si es necesario
       [(list 'lazy x) (update-env! x (exprV val-expr env (box #f)) env)]
       [_ (update-env! id (interp val-expr env) env)])]
    [(datatype name variants)
     ;; extend environment with new definitions corresponding to the datatype
     (interp-datatype name env)
     (for-each (λ (v) (interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define(interp-datatype name env)

  ; datatype predicate, eg. Nat?
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               (λ (v) (symbol=? (structV-name (first v)) name))
               env))

; interp-variant :: String String Env -> Void
(define(interp-variant name var env)

  ;; name of the variant or dataconstructor
  (def varname (variant-name var))
  (def params (variant-params var))

  ;; variant data constructor, eg. Zero, Succ

  (update-env! varname (closureV params (λ (args id) (structV name varname args)) env) env)
  ;; variant predicate, eg. Zero?, Succ?
  (update-env! (string->symbol (string-append (symbol->string varname) "?"))
               (λ (v) (symbol=? (structV-variant (first v)) varname))
               env))

;;;;
; pattern matcher
(define(find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (match (match-pattern-with-value pattern value)
       [#f (find-first-matching-case value cs)]
       [alist (cons alist body)])]))

(define(match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) #f)]
                [((litP (num v)) n)
                 (if (equal? v n) (list) #f)]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     #f)]
                [(x y) (error "Match failure")]))

;; run :: s-expr ->number/bool/string
;; runs program in minischeme+ language
(define(run prog)
  (define prog_aux (list 'local '{{datatype List 
                  {Empty} 
                  {Cons a b}}{define length {fun {l}
                            {match l
                              {case {Empty} => 0}
                              {case {Cons a b} =>  {+ 1 {length b}}}
                              }}}
                           } prog))
    
  (define exp (interp (parse prog_aux) empty-env))
  (match exp
   [(structV name variant val)(pretty-printing exp)]
    [_ exp]) )


#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define(env-lookup id env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overring the binding for id.
(define(update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))             
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;Tarea2
;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;
;LISTAS
;;;;;;;;;;;;;;;;;;;;;;

;define tipo de dato lista
(def List '{datatype List 
                  {Empty} 
                  {Cons a b}})
;entrega el largo de una lista
;length List-> number
(def length '{define length {fun {l}
                            {match l
                              {case {Empty} => 0}
                              {case {Cons a b} =>  {+ 1 {length b}}}
                              }}})

;;pretty-printing: struct -> string
;;imprime una estructura en formato string amigable
(define (pretty-printing expr)
  (define (print-list arg)
    (match arg
      [(list) "}"]
      [(list val (structV 'List var val2)) (string-append (pretty-printing-aux val) (print-list val2))]
    ))
  (define (pretty-printing-aux expr) (match expr
    [(? number? n) (string-append " " (number->string n))]
    [#f " #f"]
    [#t " #t"]
    ['() ""]
    [(list first tail ...) (string-append(pretty-printing-aux first) (pretty-printing-aux tail))]  
    [(structV 'List var val) (string-append " {list"(print-list val) )]
    [(structV name var val) (string-append " {" (symbol->string var) (pretty-printing-aux val)"}") ]
    [_ ""]
    ))
 (substring (pretty-printing-aux expr) 1)
  )
;;;;;;;;;;;;;;;;;;;;;;;;;;
; Implementacion de lazyness
;;;;;;;;;;;;;;;;;;;;;;;;;;;


; tipo de dato Val visto en clases
(deftype Val
  (numV n)
  (closureV fun body env)
  (exprV expr env cache))

; funcio strict vista en clases 04/26
; strict :: Val -> Val (only numV or closureV)
(define (strict v)
  (match v
    [(exprV expr env cache)
     (if (unbox cache)
         ;(begin
          ; (printf "using cached value for ~v ~n" expr)
           (unbox cache)
           ;)
         (begin
           ;(printf "forcing ~v ~n" expr)
           (let ([val (strict (interp expr env))])
             (set-box! cache val)
             val))
         )]
    [ _ v]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Sreams definiciones
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;define el tipo de dato Stream

(def stream-data '{datatype Stream {stream head {lazy tail}}})

;crea un Stream,
;make-stream x y -> Stream x y
(def make-stream '{define make-stream  {fun {x  {lazy y}} {stream x y}}})

;stream de unos
; ones: void-> Stream
(def ones '{define ones {make-stream 1 ones}})

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trabajando con Streams
;;;;;;;;;;;;;;;;;;;;;;;;;;

;entrega la cabeza
;stream-hd: Stream -> num/bool/struct
(def stream-hd '{define stream-hd {fun {s} {match s
                                             {case {stream head tail} => head}
                                             {case _ => s}}}})
;entrega la cola
; stream-tl: Stream-> Stream
(def stream-tl '{define stream-tl {fun {s} {match s
                                             {case {stream head tail} => tail}
                                             {case _ => s}}}})
; entrega los primeros n valores del stream
;stream-take: number Stream -> list
(def stream-take '{define stream-take {fun {n s}
                                           {match {zero? n}
                                             {case #t => {Empty}}
                                             {case #f => {Cons {stream-hd s} {stream-take {- n 1} {stream-tl s}}}}
                                               }}})

; evaluación de una fucion en dos streams 
; stream-zipWith : Stream1 Stream2 -> Stream
(def stream-zipWith '{define stream-zipWith {fun {f s1 s2}
                                                 {stream {f {stream-hd s1} {stream-hd s2}}
                                                       {stream-zipWith f {stream-tl s1} {stream-tl s2}}}}})

;stream de fibonacci

;auxiliary function for fibonaccio stream; recibe 2 enteros y etrega la secuencia de fibonacci
;de estos enteros
;stream-aux: number number -> Stream
(def stream-aux '{define stream-aux {fun {f0 f1} {stream f1 {stream-aux f1 {+ f0 f1}}}}})

;fibs: retorna Stream de fibonacci
(def fibs '{define fibs {stream-aux 0 1}})

;merge sort de dos streams ordenados
;merge-sort : Stream1 Stream2 -> Stream
(def merge-sort '{define merge-sort {fun {s1 s2} {if { > {stream-hd s1} {stream-hd s2}}
                                                     {stream {stream-hd s2} {merge-sort  s1 {stream-tl s2}}}
                                                     {stream {stream-hd s1} {merge-sort {stream-tl s1} s2}}}}})


;definicion de stream-lib data
(def stream-lib (list stream-data
                      stream-aux
                      make-stream
                      stream-hd
                      stream-tl
                      stream-take
                      ))
