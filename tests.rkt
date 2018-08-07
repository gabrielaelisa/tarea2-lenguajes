#lang play
(print-only-errors #t)
(require "main.rkt")
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+ 
(module+ test
  (test (run '{+ 1 1}) 2)
  
  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
  (test (run '{< 1 2}) #t)
  
  (test (run '{local {{define x 1}}
                x}) 1)
  
  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)
  
  ;; datatypes  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
        #f)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
        #f)      
  
  ;; match
  (test (run '{match 1 {case 1 => 2}}) 2)
  
  (test (run '{match 2
                {case 1 => 2}
                {case 2 => 3}})             
        3)
  
  (test (run '{match #t {case #t => 2}}) 2)
  
  (test (run '{match #f
                {case #t => 2}
                {case #f => 3}})             
        3)

  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}})
        #t)
  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t))

;tests for extended MiniScheme+ 
#;(module+ sanity-tests
    (test (run '{local {{datatype Nat 
                  {Zero} 
                  {Succ n}}
                {define pred {fun {n} 
                               {match n
                                 {case {Zero} => {Zero}}
                                 {case {Succ m} => m}}}}}
          {pred {Succ {Succ {Zero}}}}}) "{Succ {Zero}}")
  
(test (run
 `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1 1}")

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 10
                         {stream-zipWith
                          {fun {n m}
                               {+ n m}}
                          ones
                          ones}}}})  "{list 2 2 2 2 2 2 2 2 2 2}")
(test 
(run `{local ,stream-lib
               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                 {stream-take 10 {merge-sort fibs fibs}}}})   "{list 1 1 1 1 2 2 3 3 5 5}"))


;;;;;;;;;;;;;;;;;;;;;;;
; WARM-UP
;;;;;;;;;;;;;;;;;;;;;,;

;;; tests for pretty-printing
(module+ test
  ;; test del enunciado
 (test (pretty-printing (structV 'Nat 'Succ (list (structV 'Nat 'Zero empty))))
       "{Succ {Zero}}")
 (test (pretty-printing (structV 'Even 'Succ-Succ
                                 (list (structV 'Even 'Succ-Succ
                                                (list (structV 'Even 'Zero empty))))))
       "{Succ-Succ {Succ-Succ {Zero}}}" ))
;; test for run (WarmUp)
(module+ test
  (test(run '{local {{datatype Even 
                  {Zero} 
                  {Succ-Succ n}}
                {define four {Succ-Succ {Succ-Succ {Zero}}} 
                               }} four}) "{Succ-Succ {Succ-Succ {Zero}}}")
;;;;;;;;;;;;;;;;;;
; LISTAS
;;;;;;;;;;;;;;;;;;
  
;; tests for run (Listas parte 1 y 2)

 (test (run '{List? {Empty}}) #t)
 (test (run '{List? {Cons 1 {Cons 2 {Empty}}}}) #t)
 (test (run '{length {Empty}}) 0)
 (test (run '{length {Cons 1 {Cons 2 {Cons 3 {Empty}}}}}) 3)
 (test (run '{length {Cons 1 {Cons 2 {Empty}}}}) 2)
  
;; tests for run (Listas parte 3)
 (test(run '{match {list {+ 1 1} 4 6}
          {case {Cons h r} => h}
          {case _ => 0}}) 2)
 (test(run '{List? {list 1 2 3}}) #t)

 (test (run '{List? {list 1 {list 2 3}}}) #t)

 (test (run '{List? {list {list 1 2} 3}}) #t)

 (test(run '{match {list {list 1 1} 4 6}
          {case {Cons h r} => h}
          {case _ => 0}}) "{list 1 1}")

;; tests for run (Listas parte 4)
(test (run '{match {list 2 {list 4 5} 6}
          {case {list a {list b c} d} => c}}) 5)
  
(test (run '{match {Cons 1 {Cons 2 {Empty}}}
              {case {list a b} => #t}}) #t)
  
(test (run '{match {Cons {Cons 1 {Empty}} {Cons {Cons 2 {Empty}} {Empty}}}
              {case {list {list a} {list b}} => #t}
              {case {list a b} => #f}}) #t
                                        )
;; test for run (Listas parte 5)
 (test (run '{list 1 4 6}) "{list 1 4 6}" )
 (test (run '{list {list 1 3} 4 6}) "{list {list 1 3} 4 6}" )
  
;; tests for pretty printing(Listas parte 5)

 (test (pretty-printing (structV 'List 'Cons
                                 (list 1 (structV 'List 'Cons
                                                (list 2 (structV 'List 'Empty empty))))))
       "{list 1 2}" )
(test (run '{list 1 2 3}) "{list 1 2 3}")
  
;;;;;;;;;;;;;;;;;;;;
;EVALUACIÓN PEREZOSA
;;;;;;;;;;;;;;;;;;;;

;;; call-by-need tests 
(test/exn  (run '{{fun {x  y} x} 1 {/ 1 asd}}) "env-lookup: no binding for identifier: asd")
  
(test (run '{{fun {x  {lazy y}} x} 1 {/ 1 0}}) 1)

(test (run '{{fun {x  {lazy y} {lazy z}} x} 1 {/ 1 0} {+ 1 y}}) 1)
  
(test (run '{local {{define {lazy x} {/ 1 0}}{define y {+ 1 2}}} y}) 3)
  
(test (run '{with {{f {fun {{lazy x}  y} y}}} {f {/ 1 0} 3 }}) 3)
  
(test(run '{local {{datatype T 
                  {C {lazy a}}}
                {define x {C {/ 1 0}}}}
          {T? x}}) #t)

;;; stream testings
  
;;;; parte 1
  
(test (run `{local {,stream-data ,make-stream ,stream-hd ,ones}
{stream-hd ones}}) 1)
  

(test (run `{local {,stream-data ,make-stream
                             ,stream-hd ,stream-tl ,ones}
          {stream-hd {stream-tl ones}}}) 1)

;;;; parte 2
 (test (run `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 10 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1}")
  
 (test (run `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 5 ones}}}) "{list 1 1 1 1 1}")

  
;;; parte 3
(test  (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 10
                         {stream-zipWith
                          {fun {n m}
                               {+ n m}}
                          ones
                          ones}}}}) "{list 2 2 2 2 2 2 2 2 2 2}")
  
(test  (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 5
                         {stream-zipWith
                          {fun {n m}
                               {- n m}}
                          ones
                          ones}}}}) "{list 0 0 0 0 0}")
;;; parte 4

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 5 {stream-zipWith
                          {fun {n m}
                               {+ n m}} fibs fibs}}}}) "{list 2 2 4 6 10}")

 (test (run `{local ,stream-lib {local {,ones ,stream-zipWith ,fibs}
            {stream-take 5 {stream-zipWith  {fun {n m}
                               {+ n m}} fibs ones}}}}) "{list 2 2 3 4 6}")
;;; parte 5

(test (run `{local ,stream-lib
               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                 {stream-take 10 {merge-sort fibs fibs}}}}) "{list 1 1 1 1 2 2 3 3 5 5}")
  )


