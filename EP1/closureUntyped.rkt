#lang plai

#|
 | Funções não têm mais nome, serão chamadas de lamC (em homenagem ao λ)
 |#

; Expressões básicas
(define-type ExprC
  [numC  (n  number?)]
  [idC   (s  symbol?)]
  [plusC (l  ExprC?) (r  ExprC?)]
  [multC (l  ExprC?) (r  ExprC?)]
  [lamC  (arg  symbol?) (body  ExprC?)] ; nomes não são mais necessários
  [appC  (fun  ExprC?) (arg  ExprC?)]
  [ifC   (condição  ExprC?) (sim  ExprC?) (não  ExprC?)]
  [quoteC (s symbol?)]
  [loadC (s quoteC?)]
  [letrecC (arg symbol?) (arg2 ExprC?) (body ExprC?)]
  )


; Expressões açucaradas
(define-type ExprS
  [numS    (n  number?)]
  [idS     (s  symbol?)] 
  [lamS    (arg  symbol?) (body  ExprS?)] ; muda de acordo
  [appS    (fun  ExprS?) (arg  ExprS?)] 
  [plusS   (l  ExprS?) (r  ExprS?)]
  [bminusS (l  ExprS?) (r  ExprS?)]
  [uminusS (e  ExprS?)]
  [multS   (l  ExprS?) (r  ExprS?)]
  [ifS     (c  ExprS?) (s  ExprS?) (n  ExprS?)]
  [quoteS (s symbol?)]
  [loadS (s quoteS?)]
  [letS (arg list?) (body ExprS?)]
  [let*S (arg list?) (body ExprS?)]
  [letrecS (arg symbol?) (arg2 ExprS?) (body ExprS?)]
  )


; Retirando o açúcar
(define (desugar as); ExprS => ExprC  
  (type-case ExprS as
    [numS    (n) (numC n)]
    [idS     (s) (idC s)]
    [lamS    (a b)  (lamC a (desugar b))]
    [appS    (fun arg) (appC (desugar fun) (desugar arg))] 
    [plusS   (l r) (plusC (desugar l) (desugar r))] 
    [multS   (l r) (multC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)   (multC (numC -1) (desugar e))]
    [ifS     (c s n) (ifC (desugar c) (desugar s) (desugar n))]
    [quoteS (s) (quoteC s)]
    [loadS (s) (loadC (desugar s))]
    [letS (a b) (desugar (appS (lamS (first a) b) (second a)))]
    [let*S (a b) (desugar(letS (first a) (letS (second a) b)))]
    [letrecS (a b c) (letrecC a (desugar b) (desugar c))]
    )) 
 

#|
 | Closures não têm mais nome, mas precisam de Environment
 |#

; Símbolos devem se associar a um Value
(define-type Binding
      [bind (name  symbol?) (val  Value?)])

; A lista de associações é o Environment
; (define-type-alias Env (listof Binding))
(define mt-env empty)    ; Tente pronunciar "mt" em inglês e compare com "empty"
(define extend-env cons) ; Por sorte, cons faz exatamente o que queremos para estender o env
(define-type Value
  [numV  (n  number?)]
  [closV (arg  symbol?) (body  ExprC?) (env  list?)]
  [symV (s symbol?)])


; Novos operadores
(define (num+ l r); Value x Value => Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* l r); Value x Value => Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))

(define (symV->string s)
  (cond
    [(symV? s)
     (symbol->string (symV-s s))]
    [else
          (error 'symV->string "O argumento não é símbolo")]))

; Interpretador
(define (interp a env); ExprC x Env => Value
  (type-case ExprC a
    [numC (n) (numV n)] 
    [idC (n) (lookup n env)]
    [lamC (a b) (closV a b env)] ; definição de função captura o environment

    [appC (f a)
          (local ([define f-value (interp f env)]) ; f-value descreve melhor a ideia
            (interp (closV-body f-value)
                    (extend-env 
                        (bind (closV-arg f-value) (interp a env))
                        (closV-env f-value) ; não mais mt-env
                    )))]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [ifC (c s n) (if (zero? (numV-n (interp c env))) (interp n env) (interp s env))]
    [quoteC (s) (symV s)]
    [loadC (s) (read-file (open-input-file (symV->string(interp s env))))]
    [letrecC (a b c) (local ((define a-value (closV a b env)))
                         (interp c (extend-env (bind a a-value) env)))]
    ))
;[closV (arg  symbol?) (body  ExprC?) (env  list?)]

    (define read-file
      (lambda(file)
        (let loop ([line (read file)])
          (if (not (eof-object? line))
            (begin
              (println (interpS line))
              (loop (read file)))
           (close-input-port file)))))

; Lookup para procurar símbolos no Environment
(define (lookup for env); [for : symbol] [env : Env]) => Value
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; achou!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; vê no resto


; Parser
(define (parse s); [s : s-expression] => ExprS
  (cond
    [(number? s) (numS s)]
    [(symbol? s) (idS  s)] ; Pode ser um símbolo livre nas definições de função
    [(list? s)
     (let ([sl s])
       (case  (first sl)
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(func) (lamS (second sl) (parse (third sl)))]
         [(lambda) (lamS (second sl) (parse (third sl)))]
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(quote) (quoteS (second sl))]
         [(load) (loadS (parse(second sl)))]
         [(let) (letS (list (first (first (second sl))) (parse (second (first (second sl))))) (parse (third sl)))]
         [(let*) (let*S (list (parseLet* (first (second sl))) (parseLet* (second (second sl)))) (parse (third sl)))]
         [(letrec) (letrecS (first (first (second sl))) (parse (second (first (second sl)))) (parse (third sl)))]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))

        (define parseLet*
          (lambda (l) (list (first l) (parse (second l)))))
         
          


; Facilitador
(define (interpS s) (interp (desugar (parse s)) mt-env))

; Testes
(test (interp (plusC (numC 10) (appC (lamC '_ (numC 5)) (numC 10)))
              mt-env)
      (numV 15))
(interpS '(+ 10 (call (func x (+ x x)) 16)))
(interpS '(quote alan))
(interpS '(load (quote teste2.rkt)))
(interpS '(let ((x (+ 1 1))) (* 2 x)))
(interpS '(let* ((x (+ 1 1)) (y (* 3 x))) (+ (* 2 x) y)))
(interpS '(let ((n 5)) (if n (* n (- n 1)) 1)))
(interpS '(call (lambda x (* x 1)) 5))
(interpS '(letrec ([fac (lambda n (if n (+ n (call fac (- n 1))) 1))]) (call fac 5)))