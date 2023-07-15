#lang racket

(require racket/symbol)

(require compatibility/defmacro)


;;this code outputs desugared (simplest form) lambda calculus term

;;call using desugar function

;;input lambda term is quoted list of lambda expression with syntactic sugar, dots have to escaped
;;example input for factorial 3: (desugar '((Y (λ f n \. ZERO n 1 (* n (f (-  n  1))))) 3))

;;output is input equivalent lambda term without syntactic sugar






;make cond expression from list of functions below, first value is the name of function, second value is its expanded state.
(define-macro (functions-macro symbols)
    (cons 'cond (append (map (lambda (val) `[(equal? (car symbols) ',(car val)) ,(cadr val)])

                             
    ;; list of known functions                         
    '(
    (+ '(λ x y s z \. x s (y s z)))
    (- '(λ m n \. (n PRED) m))
    (/ '(λ n \. Y (λ c n m f x \. (λ d \. ZERO d (0 f x) (f (c d m f x))) (- n m)) (SUC n)))
    (* '(λ x y s \. x (y s)))
    (Y '(λ f \. (λ x \. f (x x)) (λ x \. f (x x))))
    (ZERO '(λ n \. n (λ x \. (λ t f \. f)) (λ t f \. t)))
    (SUC '(λ n s z \. s (n s z)))
    (PRED '(λ x s z \. x (λ f g \. g (f s)) (λ g \. z) (λ u \. u)))
    (AND '(λ x y \. x y x))
    (OR '(λ x y \. x x y))
    (T '(λ t f \. t))
    (F '(λ t f \. f))
    (NOT '(λ x t f \. x f t))
    (HELLOWORLD '(λ x y z z sa a wwdwdw \. h e l l o T F 0 1))
    (HELLOWORLD2 '(0 HELLOWORLD 1))
    ))

                        
    `((else symbols))))); variable


;make lambda function with s and z variables and call desugar-number-impl that will fill the body
;x must be a number
(define (desugar-number x)
      (list 'λ 's '\. (append '(λ z \.) (car (desugar-number-impl x)))))


;recursively add s and parentheses to create Church numerals, special case for 0 and 1 because of extra parentheses
;x must be a number
(define (desugar-number-impl x)
  (cond
    [(= x 0) (cons (cons 'z null) null)]
    [(= x 1) (cons (list 's 'z) null)]
    [else (cons (cons 's (desugar-number-impl (- x 1))) null)]))


;skip lambda symbol and calls desugar-multiple-var on the rest to get rid of multiple variables, car is needed because it is in one extra list
;x must be lambda function
(define (desugar-lambda x)
  (car (desugar-multiple-var (cdr x))))


;create new one variable lambda function for each found variable, recursively called until dot is found
;x is lambda function without lambda symbol at the beginning, for example (x y \. x)
(define (desugar-multiple-var x)
  (if (null? x)
      (display "err")
      (if (equal? (car x) '\.)
          (desugar-impl (cdr x))
          (cons (cons 'λ (cons (car x) (cons '\. (desugar-multiple-var (cdr x))))) null))))


;if f is lambda function then return its body else error
;f is lambda function
(define (function-body f)
  (if (null? f)
      #f ;error
      (if (equal? (car f) '\.)
          (cdr f)
          (function-body (cdr f)))))


;starts desugaring of function body, if body is standalone symbol then wraps it in list and call desugar-fun-body-impl
;body is body of lambda function, it can be list of symbols or standalone symbol
(define (desugar-fun-body body)
    (if (pair? body)
        (desugar-fun-body-impl body)
        (desugar-fun-body-impl (cons body null))))


;if any of symbols is know function from list defined in the beginning of this file then it gets expanded
;symbols is body of lambda function as list of symbols
(define (desugar-fun-body-impl symbols)
  (let [(expanded (functions-macro symbols))] ;expanded function
  (if (equal? expanded symbols)
      (if (null? (cdr symbols))
          (car symbols)
          symbols)
      (desugar-fun-body-impl expanded))))


;decides what type of lambda term x is and calls function that can desugar this type
;x is lambda term that should be desugared
(define (desugar-impl x)
  (if (null? x)
      null
      (cond
        [(not (pair? x)) (if (number? x) (desugar-number x) (desugar-fun-body x))] ;not a pair => number or function
        [(pair? (car x)) (cons (desugar-list (car x)) (desugar-impl (cdr x)))] ;is a pair, first value is a pair => desugar list
        [(number? (car x)) (cons (desugar-number (car x)) (desugar-impl (cdr x)))] ;is a pair and first value is a number => desugar number
        [(equal? (car x) 'λ) (desugar-lambda x)] ;is a pair and first value is lambda => desugar lambda
        [else (map (lambda (a) (desugar-check a)) x)]))) ;is pair and not any of the previous => lambda function


;compares current with an attempt to desugar current. if they are the same, then this term is desugared
;current is lambda term
(define (desugar-check current)
  (let [(next (desugar-impl current))]
  (if (equal? current next)
      current
      (desugar-check next))))


;checks input and call desugar, shows result of desugaring using display
;x is lambda term that should be desugared
(define (desugar x)
  (if (check-input x)
      (display (desugar-check x))
      (display "Invalid input")))


;desugar list x
;x is list with lambda terms
(define (desugar-list x)
  (if (equal? (cdr x) null)
      (desugar-impl (car x))
      (desugar-impl x)))


;checks input, returns false if error
;x is input lambda term 
(define (check-input x)
  (cond
    [(null? x) #f] ; empty parentheses
    [(equal? x '\.) #f]; dot outside of lambda function or multiple dots in lambda function
    [(equal? x 'λ) #f]; ; standalone lambda symbol
    [(not (pair? x)) #t] ;variable
    [(equal? (car x) 'λ) (and (not (equal? null (cdr x))) (not (equal? (cadr x) '\.)) (check-function-vars (cdr x)) (check-function-body (function-body x)))];lambda term
    [(and (not (null? (car x))) (null? (cdr x))) (check-input (car x))] ;parentheses, final application
    [else (and (check-input (car x)) (check-input (cdr x)))])) ;application


;check lambda function body, returns #f if fail
;body is lambda function body from function-body function or #f if this function failed
(define (check-function-body body)
  (if (equal? body #f)
      #f
      (check-input body)))


;checks lambda variables for undesirable symbols, pair, number, any expandable function and if there is dot symbol
;x is lambda function without lambda symbol at beginning
(define (check-function-vars symbols)
  (if (or (not (pair? symbols)) (number? (car symbols)) (equal? (car symbols) 'λ) (pair? (car symbols)) (null? (car symbols)))
      #f
      (let ([expanded (functions-macro symbols)])
        (if (not (equal? symbols expanded))
            #f
            (if (equal? (car symbols) '\.)
                #t
                (check-function-vars (cdr symbols)))))))

