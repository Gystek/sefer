(load "iterators.scm")

					; sefer-pipeline - create a ready-for-use sefer pipeline taking input from `sefer-input-iterator` (by default `input-lines-iterator`)
					;
					; [forall a b. (Iterator a -> Iterator b)] -> InputIterator -> Iterator b
					;
					; The argument is a series of partial-application functions (usually iterator adapters) that will be applied to the preceding pipeline.
					; Each element is of the form `(function . (arg1 arg2 ... argN))`.
(define (sefer-pipeline adapters)
  (if (null? adapters)
      (lambda (x) x)
      (lambda (input)
	; quick and dirty fix
	(sefer-pipeline-generate adapters (iter-map (lambda (x) x) input)))))

(define (sefer-pipeline-generate adapters it)
  (if (null? adapters)
      it
      (apply-cons (lambda (f args)
		    (sefer-pipeline-generate (cdr adapters) (apply f (append args (list it)))))
		  (car adapters))))

					; input-chars-iterator - an iterator over `stdin`'s characters, the idiomatic way to read input in sefer
(define input-chars-iterator
  (let ((next (lambda (port)
		(if (null? port)
		    empty-iterator
		(let ((c (read-char port)))
		  (if (eof-object? c)
		      (begin
			(close-input-port port)
			empty-iterator)
		      (cons c port)))))))
    (iterator (open-input-file "/dev/stdin") next)))

					; input-lines-iterator - construct an iterator over lines from an iterator over chars
					;
					; Iterator Char -> Iterator String
(define (input-lines-iterator chars)
  (iter-separate '(#\newline) chars))

					; iter-separate - construct an iterator, splitting the input chars over the given separators
					;
					; [Char] -> Iterator Char [-> Boolean] -> Iterator String
					;
					; The `immutable` argument serves to indicate whether the given iterator is immutable.
(define (iter-separate seps chars . immutable)
  (let ((next (lambda (state)
		(let* ((nsep? (lambda (c) (not (memv c seps))))
		       (line (iterator->list (iter-take-while nsep? state))))
		  (if (null? line)
		      empty-iterator
		      (cons (list->string line)
			    (if (not (null? immutable))
					; if immutable, we have to skip the already-recorded line
				(cdr (iter-next (iter-skip-while nsep? state)))
					; else, we are already at the end of the line
				state)))))))
    (iterator chars next)))

					; sefer-input-iterator - the iterator given as input to the sefer pipeline
(define sefer-input-iterator input-lines-iterator)

					; sefer-run - run a sefer pipeline and collect its output
					;
					; Iterator a -> Either b (Iterator b)
(define (sefer-run f)
  (display
   (let* ((in (sefer-input-iterator input-chars-iterator))
	  (r (f in)))
     (cond
      ((iterator? r) (iterator->list r))
      ((and (not (list? r)) (pair? r)) (car r)) ; for use with functions returing (a, Iterator a)
      (else r))))
  (newline)
  (%exit))
