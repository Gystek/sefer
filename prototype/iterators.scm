(define-record-type :iterator
  (iterator under next)
  iterator?
  (under iterator-under)
  (next iterator-next))

(define (apply-cons f xxs)
  (f (car xxs) (cdr xxs)))

(define empty-iterator '(() . ()))

; x->iterator

					; list->iterator - transform a list into an iterator
					;
					; [a] -> Iterator a
(define (list->iterator x)
  (let ((next (lambda (state)
		(if (null? state)
		    empty-iterator
		    (cons (car state)
			  (cdr state))))))
    (iterator x next)))

					; Adapters

					; iter-next - return the iterator's next element along with the updated iterator
					;
					; Iterator a -> (Maybe a, Iterator a)
(define (iter-next it)
  (if (null? it)
      empty-iterator
      (apply-cons (lambda (x xs)
		    (cons x (iterator xs (iterator-next it))))
		  ((iterator-next it) (iterator-under it)))))


					; iter-enumerate - create an iterator which gives the current iteration count as well as the next value
					; Iterator a -> Iterator (Int, a)
(define (iter-enumerate it)
  (let ((next (lambda (state)
		(let ((i (car state)))
		  (apply-cons (lambda (x it)
			   (if (null? x)
			       empty-iterator
			       (cons (cons i x)
				     (cons (+ i 1) it))))
			 (iter-next (cdr state)))))))
    (iterator (cons 0 it) next)))

					; iter-map - create an iterator calling a function on each element
					;
					; (a -> b) -> Iterator a -> Iterator b
(define (iter-map f it)
  (let ((next (lambda (state)
		(apply-cons (lambda (x it)
			 (if (null? x)
			     empty-iterator
			     (cons (f x) it)))
		       (iter-next state)))))
    (iterator it next)))

					; iter-chain - take two iterators and create a new iterator over both in sequence
					;
					; Iterator a -> Iterator a -> Iterator a
(define (iter-chain a b)
  (let ((next (lambda (state)
		(apply-cons (lambda (a b)
			      (apply-cons (lambda (xa ita)
					    (if (null? xa)
						(apply-cons (lambda (xb itb)
							      (if (null? xb)
								  empty-iterator
								  (cons xb (cons '() itb))))
							    (iter-next b))
						(cons xa (cons ita b))))
					  (iter-next a)))
			    state))))
    (iterator (cons a b) next)))

					; iter-cycle - repeat an iterator endlessly
					;
					; Iterator a -> Iterator a

(define (iter-cycle it)
  (let ((next (lambda (state)
		(apply-cons (lambda (it0 it)
			      (apply-cons (lambda (x it)
					    (if (null? x)
						(apply-cons (lambda (x it1)
							      (if (null? x)
								  empty-iterator
								  (cons x (cons it0 it1))))
							    (iter-next it0))
						(cons x (cons it0 it))))
					  (iter-next it)))
			    state))))
    (iterator (cons it it) next)))

					; iter-skip - create an iterator, skipping the first n elements
					;
					; Int -> Iterator a -> Iterator a
(define (iter-skip n it)
  (let ((next (lambda (state)
		(apply-cons (lambda (n it)
			      (apply-cons (lambda (x it)
					    (cons x (cons 0 it)))
					  (if (> n 0)
					      (iter-nth n it)
					      (iter-next it))))
			    state))))
    (iterator (cons n it) next)))

					; iter-skip-while - create an iterator, skipping the first elements matching a predicate
					;
					; (a -> Boolean) -> Iterator a -> Iterator a
(define (iter-skip-while p? it)
  (let* ((np? (lambda (a) (not (p? a))))
	 (next (lambda (state)
		 (apply-cons (lambda (found it)
			       (if found
				   (apply-cons (lambda (x it)
						 (cons x (cons #t it)))
					       (iter-next it))
				   (apply-cons (lambda (x it)
						 (cons x (cons #t it)))
					       (iter-find np? it))))
			     state))))
    (iterator (cons #f it) next)))

					; iter-filter - create an iterator, filtering out elements not matching a predicate
					;
					; (a -> Boolean) -> Iterator a -> Iterator a
(define (iter-filter p? it)
  (let ((next (lambda (state)
	       (iter-find p? state))))
    (iterator it next)))
		


; Extractors

					; iter-any? - test if any element of the iterator matches a predicate
					;
					; (a -> Boolean) -> Iterator a -> Boolean
(define (iter-any? p? it)
  (not (equal? (iter-find p? it) empty-iterator)))

					; iter-all? - test if every element of the iterator matches a predicate
					;
					; (a -> Boolean) -> Iterator a -> Boolean
(define (iter-all? p? it)
  (let ((np? (lambda (a) (not (p? a)))))
    (not (iter-any? np? it))))

					; iter-count - count the number of elements yielded by the iterator
					;
					; Iterator a -> Int
(define (iter-count it)
  (define (iter it n)
    (apply-cons (lambda (x it)
		  (if (null? x)
		      n
		      (iter it (+ n 1))))
		(iter-next it)))
  (iter it 0))

					; iter-fold - fold every element into an accumulator, applying a function
					;
					; b -> (b -> a -> b) -> Iterator a -> b
(define (iter-fold b0 f it)
  (apply-cons (lambda (x it)
		(if (null? x)
		    b0
		    (iter-fold (f b0 x) f it)))
	      (iter-next it)))

					; iter-reduce - reduce the elements to a single value, repeatedly applying a function
					;
					; (a -> a -> a) -> Iterator a -> Maybe a
(define (iter-reduce f it)
  (apply-cons (lambda (x it)
		(if (null? x)
		    '()
		    (iter-fold x f it)))
	      (iter-next it)))

					; iter-find - search for an element that satisfies a predicate inside the iterator, consuming all previous elements
					;
					; (a -> Boolean) -> Iterator a -> (Maybe a, Iterator a)
(define (iter-find p? it)
  (apply-cons (lambda (x it)
		(cond
		 ((null? x) empty-iterator)
		 ((p? x) (cons x it))
		 (else (iter-find p? it))))
	      (iter-next it)))

					; iter-sum - sum the elements inside the iterator
					;
					; Iterator Int -> Int
(define (iter-sum it)
  (iter-reduce + it))

					; iter-product - calculate the product of the elements inside the iterator
					;
					; Iterator Int -> Int
(define (iter-product it)
  (iter-reduce * it))

					; iter-nth - fetch the n-th element of the iterator, consuming all previous elements
					;
					; Int -> Iterator a -> (Maybe a, Iterator a)
(define (iter-nth n it)
  (if (= n 0)
      (iter-next it)
      (iter-nth (- n 1) (cdr (iter-next it)))))


; iterator->x

					; iterator->list - collect an iterator into a list
					;
					; Iterator a -> [a]
(define (iterator->list it)
  (define (iter it ls)
    (apply-cons (lambda (x it)
		  (if (null? x)
		      ls
		      (iter it (cons x ls))))
		(iter-next it)))
  (reverse (iter it '())))
