1:
	@node tsc/tsc.js 1-ss-ex.ts
	@node 1-ss-ex.js
	@rm 1-ss-ex.js
2:
	@racket 2-wrapper-typed.rkt || true
3:
	@racket 3* || true
4:
	@python3 retpy/retic.py 4-transient-ex.py || true
4m:
	@python3 retpy/retic.py --monotonic 4-transient-ex.py || true
5:
	@python3 retpy/retic.py --monotonic 5-mono.py || true
6ss:
	@node tsc/tsc.js 6-transient-vs-strongscript.ts
	@node 6-transient-vs-strongscript.js
	@rm 6-transient-vs-strongscript.js
6t:
	@python3 retpy/retic.py 6-transient-vs-strongscript.py
