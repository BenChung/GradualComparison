1:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 1.ts
	@cat classes.js 1.js > run.js
	- @node run.js
	- @make clean

2:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 2.ts
	@cat classes.js 2.js > run.js
	@node run.js
	- @make clean

3:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 3.ts
	@cat classes.js 3.js > run.js
	@node run.js
	- @make clean

4:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 4.ts
	@cat classes.js 4.js > run.js
	@node run.js
	- @make clean

5:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 5.ts
	@cat classes.js 5.js > run.js
	@node run.js
	- @make clean

6:
	@cp tsc/*runtime.js .
	@node tsc/tsc.js classes.ts 6.ts
	@cat classes.js 6.js > run.js
	@node run.js
	- @make clean

clean:
	@rm *~ *.js
