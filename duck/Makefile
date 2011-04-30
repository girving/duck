GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -prof -auto-all
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g
CC = gcc
CFLAGS = -O2 -Wall -Werror -I/opt/local/include

OTHERS = Parse.hs Lex.hs
TESTS = basic layout curry delay match io tyfun success types base-test expseq fac
TESTS_C = apply base ops null
TESTS_FAIL := $(patsubst test/fail/%.duck, fail/%, $(wildcard test/fail/*.duck))

default: duck

info: Parse.info

### Compile

.PHONY: duck
duck: Duck.hs runtime.o $(OTHERS)
	$(GHC) $(GHCFLAGS) --make Duck.hs runtime.o -lgc -o $@

%.hs: %.y
	@rm -f $@
	umask a-w ; $(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	@rm -f $@
	umask a-w ; $(ALEX) $(ALEXFLAGS) $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) -c $<

runtime.o: runtime.h

### Generate Haskell files from Duck

GEN = ./duck --haskell
.PHONY: gen
gen:
	$(GEN) var.duck > Gen/Var.hs
	$(GEN) type.duck > Gen/Type.hs
	$(GEN) srcLoc.duck > Gen/SrcLoc.hs
	$(GEN) prims.duck > Gen/Prims.hs
	$(GEN) lir.duck > Gen/Lir.hs
	$(GEN) value.duck > Gen/Value.hs

### Test

ALL_TESTS = $(TESTS) $(TESTS_C) $(TESTS_FAIL)
.PHONY: test $(ALL_TESTS)
test: $(ALL_TESTS)
	@echo
	@echo All tests passed!
$(TESTS): duck
	./duck test/$@.duck
$(TESTS_C): duck
	./duck -c test/$@.duck
$(TESTS_FAIL): duck
	@echo "! ./duck -Itest test/$@.duck"
	@./duck -Itest test/$@.duck; s=$$?; if [ $$s -eq 1 ]; then :; else echo $@ failed: exit status $$s != 1; false; fi

### Misc

tags: $(filter-out $(OTHERS),$(wildcard *.hs)) Parse.y Lex.x
	hasktags -c $^

.PHONY: clean
clean:
	rm -f *.o *.hi *.info duck $(OTHERS)
