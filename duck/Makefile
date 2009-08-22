GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -prof -auto-all
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g

OTHERS = Parse.hs Lex.hs
TESTS = basic layout curry delay match io tyfun success
TESTS_C = apply base ops null
TESTS_FAIL := $(patsubst test/fail/%.duck, fail/%, $(wildcard test/fail/*.duck))

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs $(OTHERS)
	$(GHC) $(GHCFLAGS) --make $< -o $@

%.hs: %.y
	@rm -f $@
	umask $$(( `umask` | 222 )) ; \
	$(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	@rm -f $@
	umask $$(( `umask` | 222 )) ; \
	$(ALEX) $(ALEXFLAGS) $< -o $@

ALL_TESTS = $(TESTS) $(TESTS_C) $(TESTS_FAIL)
.PHONY: test $(ALL_TESTS)
test: $(ALL_TESTS)
	@echo
	@echo All tests passed!
$(TESTS):
	./duck test/$@.duck
$(TESTS_C):
	./duck -c test/$@.duck
$(TESTS_FAIL):
	! ./duck -Itest test/$@.duck

.PHONY: clean
clean:
	rm -f *.o *.hi *.info duck $(OTHERS)
