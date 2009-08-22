GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -prof -auto-all
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g

OTHERS = Parse.hs Lex.hs
TESTS = basic layout curry delay match io tyfun
TESTS_C = apply base ops null

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs $(OTHERS)
	$(GHC) $(GHCFLAGS) --make $< -o $@

%.hs: %.y
	chmod -f +w $@
	$(HAPPY) $(HAPPYFLAGS) $< -o $@
	chmod -w $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	chmod -f +w $@
	$(ALEX) $(ALEXFLAGS) $< -o $@
	chmod -w $@

.PHONY: test $(TESTS) $(TESTS_C)
test: $(TESTS) $(TESTS_C)
$(TESTS):
	./duck test/$@.duck
$(TESTS_C):
	./duck -c test/$@.duck

.PHONY: clean
clean:
	rm -f *.o *.hi *.info duck $(OTHERS)
