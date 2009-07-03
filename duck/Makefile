GHC = ghc
GHCFLAGS = -O -Wall -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -prof -auto-all
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs others
	$(GHC) $(GHCFLAGS) --make $< -o $@

others: Parse.hs Lex.hs

test: duck test/basic.duck
	./duck test/basic.duck
	./duck -c test/prelude.duck
	./duck -c test/ops.duck

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	$(ALEX) $(ALEXFLAGS) $< -o $@

.PHONY: clean
clean:
	rm -f *.o *.hi *.info duck Parse.hs Lex.hs
