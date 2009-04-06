GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -XPatternGuards
HAPPY = happy
HAPPYFLAGS = -agc

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs Parse.hs
	$(GHC) $(GHCFLAGS) --make $< -o $@

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

.PHONY: clean
clean:
	rm *.o *.hi *.info duck Parse.hs 
