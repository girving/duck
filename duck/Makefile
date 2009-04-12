GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing -XPatternGuards
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs Parse.hs Lex.hs
	$(GHC) $(GHCFLAGS) --make $< -o $@

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	$(ALEX) $(ALEXFLAGS) $< -o $@

.PHONY: clean
clean:
	rm *.o *.hi *.info duck Parse.hs 
