GHC = ghc
GHCFLAGS = -O -Werror -fwarn-tabs
HAPPY = happy
HAPPYFLAGS = -agc

all: duck

duck: Duck.hs Parse.hs
	$(GHC) $(GHCFLAGS) --make $< -o $@

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -o $@
