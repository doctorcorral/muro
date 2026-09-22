AGDA  := agda
# --no-libraries: vendored stdlib ships extra .agda-lib files (tests, cubical).
AFLAGS := --no-libraries -i agda -i vendor/agda-stdlib/src --warning=noUnsupportedIndexedMatch

# Theorem modules — Judgement, Wall, Consistency, Typing, Convert,
# Reduction, Spine, Data and what they import (Base, Syntax, Subst,
# SubstLemmas, Env) — are checked under --safe: no postulates, no
# TERMINATING, no --type-in-type. Check.agda is the fuelled
# decision procedure and carries TERMINATING pragmas (as does Unembed), so
# the full tree is checked without --safe.
.PHONY: agda agda-safe agda-all agda-syntax agda-check elixir clean

agda: agda-safe agda-all

agda-safe:
	$(AGDA) $(AFLAGS) --safe agda/Muro/Wall.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Consistency.agda

agda-all:
	$(AGDA) $(AFLAGS) agda/Muro.agda

agda-syntax:
	$(AGDA) $(AFLAGS) agda/Muro/Syntax.agda
	$(AGDA) $(AFLAGS) agda/Muro/Subst.agda

agda-check:
	$(AGDA) $(AFLAGS) agda/Muro/Check.agda

elixir:
	mix test

clean:
	find agda -name '*.agdai' -delete
	rm -rf agda/_build _build deps
