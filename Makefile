CMD = coqc -R . CoqVerbose 
BIN = bin/
SRC = src/
TEST = tests/

SRC_HINTERS = $(wildcard $(SRC)Hinters/*.v)
SRC_TACTICS = $(wildcard $(SRC)Tactics/*.v)
SRC_CONCEPTS =$(wildcard $(SRC)Concepts/*.v)
SRC_EXEMPLES = $(wildcard $(TEST)examples/*.v)
SRC_UNITTEST = $(wildcard $(TEST)unit_test/*.v)

CIBLE  = $(subst src/,, $(patsubst %.v, % ,$(SRC_CONCEPTS)))
CIBLE  += $(subst src/,, $(patsubst %.v, % ,$(SRC_TACTICS)))
CIBLE  += $(subst src/,, $(patsubst %.v, % ,$(SRC_HINTERS)))

CIBLE_EXEMPLES  = $(subst src/,, $(patsubst %.v, % ,$(SRC_EXEMPLES)))
CIBLE_EXEMPLES  += $(subst src/,, $(patsubst %.v, % ,$(SRC_UNITTEST)))

All: $(CIBLE) $(CIBLE_EXEMPLES)
$(CIBLE)%:
	$(CMD) $(SRC)$@.v

$(CIBLE_EXEMPLES)%:
	$(CMD) $@.v



.PHONY:
clean:
	rm -f $(SRC)Hinters/*.vos $(SRC)Hinters/*.vok $(SRC)Hinters/*.vo $(SRC)Hinters/.*.aux $(SRC)Hinters/*.glob \
		$(SRC)Tactics/*.vos $(SRC)Tactics/*.vok $(SRC)Tactics/*.vo $(SRC)Tactics/.*.aux $(SRC)Tactics/*.glob \
		$(SRC)Concepts/*.vos $(SRC)Concepts/*.vok $(SRC)Concepts/*.vo $(SRC)Concepts/.*.aux $(SRC)Concepts/*.glob \
		$(TEST)examples/*.vos $(TEST)examples/*.vok $(TEST)examples/*.vo $(TEST)examples/.*.aux $(TEST)examples/*.glob \
		$(TEST)unit_test/*.vos $(TEST)unit_test/*.vok $(TEST)unit_test/*.vo $(TEST)unit_test/.*.aux $(TEST)unit_test/*.glob 