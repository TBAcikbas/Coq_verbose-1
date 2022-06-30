CMD = coqc -R . CoqVerbose 
BIN = bin/
SRC = src/
SRC_HINTERS = $(wildcard $(SRC)Hinters/*.v)
SRC_TACTICS = $(wildcard $(SRC)Tactics/*.v)
SRC_EXEMPLES = $(wildcard exemples/*.v)

CIBLE += $(subst src/,, $(patsubst %.v, % ,$(SRC_TACTICS)))
CIBLE  += $(subst src/,, $(patsubst %.v, % ,$(SRC_HINTERS)))
CIBLE_EXEMPLES  = $(subst src/,, $(patsubst %.v, % ,$(SRC_EXEMPLES)))


All: $(CIBLE) $(CIBLE_EXEMPLES)

$(CIBLE)%: 
	$(CMD) $(SRC)$@.v

$(CIBLE_EXEMPLES)%:
	$(CMD) $@.v

.PHONY:
clean:
	rm -f $(SRC)Hinters/*.vos $(SRC)Hinters/*.vok $(SRC)Hinters/*.vo $(SRC)Hinters/.*.aux $(SRC)Hinters/*.glob \
		$(SRC)Tactics/*.vos $(SRC)Tactics/*.vok $(SRC)Tactics/*.vo $(SRC)Tactics/.*.aux $(SRC)Tactics/*.glob \
		exemples/*.vos exemples/*.vok exemples/*.vo exemples/.*.aux exemples/*.glob 