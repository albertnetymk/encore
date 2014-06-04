SRC_DIR=src
ENCOREC=$(SRC_DIR)/front/encorec

RUNTIME_DIR=$(SRC_DIR)/runtime

SET_DIR=$(RUNTIME_DIR)/set
SET_INC=$(SET_DIR)/set.h
SET_LIB=$(SET_DIR)/set.o

PONY_DIR=$(RUNTIME_DIR)/pony
PONY_INC=$(PONY_DIR)/inc/pony
PONY_LIB=$(PONY_DIR)/bin/debug/libpony.a

FUTURE_DIR=$(RUNTIME_DIR)/future
FUTURE_INC=$(FUTURE_DIR)/context.h
FUTURE_LIB=$(FUTURE_DIR)/context.o

RELEASE_DIR=release
INC_DIR=$(RELEASE_DIR)/inc
LIB_DIR=$(RELEASE_DIR)/lib

PONY_OBJECTS=$(PONY_LIB) $(PONY_INC)
SET_OBJECTS=$(SET_LIB) $(SET_INC)
FUTURE_OBJECTS=$(FUTURE_INC) $(FUTURE_LIB)

all: encorec

encorec: runtime
	make -C $(SRC_DIR) all
	cp -r $(ENCOREC) $(RELEASE_DIR)

test:
	make -C $(SRC_DIR) test

doc:
	haddock -o $@ -h $$(find . -name "*.hs" | grep -v "\.#")
	make -C $(SET_DIR) doc

runtime: $(PONY_OBJECTS) $(SET_OBJECTS) $(FUTURE_OBJECTS)

$(PONY_OBJECTS):
	make -C $(SRC_DIR) pony
	mkdir -p $(INC_DIR)
	mkdir -p $(LIB_DIR)
	cp -r $(PONY_INC) $(INC_DIR)
	cp -r $(PONY_LIB) $(LIB_DIR)

$(SET_OBJECTS):
	make -C $(SRC_DIR) set
	mkdir -p $(INC_DIR)
	mkdir -p $(LIB_DIR)
	cp -r $(SET_INC) $(INC_DIR)
	cp -r $(SET_LIB) $(LIB_DIR)

$(FUTURE_OBJECTS):
	@echo "#############"
	make -C $(FUTURE_DIR)
	mkdir -p $(INC_DIR)
	mkdir -p $(LIB_DIR)
	cp -r $(FUTURE_INC) $(INC_DIR)
	cp -r $(FUTURE_LIB) $(LIB_DIR)

clean:
	make -C $(SRC_DIR) clean
	rm -rf $(RELEASE_DIR)
	rm -rf $(INC_DIR)
	rm -rf $(LIB_DIR)
	rm -rf doc

.PHONY: all doc runtime encorec clean $(PONY_OBJECTS) $(SET_OBJECTS) $(FUTURE_OBJECTS) runtime
