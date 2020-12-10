JASMINC ?= jasminc # point to your jasminc
EASYCRYPT ?= easycrypt # point to your easycrypt

EE = extraction/example
AE = extraction/aeslib
EB = build/example
AB = build/aeslib
EP = proof/example
AP = proof/aeslib
TT = test

OUT_DIR = build $(AB) $(EB)

.PHONY: dirs

all: dirs $(AB)/test_aes $(EB)/test_NbAESEnc $(EB)/test_NbAESEnc_mem \
          $(AE)/AES_jazz.ec $(AE)/AES_jazz_ct.ec \
          $(EE)/NbAESEnc_jazz.ec $(EE)/NbAESEnc_jazz_ct.ec \
          $(EE)/NbAESEnc_mem_jazz.ec $(EE)/NbAESEnc_mem_jazz_ct.ec

# BUILD AES LIB

$(AB)/aes.japp: src/aeslib/aes.jazz dirs
	cpp -nostdinc -DEXPORT_TEST src/aeslib/aes.jazz \
	    | grep -v "^#" > $(AB)/aes.japp

$(AB)/aes.s: $(AB)/aes.japp dirs
	$(JASMINC) $(AB)/aes.japp -o $(AB)/aes.s

# EXTRACT AES LIB FOR CORRECTNESS/SECURITY

$(AE)/AES_jazz.ec: $(AB)/aes.japp dirs
	$(JASMINC) $(AB)/aes.japp -ec aes -ec invaes -oec AES_jazz.ec
	mv AES_jazz.ec Array11.ec WArray176.ec $(AE)

# EXTRACT AES LIB FOR CONSTANT-TIME

$(AE)/AES_jazz_ct.ec: $(AB)/aes.japp dirs
	$(JASMINC) $(AB)/aes.japp -CT -ec aes -ec invaes -oec AES_jazz_ct.ec
	mv AES_jazz_ct.ec Array11.ec WArray176.ec $(AE)

# BUILD NbAESEnc WITH REGISTER CALLING CONVENTION

$(EB)/NbAESEnc.japp: src/example/NbAESEnc.jazz dirs
	cpp -nostdinc src/example/NbAESEnc.jazz  \
	    | grep -v "^#" > $(EB)/NbAESEnc.japp

$(EB)/NbAESEnc.s: $(EB)/NbAESEnc.japp dirs
	$(JASMINC) $(EB)/NbAESEnc.japp -o $(EB)/NbAESEnc.s

# EXTRACT NbAESEnc WITH REGISTER CALLING CONVENTION FOR CORRECTNESS/SECURITY

$(EE)/NbAESEnc_jazz.ec: $(EB)/NbAESEnc.japp dirs
	$(JASMINC) $(EB)/NbAESEnc.japp -ec enc -ec dec -oec NbAESEnc_jazz.ec
	mv NbAESEnc_jazz.ec Array11.ec WArray176.ec $(EE)

# EXTRACT NbAESEnc WITH REGISTER CALLING CONVENTION FOR CONSTANT-TIME

$(EE)/NbAESEnc_jazz_ct.ec: $(EB)/NbAESEnc.japp dirs
	$(JASMINC) $(EB)/NbAESEnc.japp -CT -ec enc -ec dec -oec NbAESEnc_jazz_ct.ec
	mv NbAESEnc_jazz_ct.ec Array11.ec WArray176.ec $(EE)

# BUILD NbAESEnc WITH MEMORY CALLING CONVENTION

$(EB)/NbAESEnc_mem.japp: src/example/NbAESEnc_mem.jazz dirs
	cpp -nostdinc src/example/NbAESEnc_mem.jazz  \
	    | grep -v "^#" > $(EB)/NbAESEnc_mem.japp

$(EB)/NbAESEnc_mem.s: $(EB)/NbAESEnc_mem.japp dirs
	$(JASMINC) $(EB)/NbAESEnc_mem.japp -o $(EB)/NbAESEnc_mem.s

# EXTRACT NbAESEnc WITH MEMORY CALLING CONVENTION FOR CORRECTNESS/SECURITY

$(EE)/NbAESEnc_mem_jazz.ec: $(EB)/NbAESEnc_mem.japp dirs
	$(JASMINC) $(EB)/NbAESEnc_mem.japp -ec enc -ec dec -oec NbAESEnc_mem_jazz.ec
	mv NbAESEnc_mem_jazz.ec Array11.ec WArray176.ec $(EE)

# EXTRACT NbAESEnc WITH MEMORY CALLING CONVENTION FOR CONSTANT-TIME

$(EE)/NbAESEnc_mem_jazz_ct.ec: $(EB)/NbAESEnc_mem.japp dirs
	$(JASMINC) $(EB)/NbAESEnc_mem.japp -CT -ec enc -ec dec -oec NbAESEnc_mem_jazz_ct.ec
	mv NbAESEnc_mem_jazz_ct.ec Array11.ec WArray176.ec $(EE)

# BUILD TESTS

$(AB)/test_aes: $(AB)/aes.s $(TT)/test_aes.c dirs
	gcc -Wall $(AB)/aes.s $(TT)/test_aes.c \
	    -o $(AB)/test_aes

$(EB)/test_NbAESEnc: $(TT)/test_NbAESEnc.c $(EB)/NbAESEnc.s dirs
	gcc -msse4.1 -Wall $(EB)/NbAESEnc.s $(TT)/test_NbAESEnc.c \
	    -o $(EB)/test_NbAESEnc

$(EB)/test_NbAESEnc_mem: $(TT)/test_NbAESEnc_mem.c $(EB)/NbAESEnc_mem.s dirs
	gcc -Wall $(EB)/NbAESEnc_mem.s $(TT)/test_NbAESEnc_mem.c \
	    -o $(EB)/test_NbAESEnc_mem

test: all
	@echo
	@echo '************************************************'
	@echo '***        Testing AES implementation        ***'
	@echo '************************************************'
	$(AB)/test_aes
	@echo
	@echo '************************************************'
	@echo '*** Testing encryption scheme (reg cc)      *** '
	@echo '************************************************'
	$(EB)/test_NbAESEnc
	@echo
	@echo '************************************************'
	@echo '*** Testing encryption scheme (mem cc)      *** '
	@echo '************************************************'
	$(EB)/test_NbAESEnc_mem

safety: all
	@echo
	@echo '************************************************'
	@echo '***    Safety checking AES implementation    ***'
	@echo '************************************************'
	$(JASMINC) -checksafety $(AB)/aes.japp
	@echo
	@echo '************************************************'
	@echo '***Safety checking encryption scheme (reg cc)***'
	@echo '************************************************'
	$(JASMINC) -checksafety $(EB)/NbAESEnc.japp
	@echo
	@echo '************************************************'
	@echo '***Safety checking encryption scheme (mem cc)***'
	@echo '************************************************'
	$(JASMINC) -checksafety $(EB)/NbAESEnc_mem.japp

proofs: all
	@echo
	@echo '************************************************'
	@echo '***        Machine-checking AES proof        ***'
	@echo '************************************************'
	for f in $(AP)/*.ec; do echo $$f; \
	    $(EASYCRYPT) compile $$f -I $(AE); done
	@echo
	@echo '************************************************'
	@echo '*** Machine-checking encryption scheme proof ***'
	@echo '************************************************'
	for f in proof/example/*.eca; do echo $$f; \
	    $(EASYCRYPT) compile $$f -I $(AE) -I $(EE)\
	                          -I $(AP); done
	for f in proof/example/*.ec; do echo $$f; \
	    $(EASYCRYPT) compile $$f -I $(AE) -I $(EE)\
	                          -I $(AP); done

check: test safety proofs

clean: 
	rm -Rf $(AE)/* $(EE)/* build
	rm -f $(AP)/*.eco
	rm -f $(EP)/*.eco

dirs: ${OUT_DIR}

${OUT_DIR}:
	mkdir -p ${OUT_DIR}


