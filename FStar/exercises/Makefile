INCLUDE_DIRS = \
  $(SOURCE_DIRS) \
  $(FSTAR_HOME)/ulib/.cache \
  $(KREMLIN_HOME)/kremlib \
  $(KREMLIN_HOME)/kremlib/obj \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/obj


FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDE_DIRS))

%.fst-in:
	@echo $(FSTAR_INCLUDES)

%.fsti-in:
	@echo $(FSTAR_INCLUDES)
