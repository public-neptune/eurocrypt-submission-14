CC ?= cc
CFLAGS ?= -std=c11 -O3 -march=native -pthread
BUILD := build
HENBANE := $(BUILD)/henbane
CLOSURE := $(BUILD)/closure
HENBANE_PSL_MATRIX := $(BUILD)/henbane-psl-matrix
HENBANE_SL_VERIFY := $(BUILD)/henbane-sl-verify
HENBANE_SYMMETRIC_VERIFY := $(BUILD)/henbane-symmetric-verify
PSL_SELFTEST := $(BUILD)/psl2-selftest
PREPROCESS := $(BUILD)/preprocess

# Symmetric dimensions are read from the flat presentation at runtime.
all: $(HENBANE) $(CLOSURE) $(HENBANE_PSL_MATRIX) $(HENBANE_SL_VERIFY) \
	$(HENBANE_SYMMETRIC_VERIFY) $(PREPROCESS)

$(BUILD):
	mkdir -p $@

$(HENBANE): henbane.c | $(BUILD)
	$(CC) $(CFLAGS) -o $@ henbane.c

$(CLOSURE): closure.c | $(BUILD)
	$(CC) -O3 -march=native -o $@ closure.c

$(PSL_SELFTEST): psl2_343/group.c psl2_343/group.h tests/psl_native_selftest.c | $(BUILD)
	$(CC) $(CFLAGS) -o $@ psl2_343/group.c tests/psl_native_selftest.c

$(HENBANE_PSL_MATRIX): psl2_343/matrix_solver.c psl2_343/group.c psl2_343/group.h | $(BUILD)
	$(CC) $(CFLAGS) -o $@ psl2_343/matrix_solver.c psl2_343/group.c

$(HENBANE_SL_VERIFY): psl2_343/sl_verifier.c | $(BUILD)
	$(CC) $(CFLAGS) -o $@ $< -lz

$(HENBANE_SYMMETRIC_VERIFY): symmetric_verifier.c | $(BUILD)
	$(CC) $(CFLAGS) -o $@ $< -lz

$(PREPROCESS): preprocessing/native.c | $(BUILD)
	$(CC) -std=c11 -O3 -march=native -o $@ preprocessing/native.c

henbane: $(HENBANE)
closure: $(CLOSURE)
henbane-psl-matrix: $(HENBANE_PSL_MATRIX)
henbane-sl-verify: $(HENBANE_SL_VERIFY)
henbane-symmetric-verify: $(HENBANE_SYMMETRIC_VERIFY)
psl2-selftest: $(PSL_SELFTEST)
preprocess: $(PREPROCESS)

clean:
	rm -f $(HENBANE) $(CLOSURE) $(PSL_SELFTEST) $(PREPROCESS) \
		$(HENBANE_PSL_MATRIX) $(HENBANE_SL_VERIFY) \
		$(HENBANE_SYMMETRIC_VERIFY)

test: all $(PSL_SELFTEST)
	$(PSL_SELFTEST)
	python3 -m unittest discover -s tests -v

test-challenges: all
	python3 check_solution.py challenges/chal_s7_n2.json.gz challenges/solutions/chal_s7_n2.solution.json
	python3 check_solution.py challenges/chal_semi_direct_s7_n2.json.gz challenges/solutions/chal_semi_direct_s7_n2.solution.json
	python3 check_solution.py challenges/chal_s11_n5.json.gz challenges/solutions/chal_s11_n5.solution.json
	python3 check_solution.py challenges/chal_semi_direct_s11_n5.json.gz challenges/solutions/chal_semi_direct_s11_n5.solution.json
	python3 check_solution.py challenges/chal_semi_direct_s11_n5_variant.json.gz challenges/solutions/chal_semi_direct_s11_n5_variant.solution.json
	python3 check_solution.py challenges/challenge_psl2_v1.json.gz challenges/solutions/challenge_psl2_v1.solution.json

.PHONY: all clean test test-challenges henbane closure henbane-psl-matrix henbane-sl-verify \
	henbane-symmetric-verify \
	psl2-selftest preprocess
