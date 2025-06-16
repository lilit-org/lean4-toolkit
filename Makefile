.PHONY: check-lean
check-lean:
	@which lean >/dev/null 2>&1 || (echo "error: lean is not installed. please install lean 4 first." && exit 1)
	@which lake >/dev/null 2>&1 || (echo "error: lake is not installed. please install lean 4 first." && exit 1)

.PHONY: build
build: check-lean
	@lake build

.PHONY: clean
clean: check-lean
	@lake clean
	@rm -rf build

.PHONY: test
test: check-lean
	@lake test

.PHONY: serve
serve: check-lean
	@lake serve

.PHONY: update
update: check-lean
	@lake update

.PHONY: run-basics
run-basics: check-lean
	@lake env lean src/Basics.lean

.PHONY: run-simple_proofs_I
run-simple_proofs_I: check-lean
	@lake env lean src/proofs/SimpleProofs_I.lean
