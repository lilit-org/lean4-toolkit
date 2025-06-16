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

.PHONY: update
update: check-lean
	@lake update

.PHONY: definitions
definitions: check-lean
	@lake env lean src/examples/TypeClassesExamples.lean

.PHONY: classics
classics: check-lean
	@lake env lean src/examples/PalindromeExamples.lean
	@lake env lean src/examples/BinaryTreeExamples.lean

.PHONY: proofs
proofs: check-lean
	@lake env lean src/examples/SumsAndMultiExamples.lean
