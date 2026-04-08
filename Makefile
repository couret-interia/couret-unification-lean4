.PHONY: build clean validate

build:
	lake build

clean:
	lake clean

validate:
	bash scripts/validate_pack.sh
