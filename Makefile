all: build check

build:
	time lake build

check:
	time lake lint
	time ./scripts/fmt-changed.sh --allow-dirty --check

fmt:
	time ./scripts/fmt-changed.sh --allow-dirty
	time lake build
	time lake lint
