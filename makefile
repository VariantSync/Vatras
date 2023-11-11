andrun : build run

check:
	env AGDA_DIR="./libs" agda src/Main.agda

.PHONY: check-all
check-all:
	./scripts/check-all.sh

build:
	env AGDA_DIR="./libs" agda --compile src/Main.agda

build-2.6.3:
	env AGDA_DIR="./libs" agda-2.6.3 --compile src/Main.agda

run:
	./src/Main

clean:
	rm -f src/Main
	rm -rf _build
	rm -rf src/MAlonzo
