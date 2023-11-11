.PHONY: andrun check check-all check-everything build build-2.6.3 run clean

andrun : build run

check:
	env AGDA_DIR="./libs" agda src/Main.agda

check-all:
	./scripts/check-all.sh

check-everything: src/Everything.agda
	env AGDA_DIR="./libs" agda src/Everything.agda

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
	rm -f src/Everything.agda

# Don't cache src/Everything.agda as it will break everytime some file is deleted
.PHONY: src/Everything.agda
src/Everything.agda:
	echo '{-# OPTIONS --sized-types #-}' > src/Everything.agda
	echo '{-# OPTIONS --allow-unsolved-metas #-}' >> src/Everything.agda
	echo '{-# OPTIONS --guardedness #-}' >> src/Everything.agda
	echo 'module Everything where' >> src/Everything.agda
	find src -regextype posix-extended -regex '.*/.*\.l?agda(.md)?' -not -path 'src/Everything.agda' | sed -E 's|^src/|import |; s|\.l?agda(.md)?$$||; s|/|.|g' >> src/Everything.agda
