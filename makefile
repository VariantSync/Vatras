.PHONY: andrun check check-all check-everything build build-2.6.4.3 run clean

andrun : build run

check:
	env AGDA_DIR="./libs" agda src/Vatras/Main.agda

check-all:
	./scripts/check-all.sh

check-everything: src/Vatras/Everything.agda
	env AGDA_DIR="./libs" agda src/Vatras/Everything.agda

build:
	env AGDA_DIR="./libs" agda --compile src/Vatras/Main.agda

build-2.6.4.3:
	env AGDA_DIR="./libs" agda-2.6.4.3 --compile src/Vatras/Main.agda

run:
	./src/Main

clean:
	rm -f src/Main
	rm -rf _build
	rm -rf src/MAlonzo
	rm -f src/Vatras/Everything.agda
	find . -name "*.agdai" -type f -delete

# Don't cache src/Vatras/Everything.agda as it will break everytime some file is deleted
.PHONY: src/Vatras/Everything.agda
src/Vatras/Everything.agda:
	echo '{-# OPTIONS --allow-unsolved-metas #-}' > src/Vatras/Everything.agda
	echo '{-# OPTIONS --guardedness #-}' >> src/Vatras/Everything.agda
	echo 'module Vatras.Everything where' >> src/Vatras/Everything.agda
	find src -regextype posix-extended -regex '.*/.*\.l?agda(.md)?' -not -path 'src/Vatras/Everything.agda' | sed -E 's|^src/|import |; s|\.l?agda(.md)?$$||; s|/|.|g' >> src/Vatras/Everything.agda
