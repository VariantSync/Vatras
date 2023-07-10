andrun : build run

build:
	env AGDA_DIR="./libs" agda --compile src/Main.agda

run:
	./src/Main

clean:
	rm -f src/Main
	rm -rf _build
	rm -rf src/MAlonzo
