andrun : build run

build:
	agda --compile src/Main.agda

run:
	./src/Main
