.PHONY: clean

tester: tester.cc
	g++ -g -O0 -o tester tester.cc

all: tester

check: tester
	./tester	

clean:
	rm -rf tester

