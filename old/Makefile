
pair : main.o oracle_imp.o
	g++ main.o oracle_imp.o -o pair

main.o: main.cpp
	g++ -c main.cpp

oracle_imp.o: oracle_imp.cpp oracle.h
	g++ -c oracle_imp.cpp

clean:
	rm *.o pair
