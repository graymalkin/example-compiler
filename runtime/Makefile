CC = clang
CC_OPTIONS = -std=c11

all : array.o io.o

array.o : array.c
	$(CC) $(CC_OPTIONS) -c array.c -o array.o

io.o : io.c
	$(CC) $(CC_OPTIONS) -c io.c -o io.o

clean :
	rm -f io.o array.o
