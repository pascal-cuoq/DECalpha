CC = gcc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wno-parentheses -fno-math-errno

demo: demo.o dec-alpha.o da_printing.o
	$(CC) $(CFLAGS) -o $@ $^

test-fixed: test-fixed.o dec-alpha.o da_printing.o
	$(CC) $(CFLAGS) -o $@ $^

test-random: test-random.o dec-alpha.o da_printing.o
	$(CC) $(CFLAGS) -o $@ $^ -lgmp

demo.o dec-alpha.o da_printing.o test-fixed.o test-random.o: dec-alpha.h

.PHONY: check clean
check: test-fixed test-random
	./test-fixed
	./test-fixed print > print.out
	./test-fixed strings | cmp - print.out
	./test-random

clean:
	rm -f demo test-fixed test-random *.o print.out
