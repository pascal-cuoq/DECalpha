CC = gcc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wno-parentheses -fno-math-errno

# The library is built without and with the inexact flag (see the
# README), and each test program is linked with both.
LIB = dec-alpha.o da_printing.o
LIB_INEXACT = dec-alpha-inexact.o da_printing-inexact.o
TESTS = test-fixed test-fixed-inexact test-random test-random-inexact

demo: demo.o $(LIB)
	$(CC) $(CFLAGS) -o $@ $^

test-fixed: test-fixed.o $(LIB)
	$(CC) $(CFLAGS) -o $@ $^

test-fixed-inexact: test-fixed.o $(LIB_INEXACT)
	$(CC) $(CFLAGS) -o $@ $^

test-random: test-random.o $(LIB)
	$(CC) $(CFLAGS) -o $@ $^ -lgmp

test-random-inexact: test-random.o $(LIB_INEXACT)
	$(CC) $(CFLAGS) -o $@ $^ -lgmp

dec-alpha-inexact.o: dec-alpha.c
	$(CC) $(CFLAGS) -DDA_INEXACT -c -o $@ $<

da_printing-inexact.o: da_printing.c
	$(CC) $(CFLAGS) -DDA_INEXACT_PRINTF -c -o $@ $<

demo.o $(LIB) $(LIB_INEXACT) test-fixed.o test-random.o: dec-alpha.h

.PHONY: check clean
check: $(TESTS)
	./test-fixed
	./test-fixed-inexact
	./test-fixed print > print.out
	./test-fixed strings | cmp - print.out
	./test-random
	./test-random-inexact

clean:
	rm -f demo $(TESTS) *.o print.out
