CC = gcc
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wno-parentheses -fno-math-errno

# The library is built without and with the inexact flag (see the
# README), and each test program is linked with both.
LIB = dec-alpha.o da_printing.o da_sincos.o da_log.o
LIB_INEXACT = dec-alpha-inexact.o da_printing-inexact.o \
              da_sincos-inexact.o da_log-inexact.o
TESTS = test-fixed test-fixed-inexact test-random test-random-inexact \
        test-math-random test-math-random-inexact

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

test-math-random: test-math-random.o $(LIB)
	$(CC) $(CFLAGS) -o $@ $^ -lmpfr -lgmp

test-math-random-inexact: test-math-random.o $(LIB_INEXACT)
	$(CC) $(CFLAGS) -o $@ $^ -lmpfr -lgmp

dec-alpha-inexact.o: dec-alpha.c
	$(CC) $(CFLAGS) -DDA_INEXACT -c -o $@ $<

da_printing-inexact.o: da_printing.c
	$(CC) $(CFLAGS) -DDA_INEXACT_PRINTF -c -o $@ $<

da_sincos-inexact.o: da_sincos.c
	$(CC) $(CFLAGS) -DDA_INEXACT -c -o $@ $<

da_log-inexact.o: da_log.c
	$(CC) $(CFLAGS) -DDA_INEXACT -c -o $@ $<

demo.o $(LIB) $(LIB_INEXACT) test-fixed.o test-random.o \
test-math-random.o: dec-alpha.h
$(LIB) $(LIB_INEXACT): da_internal.h
test-random.o test-math-random.o: test-random.h

gen_sincos: gen_sincos.c gen_approx.c
	$(CC) $(CFLAGS) -o $@ $(filter %.c,$^) -lmpfr -lgmp -lm

gen_log: gen_log.c gen_approx.c
	$(CC) $(CFLAGS) -o $@ $(filter %.c,$^) -lmpfr -lgmp -lm

gen_sincos gen_log: gen_approx.h

.PHONY: check clean
check: $(TESTS)
	./test-fixed
	./test-fixed-inexact
	./test-fixed print > print.out
	./test-fixed strings | cmp - print.out
	./test-random
	./test-random-inexact
	./test-math-random
	./test-math-random-inexact

clean:
	rm -f demo $(TESTS) gen_sincos gen_log *.o print.out
