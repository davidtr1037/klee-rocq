CC=clang
OPT=opt
DIS=llvm-dis
CFLAGS="-I/home/david/research/verified-se/klee-coq/include"
KLEE_BUILD=/home/david/research/verified-se/klee-coq-build

SRC_FILES=$(shell ls test_*.c)
BC_FILES=$(SRC_FILES:.c=.bc)

all: $(BC_FILES)

%.bc: %.c
	$(CC) $(CFLAGS) -fsanitize=bool -Xclang -disable-O0-optnone -c -g -emit-llvm $< -o $@
	$(OPT) -mem2reg $@ -o $@
	$(DIS) $@

%.gcov: %.c
	gcc $(CFLAGS) --coverage $< -L $(KLEE_BUILD)/lib -lkleeRuntest -lgcov -o $@

clean:
	rm $(BC_FILES)
