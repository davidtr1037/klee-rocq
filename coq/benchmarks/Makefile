CC=clang
OPT=opt
DIS=llvm-dis
CFLAGS="-I/home/david/research/verified-se/klee-coq/include"
KLEE_BUILD=/home/david/research/verified-se/klee-coq-build

all: $(TARGET)

%.bc: %.c
	$(CC) $(CFLAGS) -fsanitize=bool -Xclang -disable-O0-optnone -c -g -emit-llvm $< -o $@
	$(OPT) -mem2reg $@ -o $@
	$(DIS) $@

%.gcov: %.c
	gcc $(CFLAGS) --coverage $< -L $(KLEE_BUILD)/lib -lkleeRuntest -lgcov -o $@
