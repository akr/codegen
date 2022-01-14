all: test_lseq

lseq.vo : lseq.v
	coqc lseq.v

lseq.c lseq.h : gen_lseq.v lseq.vo
	coqc gen_lseq.v

lseq.o : lseq.c
	$(CC) -g -c lseq.c

liblseq.a : lseq.o
	rm -f liblseq.a
	ar rcs liblseq.a lseq.o

test_lseq : test_lseq.c liblseq.a
	$(CC) -g -o test_lseq test_lseq.c -L. -llseq

clean:
	rm -f \
	  *.o \
	  *.a \
	  *.vo \
	  *.vok \
	  *.vos \
	  *.glob \
	  lseq.c \
	  lseq.h \
	  test_lseq
