ROCQOPTS = -Q ../../theories codegen -I ../../src
ROCQC = rocq c

TARGETS = bool.h bool.c bool.o \
	  nat.h nat.c nat.o \
	  ascii.h ascii.c ascii.o \
	  str.h str.c str.o

all: $(TARGETS)

bool.vo bool.h bool.c : bool.v
	$(ROCQC) $(ROCQOPTS) bool.v

bool.o : bool.c bool.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

nat.vo nat.h nat.c : nat.v
	$(ROCQC) $(ROCQOPTS) nat.v

nat.o : nat.c nat.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

ascii.vo ascii.h ascii.c : ascii.v
	$(ROCQC) $(ROCQOPTS) ascii.v

ascii.o : ascii.c ascii.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

str.vo str.h str.c : str.v
	$(ROCQC) $(ROCQOPTS) str.v

str.o : str.c str.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f \
	  *.o \
	  *.a \
	  *.vo \
	  *.vok \
	  *.vos \
	  *.glob \
	  $(TARGETS)
