TARGETS = bool.h bool.c bool.o \
	  nat.h nat.c nat.o \
	  ascii.h ascii.c ascii.o \
	  str.h str.c str.o

all: $(TARGETS)

bool.vo bool.h bool.c : bool.v
	coqc bool.v

bool.o : bool.c bool.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

nat.vo nat.h nat.c : nat.v
	coqc nat.v

nat.o : nat.c nat.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

ascii.vo ascii.h ascii.c : ascii.v
	coqc ascii.v

ascii.o : ascii.c ascii.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

str.vo str.h str.c : str.v
	coqc str.v

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
