TARGETS = bool.h bool.c bool.o \
	  nat.h nat.c nat.o \
	  ascii.h ascii.c ascii.o \
	  str.h str.c str.o

all: $(TARGETS)

bool.vo : bool.v
	coqc bool.v

bool.h bool.c : bool_gen.v bool_api.v bool.vo
	coqtop -batch -l bool_gen.v

bool.o : bool.c bool.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

nat.vo : nat.v
	coqc nat.v

nat.h nat.c : nat_gen.v nat_api.v nat.vo
	coqtop -batch -l nat_gen.v

nat.o : nat.c nat.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

ascii.vo : ascii.v
	coqc ascii.v

ascii.h ascii.c : ascii_gen.v ascii_api.v ascii.vo
	coqtop -batch -l ascii_gen.v

ascii.o : ascii.c ascii.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

str.vo : str.v
	coqc str.v

str.h str.c : str_gen.v str_api.v str.vo
	coqtop -batch -l str_gen.v

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
