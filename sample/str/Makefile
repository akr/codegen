TARGETS = bool.h bool.c \
	  nat.h nat.c \
	  ascii.h ascii.c \
	  str.h str.c

all: $(TARGETS)

bool.vo : bool.v
	coqc bool.v

bool.h bool.c : bool_gen.v bool_api.v bool.vo
	coqtop -batch -l bool_gen.v

nat.vo : nat.v
	coqc nat.v

nat.h nat.c : nat_gen.v nat_api.v nat.vo
	coqtop -batch -l nat_gen.v

ascii.vo : ascii.v
	coqc ascii.v

ascii.h ascii.c : ascii_gen.v ascii_api.v ascii.vo
	coqtop -batch -l ascii_gen.v

str.vo : str.v
	coqc str.v

str.h str.c : str_gen.v str_api.v str.vo
	coqtop -batch -l str_gen.v

clean:
	rm -f \
	  *.o \
	  *.a \
	  *.vo \
	  *.vok \
	  *.vos \
	  *.glob \
	  $(TARGETS)
