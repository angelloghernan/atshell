FLAGS := -O3 -flto -DATS_MEMALLOC_LIBC

all: main

main: main.dats file.dats
	patscc ${FLAGS} -o atshell main.dats file.dats

# Typecheck only
check: main.dats file.dats
	patscc ${FLAGS} -tcats -o atshell main.dats file.dats

