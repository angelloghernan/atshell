FLAGS := -O3 -flto -DATS_MEMALLOC_LIBC

DATS_FILES := file.dats vector.dats main.dats split_string.dats exec.dats

all: main

main: ${DATS_FILES}
	patscc ${FLAGS} -o atshell $^

# Typecheck only
check: ${DATS_FILES}
	patscc ${FLAGS} -tcats -o atshell $^
