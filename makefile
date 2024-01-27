FLAGS := -O3 -flto -DATS_MEMALLOC_LIBC

DATS_FILES := main.dats file.dats vector.dats

all: main

main: ${DATS_FILES}
	patscc ${FLAGS} -o atshell $^

# Typecheck only
check: ${DATS_FILES}
	patscc ${FLAGS} -tcats -o atshell $^
