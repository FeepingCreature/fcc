MAIN=fcc
(
	echo 'LDFLAGS=-B/opt/gold'
	echo 'DFLAGS=-g -femit-templates=all'
	echo 'PARAMS='
	gdc ${MAIN}.d -fd-verbose -c -o /dev/null \
		|grep "^import\b" \
		|grep -v "(/" \
		|sed -e "s@.*(@@" -e "s@).*@@" \
		|xargs echo SOURCES=${MAIN}.d
	echo '
OBJECTS=${SOURCES:%.d=.obj/%.o}

.SUFFIXES:

.SUFFIXES: .d .o

all: $(SOURCES) link

clean:
	rm $(OBJECTS) 2>/dev/null

msg:
	@echo -n "Compiling .. "

link: msg $(OBJECTS)
	@echo
	@echo "Linking .. "
	@gdc $(LDFLAGS) $(OBJECTS) -o ' $MAIN '

run: link
	@echo "Running .. "
'
echo "	@./${MAIN} \$(PARAMS)"
echo '
.obj/%.o: %.d
	@mkdir -p `dirname $@`
	@echo -n $<\ 
	@echo -en "\e7\x9b1;H\x9b1m\x9b42m\x9b37m[$(shell sh status.sh $(SOURCES))]\x9b22m\e8"
	@gdc $(DFLAGS) $< -c -o $@
') > Makefile
echo '#!/bin/bash
find .obj -name \*.o |wc -l |xargs echo -n
echo -n " / "
echo $@ |sed -e "s@ @\n@g" |wc -l |xargs echo -n
' > status.sh

make || (
	OBJS=""
	make 2>&1 |(grep -B1 "undefined reference" || exit) \
	|head -n 1 |sed -e "s@:.*@@" |(grep "\\.o$" || exit) \
	|while read OBJ; do OBJS="$OBJS,$OBJ"; rm "$OBJ"; done
	echo "Remove $OBJS; retry"
	$0 $@
)
