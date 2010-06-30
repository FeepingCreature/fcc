MAIN=fcc
(
	echo 'LDFLAGS='
	echo 'DFLAGS=-g -femit-templates=all'
	gdc ${MAIN}.d -fd-verbose -c -o /dev/null \
		|grep import \
		|grep -v "(/" \
		|sed -e "s@.*(@@" -e "s@).*@@" \
		|xargs echo SOURCES=${MAIN}.d
	echo '
OBJECTS=${SOURCES:%.d=.obj/%.o}

.SUFFIXES:

.SUFFIXES: .d .o

all: $(SOURCES) link

clean:
	rm $(OBJECTS)

msg:
	@echo -n "Compiling .. "

link: msg $(OBJECTS)
	@echo
	@echo "Linking .. "
	@gdc $(LDFLAGS) $(OBJECTS) -o ' $MAIN '

.obj/%.o: %.d
	@mkdir -p `dirname $@`
	@echo -n $<\ 
	@gdc $(DFLAGS) $< -c -o $@
') > Makefile
make || (
	OBJS=""
	make 2>&1 |(grep -B1 "undefined reference" || exit) \
	|head -n 1 |sed -e "s@:.*@@" |(grep "\\.o$" || exit) \
	|while read OBJ; do OBJS="$OBJS,$OBJ"; rm "$OBJ"; done
	echo "Remove $OBJS; retry"
	$0 $@
)
