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
make