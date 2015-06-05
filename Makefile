O1FLAGS=-fauto-inc-dec -fcprop-registers -fdce -fdefer-pop -fdelayed-branch -fdse -fguess-branch-probability -fif-conversion2 -fif-conversion -fipa-pure-const -fipa-reference -fmerge-constants -fsplit-wide-types -ftree-builtin-call-dce -ftree-ccp -ftree-ch -ftree-copyrename -ftree-dce  -ftree-dominator-opts -ftree-dse -ftree-forwprop  -ftree-fre -ftree-phiprop -ftree-sra -ftree-pta -ftree-ter -funit-at-a-time
O2FLAGS=-fthread-jumps -falign-functions -falign-jumps -falign-loops -fcaller-saves -fcrossjumping -fcse-follow-jumps -fcse-skip-blocks -fdelete-null-pointer-checks -fexpensive-optimizations -fgcse -fgcse-lm -finline-small-functions -findirect-inlining -fipa-sra -foptimize-sibling-calls -fpeephole2 -fregmove -freorder-blocks -freorder-functions -frerun-cse-after-loop -fsched-interblock -fsched-spec -fschedule-insns -fschedule-insns2 -fstrict-aliasing -fstrict-overflow -ftree-switch-conversion -ftree-pre -ftree-vrp
O3FLAGS=-finline-functions -funswitch-loops -fpredictive-commoning -fgcse-after-reload -ftree-vectorize -fipa-cp-clone
ifeq ($(DONTOPT), y)
	OFLAGS=
else
	OFLAGS=${O1FLAGS} ${O2FLAGS} ${O3FLAGS}
endif
FLAGS=-m32 -g -save-temps -funroll-loops -ffast-math -fno-omit-frame-pointer -march=i686 ${PLATFORM} ${OFLAGS}
DFLAGS=${FLAGS} -frelease -fversion=NoDelete -combine -fwhole-program
PARAMS=
OBJSUFFIX=-opt
LDFLAGS=.obj${OBJSUFFIX}/threadlocals.o ${PLATFORM}
SOURCES=ast/dominf.d fcc.d tools/log.d tools/text.d tools/compat.d tools/base.d tools/smart_import.d tools/ctfe.d tools/tests.d classgraph.d ast/parse.d ast/base.d llvmfile.d parseBase.d casts.d tools/mersenne.d tools/threads.d tools/page_queue.d tools/behave_as.d errors.d tools/functional.d ast/types.d ast/namespace.d ast/int_literal.d ast/float_literal.d tools/time.d ast/fold.d ast/scopes.d ast/variable.d ast/opers.d ast/assign.d ast/pointer.d ast/casting.d ast/literals.d ast/static_arrays.d ast/aggregate.d ast/vardecl.d ast/modules.d ast/fun.d ast/stringparse.d tools/threadpool.d quicksort.d ast/aggregate_parse.d ast/returns.d ast/math.d ast/ifstmt.d ast/conditionals.d ast/tuples.d ast/structure.d ast/loops.d ast/iterator.d ast/literal_string.d ast/arrays.d ast/structfuns.d ast/nestfun.d ast/stackframe.d ast/dg.d ast/aliasing.d ast/properties.d ast/tuple_access.d ast/unary.d ast/index.d ast/slice.d ast/type_info.d ast/oop.d ast/tenth.d ast/newexpr.d ast/funcall.d ast/guard.d ast/withstmt.d ast/templ.d ast/globvars.d ast/context.d ast/concat.d ast/stringex.d ast/c_bind.d ast/externs.d ast/eval.d ast/iterator_ext.d ast/vector.d ast/intr.d ast/conditional_opt.d ast/cond.d ast/nulls.d ast/sa_index_opt.d ast/intrinsic.d ast/pragmas.d ast/mode.d ast/propcall.d ast/properties_parse.d ast/main.d ast/alignment.d ast/modules_parse.d ast/platform.d ast/longmath.d ast/mixins.d ast/enums.d ast/import_parse.d ast/trivial.d ast/fp.d ast/expr_statement.d ast/macros.d ast/vardecl_expr.d ast/property.d ast/condprop.d alloc.d quickformat.d dwarf2.d ast/vardecl_parse.d ast/typeset.d ast/repl.d ast/dependency.d memconserve_stdfile.d ast/prefixfun.d base.d llvmtype.d cache.d ast/forex.d
PROFILE_USE=-fbranch-probabilities -funroll-loops -fpeel-loops -ftracer
# GDCPREFIX=/opt/newgdc/bin/

.SUFFIXES: .d

all: build

build:
	@echo
	@echo "Building .. "
	@rm fcc.gcda || true
	@${GDCPREFIX}gcc ${FLAGS} -c -o .obj${OBJSUFFIX}/threadlocals.o threadlocals.c
	${GDCPREFIX}gdc ${DFLAGS} $(LDFLAGS) $(SOURCES) -o fcc ${LINKAUX}
	@# ${GDCPREFIX}gdc -fprofile-generate ${DFLAGS} $(LDFLAGS) $(SOURCES) -o fcc 
	@# @echo "Generating profile .. "
	@# @fcc hello.nt
	@# @echo "Rebuilding .. "
	@# @${GDCPREFIX}gdc ${PROFILE_USE} ${DFLAGS} $(LDFLAGS) $(SOURCES) -o fcc 