TESTDIRS += tests/ok/00-basicos
TESTDIRS += tests/ok/10-sugar
TESTDIRS += tests/ok/20-tysym
TESTDIRS += tests/ok/30-opts

TESTS	:= $(shell find $(TESTDIRS) -name '*.fd4' -type f | sort)

# Los binarios. La primer línea es una magia para encontrar el
# ejecutable que crea stack, porque correr 'stack run' es recontra lento
# (~30x). Además, encontralo nos sirve para marcar la dependencia, y no
# volver a correr los tests si el compilador no cambió (pero sí correr
# la VM si cambió la VM, etc).
EXE	:= $(shell cabal exec whereis compiladores2023 | awk '{print $$2};')
VM	:= ./vm/macc
#CC := gcc runtime.c -lgc -o

EXTRAFLAGS	:= 
# EXTRAFLAGS	+= --optimize

# Las reglas a chequear. Se puede deshabilitar toda una familia de tests
# comentando una de estas líneas.
CHECK	+= $(patsubst %,%.check_eval,$(TESTS))
CHECK	+= $(patsubst %,%.check_cek,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc32_h,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc32,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc32noopt_h,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc32noopt,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc8_h,$(TESTS))
CHECK	+= $(patsubst %,%.check_bc8noopt_h,$(TESTS))
CHECK	+= $(patsubst %,%.check_eval_opt,$(TESTS))
# CHECK	+= $(patsubst %,%.check_opt,$(TESTS))
CHECK	+= $(patsubst %,%.check_c,$(TESTS))

# Ejemplo: así se puede apagar un test en particular.
# CHECK	:= $(filter-out tests/correctos/grande.fd4.check_bc32,$(CHECK))

# Esta regla corre todos los tests (por sus dependencias) y luego
# imprime un mensaje.
test_all: $(CHECK)
	@echo "---------------------------------"
	@echo "             Todo OK             "
	@echo "---------------------------------"

Q=@
ifneq ($(V),)
	Q=
endif

# Esto cancela la regla por defecto de make para generar un .out
# copiando el archivo original.
%.out: %

# Aceptar la salida de los programas como correcta. Copia de la salida
# real del evaluador hacia los .out que contienen la salida esperada.
#
# Si no existen los archivos, los crea, así que esto puede usarse para
# agregar un nuevo test.
#
# La _única_ salida que se acepta es la del --eval. Todos los demás
# evaluadores/backends deben coincidir.
accept: $(patsubst %,%.accept,$(TESTS))

# La otra salida esperada es la de las optimizaciones.
# accept: $(patsubst %,%.accept_opt,$(TESTS))

%.accept: %.actual_out_eval
	@echo "ACCEPT	$(patsubst %.accept,%,$@)"
	$(Q)cp $< $(patsubst %.actual_out_eval,%.out,$<)

# Generar salida con el evaluador naive.
%.actual_out_eval: % $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --eval $< > $@

# Comparar salida naive con esperada.
%.check_eval: %.out %.actual_out_eval
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	EVAL	$(patsubst %.out,%,$<)"

# Idem CEK
%.actual_out_cek: % $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --cek $< > $@

%.check_cek: %.out %.actual_out_cek
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	CEK	$(patsubst %.out,%,$<)"

# Bytecode sin optimizaciones. Primero la regla para generar el bytecode, no se chequea
# nada.
%.noopt.bc32: %.fd4 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --bytecompileNoOpt $< >/dev/null

# Correr bytecode para generar la salida (con VM en C).
# Finalmente la comparación.
%.fd4.actual_out_bc32noopt: %.noopt.bc32 $(VM)
	$(Q)$(VM) $< > $@

%.check_bc32noopt: %.out %.actual_out_bc32noopt
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC32NO		$(patsubst %.out,%,$<)"

# Idem pero para Macchina en Haskell.
%.fd4.actual_out_bc32noopt_h: %.noopt.bc32 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --runVM $< > $@

%.check_bc32noopt_h: %.out %.actual_out_bc32noopt_h
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC32NO H	$(patsubst %.out,%,$<)"

# Bytecode. Primero la regla para generar el bytecode, no se chequea
# nada.
%.bc32: %.fd4 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --bytecompile $< >/dev/null

# Correr bytecode para generar la salida (con VM en C).
# Finalmente la comparación.
%.fd4.actual_out_bc32: %.bc32 $(VM)
	$(Q)$(VM) $< > $@

%.check_bc32: %.out %.actual_out_bc32
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC32	$(patsubst %.out,%,$<)"

# Idem pero para Macchina en Haskell.
%.fd4.actual_out_bc32_h: %.bc32 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --runVM $< > $@

%.check_bc32_h: %.out %.actual_out_bc32_h
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC32 H	$(patsubst %.out,%,$<)"



# Bytecode8 sin optimizaciones. Primero la regla para generar el bytecode, no se chequea
# nada.
%.noopt.bc8: %.fd4 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --bytecompileNoOpt8 $< >/dev/null

# chequeo si coninside la salida con ejecutarlo en la macchina en haskell.
%.fd4.actual_out_bc8noopt_h: %.noopt.bc8 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --runVM8 $< > $@

%.check_bc8noopt_h: %.out %.actual_out_bc8noopt_h
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC8NO H	$(patsubst %.out,%,$<)"

# Bytecode8. Primero la regla para generar el bytecode, no se chequea
# nada.
%.bc8: %.fd4 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --bytecompile8 $< >/dev/null

# chequeo si coninside la salida con ejecutarlo en la macchina en haskell.
%.fd4.actual_out_bc8_h: %.bc8 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --runVM8 $< > $@

%.check_bc8_h: %.out %.actual_out_bc8_h
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	BC8 H	$(patsubst %.out,%,$<)"



# Chequear optimizaciones. No se corre nada, sólo se compara
# la salida de --typecheck --optimize respecto a la esperada
# (guardada en un archivo)
%.actual_opt_out: % $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --typecheck --optimize $< > $@

%.check_opt: %.opt_out %.actual_opt_out
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	OPT	$(patsubst %.out,%,$<)"

%.accept_opt: %.actual_opt_out
	cp $< $(patsubst %.actual_opt_out,%.opt_out,$<)

# Evaluar código optimizado, sólo vía eval, se supone que debe ser
# suficiente.

%.actual_out_eval_opt: % $(EXE)
	$(Q)$(EXE) --eval --optimize $< > $@

%.check_eval_opt: %.out %.actual_out_eval_opt
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	EVALOPT	$(patsubst %.out,%,$<)"

# C. Primero la regla para generar el codigo C, no se chequea nada.
%.c: %.fd4 $(EXE)
	$(Q)$(EXE) $(EXTRAFLAGS) --cc $< >/dev/null

%.exe: %.c 
	$(Q)$(CC) $< -Wno-int-conversion -Wno-incompatible-pointer-types runtime.c -lgc -o $@

# Correr en C.
# Finalmente la comparación.
%.fd4.actual_out_c: %.exe
	$(Q)./$< > $@

%.check_c: %.out %.actual_out_c
	$(Q)diff -u $^
	$(Q)touch $@
	@echo "OK	CC	$(patsubst %.out,%,$<)"

# Estas directivas indican que NO se borren los archivos intermedios,
# así podemos examinarlos, particularmente cuando algo no anda.
.SECONDARY: $(patsubst %,%.actual_out_eval,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_cek,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_c,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc32,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc32_h,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc32noopt,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc32noopt_h,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc8noopt_h,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_bc8_h,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_out_eval_opt,$(TESTS))
.SECONDARY: $(patsubst %,%.actual_opt_out,$(TESTS))
.SECONDARY: $(patsubst %.fd4,%.bc32,$(TESTS))
.SECONDARY: $(patsubst %.fd4,%.bc32noopt,$(TESTS))
.SECONDARY: $(patsubst %.fd4,%.bc8,$(TESTS))
.SECONDARY: $(patsubst %.fd4,%.bc8noopt,$(TESTS))
.SECONDARY: $(patsubst %.fd4,%.c,$(TESTS))

.PHONY: test_all accept
