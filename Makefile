AGDA = agda

SRC= DurationMonad-L-wave.agda DurationMonad-L-bar.agda Equiv-MX.agda Properties-L-wave.agda DecidableOrder.agda

#$(wildcard *.agda)
TGS=$(foreach FILE, $(SRC), $(FILE)i)
HTML=$(foreach FILE, $(SRC), $(FILE:.agda=.html))

# Default goal
.PHONY: default
default: $(TGS) 

%.agdai: $(SRC) 
	@echo Compiling $@
	$(AGDA) $(@:.agdai=.agda)

html: $(HTML)

%.html: $(SRC)
	$(AGDA) --html $(@:.html=.agda)

clean:
	rm -f $(wildcard *.agdai)

# For debugging variables
print-%  : ; @echo $* = $($*)

 
