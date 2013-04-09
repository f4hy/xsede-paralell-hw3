# You must use PrgEnv-cray.

CC = icc -O3
UPCC = sgiupc
# If you change this, also change the mppwidth parameter in "job-knapsack" accordingly
# NTHREADS = 4

TARGETS=serial knapsack autograder

all: $(TARGETS)

serial: serial.cpp
	$(CC) -o $@ $<
	
autograder: autograder.cpp
	$(CC) -o $@ $<
	
knapsack: knapsack.upc
	$(UPCC) -o $@ $<

clean:
	rm -f *.o *.out *.w2c.c *.w2c.h $(TARGETS)
