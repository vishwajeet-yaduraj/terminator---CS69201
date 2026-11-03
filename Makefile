CC = gcc
CFLAGS = -std=c11 -Wall -Wextra -O2
SOURCE = terminator.c
TARGET = terminator
LDLIBS = -lX11 -pthread

.PHONY: all clean

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CC) $(CFLAGS) $(SOURCE) -o $(TARGET) $(LDLIBS)

clean:
	rm -f $(TARGET)
