#
# This makefile system follows the structuring conventions
# recommended by Peter Miller in his excellent paper:
#
#	Recursive Make Considered Harmful
#	http://aegis.sourceforge.net/auug97.pdf
#

-include Makelocal

OBJDIR := obj

TOP_DIR := .
ARCH_DIR := $(TOP_DIR)/kern/arch
INCLUDE_DIR := $(TOP_DIR)/kern/include
UNAME=$(shell uname -m)
V = @

# Cross-compiler ros toolchain
#
# This Makefile will automatically use the cross-compiler toolchain
# installed as 'i386-ros-elf-*', if one exists.  If the host tools ('gcc',
# 'objdump', and so forth) compile for a 32-bit x86 ELF target, that will
# be detected as well.  If you have the right compiler toolchain installed
# using a different name, set GCCPREFIX explicitly in conf/env.mk

# try to infer the correct GCCPREFIX
ifndef GCCPREFIX
GCCPREFIX := $(shell if i386-ros-elf-objdump -i 2>&1 | grep '^elf32-i386$$' >/dev/null 2>&1; \
	then echo 'i386-ros-elf-'; \
	elif objdump -i 2>&1 | grep 'elf32-i386' >/dev/null 2>&1; \
	then echo ''; \
	else echo "***" 1>&2; \
	echo "*** Error: Couldn't find an i386-*-elf version of GCC/binutils." 1>&2; \
	echo "*** Is the directory with i386-ros-elf-gcc in your PATH?" 1>&2; \
	echo "*** If your i386-*-elf toolchain is installed with a command" 1>&2; \
	echo "*** prefix other than 'i386-ros-elf-', set your GCCPREFIX" 1>&2; \
	echo "*** environment variable to that prefix and run 'make' again." 1>&2; \
	echo "*** To turn off this error, run 'gmake GCCPREFIX= ...'." 1>&2; \
	echo "***" 1>&2; exit 1; fi)
endif

# Default programs for compilation
CC	    := ivycc --deputy --gcc=$(GCCPREFIX)gcc
AS	    := $(GCCPREFIX)as
AR	    := $(GCCPREFIX)ar
LD	    := $(GCCPREFIX)ld
OBJCOPY	:= $(GCCPREFIX)objcopy
OBJDUMP	:= $(GCCPREFIX)objdump
NM	    := $(GCCPREFIX)nm
PERL    := perl

# User defined constants passed on the command line 
TARGET_ARCH ?= i386

# Universal compiler flags
# -fno-builtin is required to avoid refs to undefined functions in the kernel.
# Only optimize to -O1 to discourage inlining, which complicates backtraces.
CFLAGS := $(CFLAGS) -D$(TARGET_ARCH)
CFLAGS += -O2 -pipe -MD -fno-builtin -fno-stack-protector -gstabs
CFLAGS += -Wall -Wno-format -Wno-unused -Wno-attributes
CFLAGS += -nostdinc -Igccinclude/$(TARGET_ARCH)

# Universal loader flags
LDFLAGS := -nostdlib

# GCC Library path 
GCC_LIB := $(shell $(CC) -print-libgcc-file-name)

# 64 Bit specific flags / definitions
ifeq ($(TARGET_ARCH),i386)
	ifeq ($(UNAME),x86_64)
		CFLAGS += -m32
		LDFLAGS += -melf_i386
		GCC_LIB = $(shell $(CC) -print-libgcc-file-name | sed 's/libgcc.a/32\/libgcc.a/')
	endif
endif

# List of directories that the */Makefrag makefile fragments will add to
OBJDIRS :=

# Make sure that 'all' is the first target
all: symlinks

kern/boot/Makefrag: symlinks

symlinks:
	-unlink kern/include/arch
	ln -s ../arch/$(TARGET_ARCH)/ kern/include/arch
	-unlink kern/src/arch
	ln -s ../arch/$(TARGET_ARCH)/ kern/src/arch
	-unlink kern/boot
	ln -s arch/$(TARGET_ARCH)/boot/ kern/boot

# Include Makefrags for subdirectories
include user/Makefrag
include kern/Makefrag

# Eliminate default suffix rules
.SUFFIXES:

# Delete target files if there is an error (or make is interrupted)
.DELETE_ON_ERROR:

# This magic automatically generates makefile dependencies
# for header files included from C source files we compile,
# and keeps those dependencies up-to-date every time we recompile.
# See 'mergedep.pl' for more information.
$(OBJDIR)/.deps: $(foreach dir, $(OBJDIRS), $(wildcard $(OBJDIR)/$(dir)/*.d))
	@mkdir -p $(@D)
	@$(PERL) scripts/mergedep.pl $@ $^

-include $(OBJDIR)/.deps

# For deleting the build
clean:
	rm -rf $(OBJDIR)

always:
	@:

.PHONY: all always clean

