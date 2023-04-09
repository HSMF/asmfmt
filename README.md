# asmfmt

Formatter for NASM-Style Assembly

## Installation

You need to have a more or less current rust toolchain.

```bash
cargo install --path .
```

## Usage

run `asmfmt [FILE]`. If FILE is not specified, asmfmt reads from stdin.

```bash
> cat program.asm
global _start

_start: ; entry point
    mov eax, 5
st:
    ret
> asmfmt program.asm # formats program.asm
```
