#!/bin/fish

set -l d (date +%s)
echo {$d}.asm
cp crates/lexer/testdata/printf1.asm {$d}.asm
silicon {$d}.asm --output before-{$d}.png
cargo run -- {$d}.asm > {$d}-out.asm
silicon {$d}-out.asm --output after-{$d}.png
/bin/rm {$d}.asm {$d}-out.asm
