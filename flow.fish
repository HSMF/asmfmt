#!/bin/fish

set -l d (date +%s)
echo {$d}.asm
cp ./crates/fmt/testdata/printf2.asm {$d}.asm
silicon {$d}.asm --output before.png
cargo run -- {$d}.asm > {$d}-out.asm
silicon {$d}-out.asm --output after.png
/bin/rm {$d}.asm {$d}-out.asm
