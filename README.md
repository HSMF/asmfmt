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

## In Editors

### Neovim

The recommended way of including asmfmt in Neovim is by using [null-ls](https://github.com/jose-elias-alvarez/null-ls.nvim)

```lua
local asmfmt = {
    method = require("null-ls").methods.FORMATTING,
    filetypes = { "asm" },
    generator = null_ls.formatter({
        command = "asmfmt",
        to_stdin = true,
    }),
}

require("null-ls").setup({
    sources = {
        asmfmt,
        -- other sources...
    }
})
```

### VSCode

Use [this extension](./asmfmt-vsc/)

### Others

- if your editor is not supported and you know how to support it, please submit a PR. Thanks!
