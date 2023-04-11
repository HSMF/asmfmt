# FMT

The formatting rules of asmfmt

There are two kinds of formatting rules. Ones that operate locally and ones that operate on the
entire program.

## Formatters

### Local Formatters

- [IndentDirectives] Formats directives. Indents to `indent_by` and removes unnecessary spaces
- [FixCase] Fixes the case of keywords. By default changes case to lowercase, but this can be changed by the `uppercase_tokens` option
  Positions where the case is changed are: instructions, registers, and directive keywords

### Global Formatters

- [align_comments] Aligns comments such that they all appear on the same column
- [align_operands] Aligns the operands and instructions.
  Each label counts as a scope. Local labels (`.example`) don't reset the scope.
