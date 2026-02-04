# Formatting Check

## Purpose

Catch formatting issues in `.md` and `.tex` files before they become problems. These are mechanical checks that do not require judgment.

## Criteria

### 1. ASCII Only

All characters must be in ASCII range (0-127).

**Common violations:**
- Curly quotes: `"` `"` `'` `'` -> use `"` and `'`
- Em/en dashes: `—` `–` -> use `---` or `--`
- Accented letters: `e` -> use `\'e` in LaTeX
- Math symbols outside LaTeX: `×` `÷` `≤` `≥` -> use `\times`, `\leq` etc.
- Greek letters: `alpha` -> use `$\alpha$`

**Manual check:**
```bash
grep -rP '[^\x00-\x7F]' src/
```

### 2. No Horizontal Rule Separators

Markdown files should not use `---`, `***`, or `___` as section separators.

**Why:** I hate them.

**Manual check:**
```bash
grep -rn '^---$\|^***$\|^___$' src/*.md
```

**Exception:** YAML frontmatter delimiters at file start are acceptable.

### 3. LaTeX Basics

- Delimiter balance
- Bare `_` outside math mode -> use `\_` or `$H_0$`
- Bare `<` or `>` outside math -> use `$<$` or `\textless`
- Double spaces -> single space suffices
- Space before punctuation: `word .` -> `word.`

## Procedure

**Agent check:**

Read the file and scan for:
1. Non-ASCII bytes (report character and suggested replacement)
2. Horizontal rule lines (report line number)
3. LaTeX issues (report line and specific problem)

## Output Format

```
PASS: No formatting issues

FAIL: Formatting issues found
  - file.md:42: non-ASCII curly quote " -> use "
  - file.md:87: horizontal rule --- -> use heading or remove
  - file.tex:103: bare underscore H_0 -> use $H_0$
  - file.tex:156: unbalanced $ delimiter
```
