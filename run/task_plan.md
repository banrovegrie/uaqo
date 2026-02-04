# Task Plan: Formatting Compliance for src/*.md Files

## Objective
Make all markdown files in `src/` compliant with `src/tests/check-format.md` standards.

## Phases

### Phase 1: Repository Study
- [ ] Understand repository structure
- [ ] Review check-format.md criteria in detail
- [ ] Identify all .md files in src/

### Phase 2: File Inventory
- [ ] List all .md files to check
- [ ] Categorize by location (chapters/, experiments/, tests/, frontmatter/)

### Phase 3: Compliance Checks
- [ ] Check 1: ASCII-only characters
- [ ] Check 2: No horizontal rule separators
- [ ] Check 3: Math delimiters in markdown
- [ ] Check 4: LaTeX basics (delimiter balance, bare underscores, etc.)

### Phase 4: Fixes
- [ ] Fix non-ASCII characters
- [ ] Remove horizontal rules
- [ ] Add math delimiters where needed
- [ ] Fix LaTeX issues

### Phase 5: Verification
- [ ] Re-run all checks
- [ ] Document results

## Decisions Log
| Decision | Rationale | Date |
|----------|-----------|------|
| Use run/ folder for planning | User requested dedicated planning space | 2026-02-04 |

## Current Status
**COMPLETE** - All phases finished

### Final Verification Summary
- Total files scanned: 51 (in src/, excluding .lake/)
- Files with issues: 11
- Files fixed: 11
- Check 1 (ASCII): PASS
- Check 2 (Horizontal rules): PASS (none found)
- Check 3 (Math delimiters): PASS (fixed during Check 1)
- Check 4 (LaTeX basics): PASS
