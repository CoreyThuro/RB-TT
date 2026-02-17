# Recovery Guide

This repository now has a snapshot tag `snapshot-subst-20240215` that captures the state before the next round of edits. Use the following commands inside the repo root (WSL) to inspect or restore files.

## List available snapshots
```
git tag --list 'snapshot-*'
```

## Diff current work against the snapshot
```
git diff snapshot-subst-20240215
```

To diff a single file:
```
git diff snapshot-subst-20240215 -- path/to/file.lean
```

## Restore a file from the snapshot
```
git checkout snapshot-subst-20240215 -- path/to/file.lean
```

## Restore everything back to the snapshot (WARNING: overwrites local work)
```
git reset --hard snapshot-subst-20240215
```

Always double-check with `git status` before running destructive commands.
