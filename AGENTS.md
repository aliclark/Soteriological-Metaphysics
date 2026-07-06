Task Worktree To Main Process

1. Work on a task branch or detached Codex worktree.
   If detached and the task is nontrivial, create a branch:
   git switch -c codex/<task-name>

2. Before finalizing, check whether main moved:
   git rev-parse HEAD
   git rev-parse main
   git merge-base HEAD main
   git log --oneline HEAD..main

3. If main has moved, merge it into the task worktree:
   git merge main

4. Do a semantic sanity check, not just a conflict check:
   - Read the commits from main that were merged:
     git log --oneline <old-base>..main
     git diff --stat <old-base>..main
   - Inspect touched files that overlap conceptually with this task.
   - Look for naming, namespace, theorem-shape, import, prose-register, or API convention changes.
   - Apply any implications from main to the current work too.
     Example: if main renamed a convention, reword/rename the new task code accordingly.
   - Search for stale terms if relevant:
     rg "OldName|old_phrase|old_namespace"

5. Re-run the project checks:
   lake build
   Optional targeted checks:
   rg -n "sorry|admit|axiom" <new-or-touched-lean-files>
   #print axioms <important_new_theorem>

6. Commit the completed task on the task branch:
   git status --short
   git add <changed-files>
   git commit -m "<task summary>"

7. At this point, ask for final Review and merge approval from the user, and wait here for response.

8. If Approved, merge into main from the real main worktree:
   cd <main-worktree>
   git status --short
   git switch main
   git merge <task-branch>

9. Verify main after merge:
   lake build

10. If clean, remove the temporary branch and worktree:
   git branch -d <task-branch>
   git worktree remove <task-worktree-path>
   git worktree prune