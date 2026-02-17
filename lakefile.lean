import Lake
open Lake DSL

package «RBTT» where
  -- add any dependencies here if needed

@[default_target]
lean_lib «RBTT» where
  srcDir := "src"

lean_exe rbtt where
  root := `Main
  srcDir := "src"

lean_exe «check-budgets» where
  root := `RBTT.Scripts.CheckBudgets
  srcDir := "scripts"
  supportInterpreter := true
