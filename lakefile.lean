import Lake
open Lake DSL
open System (FilePath)

package «lean-sys» where
  version := v!"0.1.0"

target lean_sys_shim_o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "lean_sys_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "lean_sys_shim.c"
  let leanIncludeDir ← getLeanIncludeDir
  buildO oFile srcJob #["-I", leanIncludeDir.toString] #["-O3", "-fPIC"] "cc"

extern_lib liblean_sys_shim pkg := do
  let shimO ← lean_sys_shim_o.fetch
  let name := nameToStaticLib "lean_sys_shim"
  buildStaticLib (pkg.staticLibDir / name) #[shimO]

@[default_target]
lean_lib «LeanSys» where
  roots := #[`LeanSys]
  precompileModules := false

@[default_target]
lean_exe «lean-sys-core» where
  root := `LeanSys.Core
  supportInterpreter := false
