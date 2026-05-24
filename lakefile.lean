import Lake
open Lake DSL

package «PerfectFunctionalRepresentations»

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

lean_lib «PerfectFunctionalRepresentations» where
  globs := #[Glob.submodules `PerfectFunctionalRepresentations]
