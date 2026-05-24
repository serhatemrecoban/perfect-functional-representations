import Lake
open Lake DSL

package «PerfectFunctionalRepresentations»

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib «PerfectFunctionalRepresentations» where
  roots := #[`PerfectFunctionalRepresentations]
  globs := #[Glob.one `PerfectFunctionalRepresentations, Glob.submodules `PerfectFunctionalRepresentations]
