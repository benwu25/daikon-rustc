To get `daikon-rustc`,

 * Build the compiler.
     * `./x setup`
     * `./x build library/std`
 * Set up daikon as a toolchain with the stage 1 build.
     * `rustup toolchain link daikon build/<platform>/stage1`
 * Produce dtrace and decls files in one command via `cargo +daikon run`,
   or instrument with rustc via `rustc +daikon foo.rs`, and run to produce trace data.
