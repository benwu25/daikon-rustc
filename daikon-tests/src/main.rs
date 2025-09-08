// add #[cfg(test)] later to be clear this crate only for testing
fn main() {
    // iterate through "./tests" and run rustc +daikon for files, cargo +daikon for multi-file tests in subdirectories
    let test_path = std::fs::canonicalize(std::path::Path::new("./tests")).unwrap();
    for entry in std::fs::read_dir(test_path.clone()).unwrap() {
        let entry = entry.unwrap();
        let path = std::fs::canonicalize(entry.path()).unwrap();
        println!("{}", path.display());
        if path.is_dir() {
            // set current_dir to canonicalize(<dir>) in Command and do cargo +daikon build
        } else {
            // set current_dir to canonicalize(test_path.clone()) and execute rustc +daikon
            let path_str = path.to_str().unwrap();
            if !path_str.ends_with("rs") {
                continue;
            } else {
                std::process::Command::new("rustc")
                    .arg("+daikon")
                    .arg(path_str)
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .current_dir(&test_path)
                    .spawn()
                    .expect("failed to execute daikon-rustc");
                // read <name>.pp to string, delete executable, decls/dtrace, and pp. do checks.
            }
        }
    }
}
