// Proper primitive types
// i8, i16, i32, i64, i128 and isize
// u8, u16, u32, u64, u128 and usize
// f32, f64
// char
// bool
// () -- why is this possible for parameters :/

// Other types for Daikon to munch
// str
// String
// Vec
// more to come?
pub(crate) static I8: &str = "i8";
pub(crate) static I16: &str = "i16";
pub(crate) static I32: &str = "i32";
pub(crate) static I64: &str = "i64";
pub(crate) static I128: &str = "i128";
pub(crate) static ISIZE: &str = "isize";

pub(crate) static U8: &str = "u8";
pub(crate) static U16: &str = "u16";
pub(crate) static U32: &str = "u32";
pub(crate) static U64: &str = "u64";
pub(crate) static U128: &str = "u128";
pub(crate) static USIZE: &str = "usize";

pub(crate) static F32: &str = "f32";
pub(crate) static F64: &str = "f64";

pub(crate) static CHAR: &str = "char";
pub(crate) static BOOL: &str = "bool";
pub(crate) static UNIT: &str = "()";
pub(crate) static STR: &str = "str";
pub(crate) static STRING: &str = "String";
pub(crate) static VEC: &str = "Vec";

// placeholders are between the strs

pub(crate) static DTRACE_ENTRY: [&str; 3] = ["fn __skip() { dtrace_entry(\"",
                                             ":::ENTER\", *",
                                             "_COUNTER.lock().unwrap()); }"];
pub(crate) fn build_entry(ppt_name: String) -> String {
    let mut res = String::from(DTRACE_ENTRY[0]);
    res.push_str(&ppt_name);
    res.push_str(DTRACE_ENTRY[1]);
    res.push_str(&ppt_name.to_uppercase());
    res.push_str(DTRACE_ENTRY[2]);
    res
}

pub(crate) static DTRACE_EXIT: [&str; 4] = ["fn __skip() { dtrace_exit(\"",
                                           ":::EXIT",
                                           "\", *",
                                           "_COUNTER.lock().unwrap()); }"];
pub(crate) fn build_exit(ppt_name: String, exit_counter: usize) -> String {
    let mut res = String::from(DTRACE_EXIT[0]);
    res.push_str(&ppt_name);
    res.push_str(DTRACE_EXIT[1]);
    res.push_str(&exit_counter.to_string());
    res.push_str(DTRACE_EXIT[2]);
    res.push_str(&ppt_name.to_uppercase());
    res.push_str(DTRACE_EXIT[3]);
    res
}

pub(crate) static INC: [&str; 2] = ["fn __skip() { *",
                                    "_COUNTER.lock().unwrap() += 1; }"];
pub(crate) fn build_inc(ppt_name: String) -> String {
    let mut res = String::from(INC[0]);
    res.push_str(&ppt_name.to_uppercase());
    res.push_str(INC[1]);
    res
}

pub(crate) static DTRACE_PRIM: [&str; 4] = ["fn __skip() { dtrace_print_prim::<",
                                            ">(",
                                            ", String::from(\"",
                                            "\")); }"];
pub(crate) fn build_prim(p_type: String, var_name: String) -> String {
    let mut res = String::from(DTRACE_PRIM[0]);
    res.push_str(&p_type);
    res.push_str(DTRACE_PRIM[1]);
    res.push_str(&var_name);
    res.push_str(DTRACE_PRIM[2]);
    res.push_str(&var_name);
    res.push_str(DTRACE_PRIM[3]);
    res
}

pub(crate) static DTRACE_PRIM_STRUCT: [&str; 4] = ["dtrace_print_prim::<",
                                                  ">(self.",
                                                  ", format!(\"{}{}\", prefix, \".",
                                                  "\"));"];
pub(crate) fn build_field_prim(p_type: String, field_name: String) -> String {
    let mut res = String::from(DTRACE_PRIM_STRUCT[0]);
    res.push_str(&p_type);
    res.push_str(DTRACE_PRIM_STRUCT[1]);
    res.push_str(&field_name);
    res.push_str(DTRACE_PRIM_STRUCT[2]);
    res.push_str(&field_name);
    res.push_str(DTRACE_PRIM_STRUCT[3]);
    res
}

pub(crate) static DTRACE_USERDEF: [&str; 6] = ["fn __skip() { dtrace_print_pointer(",
                                               " as *const _ as usize, String::from(\"",
                                               "\"));\n",
                                               ".dtrace_print_fields(",
                                               ", String::from(\"",
                                               "\")); }"];
pub(crate) fn build_userdef(var_name: String, depth_arg: i32) -> String {
    let mut res = String::from(DTRACE_USERDEF[0]);
    res.push_str(&var_name);
    res.push_str(DTRACE_USERDEF[1]);
    res.push_str(&var_name);
    res.push_str(DTRACE_USERDEF[2]);
    res.push_str(&var_name);
    res.push_str(DTRACE_USERDEF[3]);
    res.push_str(&String::from(depth_arg.to_string()));
    res.push_str(DTRACE_USERDEF[4]);
    res.push_str(&var_name);
    res.push_str(DTRACE_USERDEF[5]);
    res
}

pub(crate) static DTRACE_USERDEF_STRUCT: [&str; 5] = ["dtrace_print_pointer(self.",
                                                      " as *const _ as usize, format!(\"{}{}\", prefix, \".",
                                                      "\"));\nself.",
                                                      ".dtrace_print_fields(depth - 1, format!(\"{}{}\", prefix, \".",
                                                      "\"));"];
pub(crate) fn build_field_userdef(field_name: String) -> String {
    let mut res = String::from(DTRACE_USERDEF_STRUCT[0]);
    res.push_str(&field_name);
    res.push_str(DTRACE_USERDEF_STRUCT[1]);
    res.push_str(&field_name);
    res.push_str(DTRACE_USERDEF_STRUCT[2]);
    res.push_str(&field_name);
    res.push_str(DTRACE_USERDEF_STRUCT[3]);
    res.push_str(&field_name);
    res.push_str(DTRACE_USERDEF_STRUCT[4]);
    res
}

pub(crate) static LET_RET: [&str; 2] = ["fn __skip() { let ret = ",
                                        "; }"];
pub(crate) fn build_let_ret(expr: String) -> String {
    let mut res = String::from(LET_RET[0]);
    res.push_str(&expr);
    res.push_str(LET_RET[1]);
    res
}

pub(crate) static RET: [&str; 1] = ["fn __skip() { return ret; }"];
pub(crate) fn build_ret() -> String {
    String::from(RET[0])
}

// you have to delete this?
// make this an array with DTRACE_PRINT_FIELDS_EPILOGUE...
pub(crate) static DTRACE_PRINT_FIELDS_PROLOGUE: &str = "impl __skip { pub fn dtrace_print_fields(&self, depth: i32, prefix: String) { if depth == 0 { return; } ";
pub(crate) fn dtrace_print_fields_prologue() -> String {
    String::from(DTRACE_PRINT_FIELDS_PROLOGUE)
}

pub(crate) static DTRACE_PRINT_FIELDS_EPILOGUE: &str = "} } struct __skip{}"; // maybe can avoid deleting it, but still bad
pub(crate) fn dtrace_print_fields_epilogue() -> String {
    String::from(DTRACE_PRINT_FIELDS_EPILOGUE)
}

pub(crate) static BUILD_A_IMPL_BLOCK: &str = "impl __skip {}";
pub(crate) fn base_impl() -> String {
    String::from(BUILD_A_IMPL_BLOCK)
}

pub(crate) static FABRICATE_TYPE_FOR_IMPL: [&str; 3] = ["fn __skip() -> ",
                                                        " {}\nstruct ",
                                                        "{}"];
pub(crate) fn build_phony_ret(struct_name: String) -> String {
    let mut res = String::from(FABRICATE_TYPE_FOR_IMPL[0]);
    res.push_str(&struct_name);
    res.push_str(FABRICATE_TYPE_FOR_IMPL[1]);
    res.push_str(&struct_name);
    res.push_str(FABRICATE_TYPE_FOR_IMPL[2]);
    res
}

pub(crate) static VOID_RETURN: &str = "fn __skip() { return; }";
pub(crate) fn build_void_return() -> String {
    String::from(VOID_RETURN)
}

pub(crate) static NONCE_COUNTER: [&str; 2] = ["static ",
                                              "_COUNTER: LazyLock<Mutex<u32>> = LazyLock::new(|| Mutex::new(1));"];
pub(crate) fn build_nonce_counter(ppt_name: String) -> String {
    let mut res = String::from(NONCE_COUNTER[0]);
    res.push_str(&ppt_name.to_uppercase());
    res.push_str(NONCE_COUNTER[1]);
    res
}

pub(crate) static IMPORTS: &str = "use std::fs::File;\nuse std::io::prelude::*;\nuse std::sync::{LazyLock, Mutex};\n";
pub(crate) fn build_imports() -> String {
    String::from(IMPORTS)
}

pub(crate) static DAIKON_LIB: &str =
"pub fn dtrace_print_pointer_arr<T>(v: &[&T], var_name: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", var_name).ok();
    let mut arr = String::from(\"[\");
    let mut i = 0;
    while i < v.len() - 1 {
        arr.push_str(&format!(\"0x{:x} \", v[i] as *const _ as usize));
        i += 1;
    }
    if v.len() > 0 {
        arr.push_str(&format!(\"0x{:x}\", v[v.len() - 1] as *const _ as usize));
    }
    arr.push_str(\"]\");
    writeln!(&mut traces, \"{}\", arr).ok();
    writeln!(&mut traces, \"0\").ok();
}

pub fn dtrace_print_pointer_vec<T>(v: &Vec<&T>, var_name: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", var_name).ok();
    let mut arr = String::from(\"[\");
    let mut i = 0;
    while i < v.len() - 1 {
        arr.push_str(&format!(\"0x{:x} \", v[i] as *const _ as usize));
        i += 1;
    }
    if v.len() > 0 {
        arr.push_str(&format!(\"0x{:x}\", v[v.len() - 1] as *const _ as usize));
    }
    arr.push_str(\"]\");
    writeln!(&mut traces, \"{}\", arr).ok();
    writeln!(&mut traces, \"0\").ok();
}

// T must implement Display trait
fn dtrace_print_prim_arr<T: std::fmt::Display>(v: &[T], prefix: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", format!(\"{}{}\", prefix, \"[..]\")).ok();
    let mut arr = String::from(\"[\");
    let mut i = 0;
    while i < v.len() - 1 {
        arr.push_str(&format!(\"{} \", v[i]));
        i += 1;
    }
    if v.len() > 0 {
        arr.push_str(&format!(\"{}\", v[v.len() - 1]));
    }
    arr.push_str(\"]\");
    writeln!(&mut traces, \"{}\", arr).ok();
    writeln!(&mut traces, \"0\").ok();
}

fn dtrace_print_str(v: &str, var_name: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", var_name).ok();
    writeln!(&mut traces, \"{}\", v).ok();
    writeln!(&mut traces, \"0\").ok();
}

// T must implement Display trait
fn dtrace_print_prim<T: std::fmt::Display>(v: T, var_name: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", var_name).ok();
    writeln!(&mut traces, \"{}\", v).ok();
    writeln!(&mut traces, \"0\").ok();
}

fn dtrace_print_pointer(v: usize, var_name: String) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", var_name).ok();
    writeln!(&mut traces, \"0x{:x}\", v).ok();
    writeln!(&mut traces, \"0\").ok();
}

fn dtrace_entry_no_nonce(ppt_name: &str) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", ppt_name).ok();
}

fn dtrace_exit_no_nonce(ppt_name: &str) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", ppt_name).ok();
}

fn dtrace_entry(ppt_name: &str, nonce: u32) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(&mut traces, \"{}\", ppt_name).ok();
    writeln!(&mut traces, \"this_invocation_nonce\").ok();
    writeln!(&mut traces, \"{}\", nonce).ok();
}

fn dtrace_exit(ppt_name: &str, nonce: u32) {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(traces, \"{}\", ppt_name).ok();
    writeln!(traces, \"this_invocation_nonce\").ok();
    writeln!(traces, \"{}\", nonce).ok();
}

fn dtrace_newline() {
    let mut traces = match File::options().append(true).open(\"main.dtrace\") {
        Err(why) => panic!(\"Daikon couldn't open file, {}\", why),
        Ok(traces) => traces,
    };
    writeln!(traces, \"\").ok();
}";

pub(crate) fn daikon_lib() -> String {
    String::from(DAIKON_LIB)
}