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

pub(crate) static DTRACE_ENTRY: [&str; 3] = ["fn main() { dtrace_entry(\"",
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

pub(crate) static DTRACE_EXIT: [&str; 4] = ["fn main() { dtrace_exit(\"",
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

pub(crate) static INC: [&str; 2] = ["fn main() { *",
                                    "_COUNTER.lock().unwrap() += 1; }"];
pub(crate) fn build_inc(ppt_name: String) -> String {
    let mut res = String::from(INC[0]);
    res.push_str(&ppt_name);
    res.push_str(INC[1]);
    res
}

pub(crate) static DTRACE_PRIM: [&str; 4] = ["fn main() { dtrace_print_prim::<",
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

pub(crate) static DTRACE_USERDEF: [&str; 6] = ["fn main() { dtrace_print_pointer(",
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

pub(crate) static LET_RET: [&str; 2] = ["fn main() { let ret = ",
                                        "; }"];
pub(crate) fn build_let_ret(expr: String) -> String {
    let mut res = String::from(LET_RET[0]);
    res.push_str(&expr);
    res.push_str(LET_RET[1]);
    res
}

pub(crate) static RET: [&str; 1] = ["fn main() { return ret; }"];
pub(crate) fn build_ret() -> String {
    String::from(RET[0])
}