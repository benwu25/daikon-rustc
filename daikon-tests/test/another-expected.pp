struct X {
    pub a: i32,
}

fn main() {
    let mut __daikon_nonce = 0;
    let mut __unwrap_nonce = NONCE_COUNTER.lock().unwrap();
    __daikon_nonce = *__unwrap_nonce;
    *__unwrap_nonce += 1;
    drop(__unwrap_nonce);
    dtrace_entry("main:::ENTER", __daikon_nonce);
    dtrace_newline();
    let x = 6;
    boo(&&x);
    let y = X { a: 6 };
    moon(&&y);
    fn nest(q: &X) {
        let mut __daikon_nonce = 0;
        let mut __unwrap_nonce = NONCE_COUNTER.lock().unwrap();
        __daikon_nonce = *__unwrap_nonce;
        *__unwrap_nonce += 1;
        drop(__unwrap_nonce);
        dtrace_entry("nest:::ENTER", __daikon_nonce);
        dtrace_print_pointer(q as *const _ as usize, String::from("q"));
        q.dtrace_print_fields(3, String::from("q"));
        dtrace_newline();
        drop(q);
        dtrace_exit("nest:::EXIT1", __daikon_nonce);
        dtrace_print_pointer(q as *const _ as usize, String::from("q"));
        q.dtrace_print_fields(3, String::from("q"));
        dtrace_newline();
        return;
    }
    nest(&y);
    println!("{}", y.a);
    dtrace_exit("main:::EXIT1", __daikon_nonce);
    dtrace_newline();
    return;
}

fn boo<'a, 'b>(a: &'a &'b i32) {
    let mut __daikon_nonce = 0;
    let mut __unwrap_nonce = NONCE_COUNTER.lock().unwrap();
    __daikon_nonce = *__unwrap_nonce;
    *__unwrap_nonce += 1;
    drop(__unwrap_nonce);
    dtrace_entry("boo:::ENTER", __daikon_nonce);
    dtrace_print_prim::<i32>(i32::from_str(&a.to_string()).expect("Ok"),
        String::from("a"));
    dtrace_newline();
    println!("{}", **a);
    dtrace_exit("boo:::EXIT1", __daikon_nonce);
    dtrace_print_prim::<i32>(i32::from_str(&a.to_string()).expect("Ok"),
        String::from("a"));
    dtrace_newline();
    return;
}

fn moon<'a, 'b>(x: &'a &'b X) {
    let mut __daikon_nonce = 0;
    let mut __unwrap_nonce = NONCE_COUNTER.lock().unwrap();
    __daikon_nonce = *__unwrap_nonce;
    *__unwrap_nonce += 1;
    drop(__unwrap_nonce);
    dtrace_entry("moon:::ENTER", __daikon_nonce);
    dtrace_print_pointer(x as *const _ as usize, String::from("x"));
    x.dtrace_print_fields(3, String::from("x"));
    dtrace_newline();
    println!("{}", x.a);
    dtrace_exit("moon:::EXIT1", __daikon_nonce);
    dtrace_print_pointer(x as *const _ as usize, String::from("x"));
    x.dtrace_print_fields(3, String::from("x"));
    dtrace_newline();
    return;
}

fn dark_moon(x: std::primitive::i32) {
    let mut __daikon_nonce = 0;
    let mut __unwrap_nonce = NONCE_COUNTER.lock().unwrap();
    __daikon_nonce = *__unwrap_nonce;
    *__unwrap_nonce += 1;
    drop(__unwrap_nonce);
    dtrace_entry("dark_moon:::ENTER", __daikon_nonce);
    dtrace_print_prim::<i32>(x, String::from("x"));
    dtrace_newline();
    dtrace_exit("dark_moon:::EXIT1", __daikon_nonce);
    dtrace_print_prim::<i32>(x, String::from("x"));
    dtrace_newline();
    return;
}
