struct X { pub a: i32 }

fn main() {

    let x = 6;
    boo(&&x);

    let y = X { a: 6 };
    moon(&&y);

    fn nest(q: &X) { drop(q); }

    nest(&y);

    println!("{}", y.a);

}

fn boo<'a, 'b>(a: &'a &'b i32) { println!("{}", **a); }

fn moon<'a, 'b>(x: &'a &'b X) { println!("{}", x.a); }

fn dark_moon(x: std::primitive::i32) {}
