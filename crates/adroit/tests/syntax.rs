use adroit::Module;

fn syntax(src: &str, out: &str) {
    let module: Module = src.parse().unwrap();
    assert_eq!(format!("{module}"), out);
}

#[test]
fn test_empty() {
    syntax(
        include_str!("in/empty.adroit"),
        include_str!("out/empty.adroit"),
    )
}

#[test]
fn test_sub() {
    syntax(
        include_str!("in/sub.adroit"),
        include_str!("out/sub.adroit"),
    )
}

#[test]
fn test_loop() {
    syntax(
        include_str!("in/loop.adroit"),
        include_str!("out/loop.adroit"),
    )
}

#[test]
fn test_struct() {
    syntax(
        include_str!("in/struct.adroit"),
        include_str!("out/struct.adroit"),
    )
}

#[test]
fn test_enum() {
    syntax(
        include_str!("in/enum.adroit"),
        include_str!("out/enum.adroit"),
    )
}
