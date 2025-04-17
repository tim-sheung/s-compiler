mod parser;

/**
This is a program that compiles s-expression
**/

fn main() {
    let code = r#"(? (lt 1 2) "yes" "no")"#;
    let mut parser = parser::Parser::new();
    let result = parser.parse_program(code);
    println!("Result: {}", result);
}
