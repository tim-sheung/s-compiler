mod parser;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    pub fn alert(s: &str);
}

#[wasm_bindgen]
pub fn compile(code: &str) -> String {
    let mut parser = parser::Parser::new();
    parser.parse_program(code)
}
