use std::collections::HashMap;
use std::collections::VecDeque;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Atom(String),
    List(Vec<Node>),
}

pub struct Parser {
    symbol_tables: Vec<HashMap<String, Node>>,
    loop_break: bool,
    loop_continue: bool,
    return_value: Option<String>,
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            symbol_tables: Vec::new(),
            loop_break: false,
            loop_continue: false,
            return_value: None,
        }
    }

    pub fn tokenize(&mut self, code: String) -> VecDeque<String> {
        let mut vec = VecDeque::new();
        let mut i = 0;
        let supported_symbols = vec!['+', '-', '*', '/', '?'];
        while i < code.len() {
            let mut token = String::new();
            let ch = code.chars().nth(i).unwrap();
            if ch.is_whitespace() {
                i += 1;
                continue;
            } else if ch == '(' || ch == ')' || supported_symbols.contains(&ch) {
                token.push(ch);
                i += 1;
            } else if ch == '"' {
                token.push(ch);
                i += 1;
                while i < code.len() {
                    let ch = code.chars().nth(i).unwrap();
                    token.push(ch);
                    i += 1;
                    if ch == '"' {
                        break;
                    }
                }
            } else if ch.is_alphanumeric() {
                while i < code.len() {
                    let ch = code.chars().nth(i).unwrap();
                    if ch.is_alphanumeric() {
                        token.push(ch);
                        i += 1;
                    } else {
                        break;
                    }
                }
            } else {
                panic!("Unexpected character: {}", ch);
            }
            vec.push_back(token);
        }
        vec
    }

    pub fn parse_program(&mut self, code: &str) -> String {
        let expression = format!("(do {})", code);
        let mut tokens = self.tokenize(expression);
        let node = self.parse_expression(&mut tokens);
        self.eval_node(node)
    }

    pub fn parse_expression(&mut self, tokens: &mut VecDeque<String>) -> Node {
        // consume "("
        if tokens.front().unwrap() != "(" {
            panic!("Syntax error");
        }
        tokens.pop_front();
        let mut vec = Vec::new();
        while !tokens.is_empty() {
            let token = tokens.front().unwrap();
            match token.as_str() {
                "(" => {
                    let expression = self.parse_expression(tokens);
                    vec.push(expression);
                }
                ")" => {
                    // consume ")"
                    tokens.pop_front();
                    return Node::List(vec);
                }
                _ => {
                    // consume token
                    let val = tokens.pop_front().unwrap();
                    vec.push(Node::Atom(val));
                }
            }
        }
        panic!("Unmatched parentheses");
    }

    pub fn eval_node(&mut self, node: Node) -> String {
        if self.loop_break || self.loop_continue {
            return "null".to_string();
        }
        if self.return_value.is_some() {
            return self.return_value.clone().unwrap();
        }
        match node {
            Node::Atom(atom) => self.eval_atom(atom),
            Node::List(list) => self.eval_list(list),
        }
    }

    pub fn eval_atom(&mut self, atom: String) -> String {
        if self.is_primitive_type(&atom) {
            atom
        } else {
            let symbol_table = self
                .symbol_tables
                .iter()
                .rfind(|table| table.contains_key(&atom))
                .unwrap();
            let node = symbol_table.get(&atom).unwrap();
            match node {
                Node::Atom(val) => val.clone(),
                Node::List(_) => panic!("Cannot evaluate a list as an atom"),
            }
        }
    }

    pub fn eval_list(&mut self, list: Vec<Node>) -> String {
        let atom = match list[0].clone() {
            Node::Atom(val) => val,
            _ => panic!("The first element of a list must be an Atom"),
        };
        if list.len() == 1 && !self.is_keyword(&atom) {
            return self.eval_atom(atom);
        }
        match atom.as_str() {
            "+" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                (operand1 + operand2).to_string()
            }
            "-" => {
                let num_operands = list.len() - 1;
                if num_operands == 1 {
                    let operand = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                    (-operand).to_string()
                } else if num_operands == 2 {
                    let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                    let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                    (operand1 - operand2).to_string()
                } else {
                    panic!("Invalid number of operands for '-' operator");
                }
            }
            "*" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                (operand1 * operand2).to_string()
            }
            "/" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                (operand1 / operand2).to_string()
            }
            "lt" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                (operand1 < operand2).to_string()
            }
            "gt" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<i32>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<i32>().unwrap();
                (operand1 > operand2).to_string()
            }
            "eq" => {
                let operand1 = self.eval_node(list[1].clone());
                let operand2 = self.eval_node(list[2].clone());
                (operand1 == operand2).to_string()
            }
            "ne" => {
                let operand1 = self.eval_node(list[1].clone());
                let operand2 = self.eval_node(list[2].clone());
                (operand1 != operand2).to_string()
            }
            "and" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<bool>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<bool>().unwrap();
                (operand1 & operand2).to_string()
            }
            "or" => {
                let operand1 = self.eval_node(list[1].clone()).parse::<bool>().unwrap();
                let operand2 = self.eval_node(list[2].clone()).parse::<bool>().unwrap();
                (operand1 | operand2).to_string()
            }
            "not" => {
                let operand = self.eval_node(list[1].clone()).parse::<bool>().unwrap();
                (!operand).to_string()
            }
            "?" => {
                let condition = self.eval_node(list[1].clone()).parse::<bool>().unwrap();
                let true_branch = self.eval_node(list[2].clone());
                let false_branch = self.eval_node(list[3].clone());
                if condition {
                    true_branch.clone()
                } else {
                    false_branch.clone()
                }
            }
            "do" => {
                self.symbol_tables.push(HashMap::new());
                let mut val = String::from("");
                for i in 1..list.len() {
                    val = self.eval_node(list[i].clone());
                }
                // remove the symbol table
                self.symbol_tables.pop();
                val
            }
            "var" => {
                let var = match list[1].clone() {
                    Node::Atom(val) => val,
                    _ => panic!("Variable name must be an Atom"),
                };
                let val = self.eval_node(list[2].clone());
                let table = self.symbol_tables.last_mut().unwrap();
                table.insert(var, Node::Atom(val.clone()));
                val
            }
            "set" => {
                let var = match list[1].clone() {
                    Node::Atom(val) => val,
                    _ => panic!("Variable name must be an Atom"),
                };
                let val = self.eval_node(list[2].clone());
                for table in self.symbol_tables.iter_mut().rev() {
                    if table.contains_key(&var) {
                        table.insert(var, Node::Atom(val.clone()));
                        return val;
                    }
                }
                panic!("Variable not found: {}", var);
            }
            "if" => {
                let condition = self.eval_node(list[1].clone()).parse::<bool>().unwrap();
                let true_node = list[2].clone();
                if condition {
                    self.eval_node(true_node)
                } else if list.len() == 4 {
                    let false_node = list[3].clone();
                    self.eval_node(false_node)
                } else {
                    "null".to_string()
                }
            }
            "loop" => {
                let condition_node = list[1].clone();
                while self
                    .eval_node(condition_node.clone())
                    .parse::<bool>()
                    .unwrap()
                {
                    let body_node = list[2].clone();
                    self.eval_node(body_node);
                    if self.loop_break {
                        self.loop_break = false;
                        break;
                    }
                    if self.loop_continue {
                        self.loop_continue = false;
                        continue;
                    }
                }
                "null".to_string()
            }
            "break" => {
                self.loop_break = true;
                "null".to_string()
            }
            "continue" => {
                self.loop_continue = true;
                "null".to_string()
            }
            "def" => {
                let func = match list[1].clone() {
                    Node::Atom(val) => val,
                    _ => panic!("Function name must be an Atom"),
                };
                let args = match list[2].clone() {
                    Node::List(val) => val,
                    _ => panic!("Function arguments must be a List"),
                };
                let body = match list[3].clone() {
                    Node::List(val) => val,
                    _ => panic!("Function body must be a List"),
                };
                // insert at the first symbol table
                let table = self.symbol_tables.first_mut().unwrap();
                let node = Node::List(vec![Node::List(args), Node::List(body)]);
                table.insert(func, node);
                "null".to_string()
            }
            "call" => {
                let func = match &list[1] {
                    Node::Atom(val) => val,
                    _ => panic!("Function name must be an Atom"),
                };
                let args = &list[2..];
                let node = self.symbol_tables.first().unwrap().get(func).unwrap();
                let (args_node, body_node) = match node {
                    Node::List(val) => (val[0].clone(), val[1].clone()),
                    _ => panic!("Function definition must be a List"),
                };
                let arg_names: Vec<String> = match args_node {
                    Node::List(val) => val
                        .iter()
                        .map(|arg| match arg {
                            Node::Atom(val) => val.clone(),
                            _ => panic!("Function argument name must be an Atom"),
                        })
                        .collect(),
                    _ => panic!("Function arguments must be a List"),
                };
                if args.len() != arg_names.len() {
                    panic!("Function call has different number of arguments than definition");
                }
                // create a new symbol table and insert the arguments
                let mut table = HashMap::new();
                println!("Calling function: {}", func);
                for (i, arg) in args.iter().enumerate() {
                    let arg_name = &arg_names[i];
                    let arg_value = self.eval_node(arg.clone());
                    println!("Argument: {} = {}", arg_name, arg_value);
                    table.insert(arg_name.clone(), Node::Atom(arg_value));
                }
                self.symbol_tables.push(table);
                let val = self.eval_node(body_node);
                // remove the symbol table
                self.symbol_tables.pop();
                self.return_value = None;
                val
            }
            "return" => match list.len() {
                1 => "null".to_string(),
                2 => {
                    let val = self.eval_node(list[1].clone());
                    self.return_value = Some(val.clone());
                    val
                }
                _ => panic!("Invalid number of arguments for 'return' operator"),
            },
            _ => {
                panic!("Unsupported operator: {}", atom);
            }
        }
    }

    fn is_primitive_type(&self, value: &str) -> bool {
        (value.starts_with('"') && value.ends_with('"'))
            || value.parse::<i32>().is_ok()
            || value == "true"
            || value == "false"
            || value == "null"
    }

    fn is_keyword(&self, value: &str) -> bool {
        match value {
            "if" | "do" | "var" | "set" | "loop" | "break" | "continue" | "def" | "call" => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() {
        let mut parser = Parser::new();
        let code = r#"(? (lt 1 2) "yes" "no")"#;
        let tokens = parser.tokenize(code.to_string());
        assert_eq!(tokens.len(), 10);
        assert_eq!(tokens[0], "(");
        assert_eq!(tokens[1], "?");
        assert_eq!(tokens[2], "(");
        assert_eq!(tokens[3], "lt");
        assert_eq!(tokens[4], "1");
        assert_eq!(tokens[5], "2");
        assert_eq!(tokens[6], ")");
        assert_eq!(tokens[7], "\"yes\"");
        assert_eq!(tokens[8], "\"no\"");
        assert_eq!(tokens[9], ")");
    }

    #[test]
    fn test_parse_program() {
        let mut parser = Parser::new();
        let code = r#"
        (? (lt 1 2) "yes" "no")
        (do (+ 1 2) (* 3 4))
        (eq 1 1)
        (ne 1 2)
        "#;
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_expression() {
        let mut parser = Parser::new();
        let code = r#"
        (? (lt 1 2) "yes" "no")
        "#;
        let mut tokens = parser.tokenize(code.to_string());
        let node = parser.parse_expression(&mut tokens);
        assert_eq!(
            node,
            Node::List(vec![
                Node::Atom("?".to_string()),
                Node::List(vec![
                    Node::Atom("lt".to_string()),
                    Node::Atom("1".to_string()),
                    Node::Atom("2".to_string()),
                ]),
                Node::Atom("\"yes\"".to_string()),
                Node::Atom("\"no\"".to_string()),
            ])
        );
    }

    #[test]
    fn test_parse_add() {
        let mut parser = Parser::new();
        let code = "(+ 1 (+ 2 3))";
        assert_eq!(parser.parse_program(code), "6");
    }

    #[test]
    fn test_parse_sub() {
        let mut parser = Parser::new();
        let code = "(- 5 (- 2 1))";
        assert_eq!(parser.parse_program(code), "4");
    }

    #[test]
    fn test_parse_mul() {
        let mut parser = Parser::new();
        let code = "(* 3 (* 2 2))";
        assert_eq!(parser.parse_program(code), "12");
    }

    #[test]
    fn test_parse_div() {
        let mut parser = Parser::new();
        let code = "(/ 8 (/ 4 2))";
        assert_eq!(parser.parse_program(code), "4");
    }

    #[test]
    fn test_parse_eq() {
        let mut parser = Parser::new();
        let code = "(eq 1 1)";
        assert_eq!(parser.parse_program(code), "true");
        let code = r#"(eq "peter" "peter")"#;
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_ne() {
        let mut parser = Parser::new();
        let code = "(ne 1 2)";
        assert_eq!(parser.parse_program(code), "true");
        let code = r#"(ne "peter" "david")"#;
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_lt() {
        let mut parser = Parser::new();
        let code = "(lt 1 2)";
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_gt() {
        let mut parser = Parser::new();
        let code = "(gt 2 1)";
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_and() {
        let mut parser = Parser::new();
        let code = "(and true false)";
        assert_eq!(parser.parse_program(code), "false");
        let code = "(and true true)";
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_or() {
        let mut parser = Parser::new();
        let code = "(or true false)";
        assert_eq!(parser.parse_program(code), "true");
        let code = "(or false false)";
        assert_eq!(parser.parse_program(code), "false");
    }

    #[test]
    fn test_parse_not() {
        let mut parser = Parser::new();
        let code = "(not true)";
        assert_eq!(parser.parse_program(code), "false");
        let code = "(not false)";
        assert_eq!(parser.parse_program(code), "true");
    }

    #[test]
    fn test_parse_cond() {
        let mut parser = Parser::new();
        let code = "(? (eq 1 1) \"yes\" \"no\")";
        assert_eq!(parser.parse_program(code), "\"yes\"");
    }

    #[test]
    fn test_parse_do() {
        let mut parser = Parser::new();
        let code = "(do (+ 1 2) (* 3 4))";
        assert_eq!(parser.parse_program(code), "12");
    }

    #[test]
    fn test_parse_variables() {
        let mut parser = Parser::new();
        let code = r#"
        (var x 5)
        (var y 10)
        (do
            (set x (+ x y))
            (set y (* x y))
            (set y (/ y 2))
        )
        y
        "#;
        assert_eq!(parser.parse_program(code), "75");
        let code = r#"
        (var a 1)
        (var b (+ a 1))
        (do
            (var a (+ b 5))
            (set b (+ a 10))
        )
        (* a b)
        "#;
        assert_eq!(parser.parse_program(code), "17");
    }

    #[test]
    fn test_parse_if() {
        let mut parser = Parser::new();
        let code = "(if (eq 1 1) 5)";
        assert_eq!(parser.parse_program(code), "5");
        let code = "(if (eq 1 2) 5)";
        assert_eq!(parser.parse_program(code), "null");
        let code = "(if (eq 1 1) 5 10)";
        assert_eq!(parser.parse_program(code), "5");
        let code = "(if (eq 1 2) 5 10)";
        assert_eq!(parser.parse_program(code), "10");
        let code = r#"
        (var a 1)
        (var b 5)
        (var c 10)
        (if (eq a 1)
            (set c 20)
            (set c 30)
        )
        (c)
        "#;
        assert_eq!(parser.parse_program(code), "20");
    }

    #[test]
    fn test_parse_loop() {
        let mut parser = Parser::new();
        let code = r#"
        (var a 1)
        (var b 5)
        (var c 10)
        (loop (lt a b)
            (do
                (set a (+ a 1))
                (if (eq a 3) (break))
                (set c (+ c 1))
            )
        )
        (+ a c)
        "#;
        assert_eq!(parser.parse_program(code), "14");
        let code = r#"
        (var a 1)
        (var b 5)
        (var c 10)
        (loop (lt a b)
            (do
                (set a (+ a 1))
                (if (eq a 3) (continue))
                (set c (+ c 1))
            )
        )
        (+ a c)
        "#;
        assert_eq!(parser.parse_program(code), "18");
    }

    #[test]
    fn test_parse_function() {
        let mut parser = Parser::new();
        let code = r#"
        (def add (a b) (+ a b))
        (call add 5 10)
        "#;
        assert_eq!(parser.parse_program(code), "15");
        let code = r#"
        (def add (a b) (+ a b))
        (def mul (a b) (* a b))
        (call mul (call add 5 10) 2)
        "#;
        assert_eq!(parser.parse_program(code), "30");

        let code = r#"
        (def fib (n) (if (eq n 0) 0 (+ n (call fib (- n 1)))))
        (call fib 5)
        "#;
        assert_eq!(parser.parse_program(code), "15");
        let code = r#"
        (def fib (n) (do
            (var r 0)
            (loop (gt n 0) (do
                (set r (+ r n))
                (set n (- n 1))
            ))
            (return r)
        ))
        (call fib 5)
        "#;
        assert_eq!(parser.parse_program(code), "15");
    }

    #[test]
    fn test_is_primitive_type() {
        let parser = Parser::new();
        assert!(parser.is_primitive_type("1"));
        assert!(parser.is_primitive_type("\"hello\""));
        assert!(parser.is_primitive_type("true"));
        assert!(parser.is_primitive_type("false"));
        assert!(parser.is_primitive_type("null"));
        assert!(!parser.is_primitive_type("abc"));
        assert!(!parser.is_primitive_type("(1 2)"));
    }
}
