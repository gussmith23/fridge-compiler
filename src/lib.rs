use std::collections::HashMap;

use egg::{define_language, Id, RecExpr, Symbol};

define_language! {
    pub enum Language {
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "not" = Not([Id; 1]),
        Symbol(Symbol),
    }
}

pub fn interpret(expr: &RecExpr<Language>, id: Id, env: &HashMap<Symbol, bool>) -> bool {
    match expr.as_ref()[usize::from(id)] {
        Language::And([a_id, b_id]) => interpret(expr, a_id, env) && interpret(expr, b_id, env),
        Language::Or([a_id, b_id]) => interpret(expr, a_id, env) || interpret(expr, b_id, env),
        Language::Not([id]) => !interpret(expr, id, env),
        Language::Symbol(s) => *env.get(&s).expect("Symbol not found in environment!"),
    }
}
#[cfg(test)]
mod tests {

    use super::*;

    /// This test compares two versions of the same program to make sure they're equivalent.
    #[test]
    fn example_0x87() {
        let mut expr = RecExpr::default();
        let a_id = expr.add(Language::Symbol(Symbol::from("A")));
        let b_id = expr.add(Language::Symbol(Symbol::from("B")));
        let c_id = expr.add(Language::Symbol(Symbol::from("C")));
        let not_a_id = expr.add(Language::Not([a_id]));
        let not_b_id = expr.add(Language::Not([b_id]));
        let not_c_id = expr.add(Language::Not([c_id]));
        let g1_id = expr.add(Language::And([not_a_id, not_b_id]));
        let not_g1_id = expr.add(Language::Not([g1_id]));
        let g2_id = expr.add(Language::And([not_g1_id, not_c_id]));
        let not_g2_id = expr.add(Language::Not([g2_id]));
        let g3_id = expr.add(Language::And([not_g1_id, not_g2_id]));
        let g4_id = expr.add(Language::And([not_g2_id, not_c_id]));
        let x_id = expr.add(Language::Or([g3_id, g4_id]));

        let n5_id = expr.add(Language::Or([b_id, a_id]));
        let n6_id = expr.add(Language::And([n5_id, c_id]));
        let n7_part1_id = expr.add(Language::Or([a_id, c_id]));
        let n7_id = expr.add(Language::Or([n7_part1_id, b_id]));
        let n8_id = expr.add(Language::Not([n7_id]));
        let x_min_id = expr.add(Language::Or([n8_id, n6_id]));

        for a in &[true, false] {
            for b in &[true, false] {
                for c in &[true, false] {
                    let mut env = HashMap::default();
                    env.insert(Symbol::from("A"), *a);
                    env.insert(Symbol::from("B"), *b);
                    env.insert(Symbol::from("C"), *c);
                    assert_eq!(
                        interpret(&expr, x_id, &env),
                        interpret(&expr, x_min_id, &env)
                    );
                }
            }
        }
    }
}
