use std::collections::HashMap;

use egg::{define_language, rewrite, Id, RecExpr, Rewrite, Symbol};

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

pub fn demorgans_and() -> Rewrite<Language, ()> {
    rewrite!("demorgans-and"; "(not (and ?a ?b))" => "(or (not ?a) (not ?b))")
}

pub fn demorgans_or() -> Rewrite<Language, ()> {
    rewrite!("demorgans-or"; "(not (or ?a ?b))" => "(and (not ?a) (not ?b))")
}

pub fn simplify_double_not() -> Rewrite<Language, ()> {
    rewrite!("simplify-double-not"; "(not (not ?a))" => "?a")
}

pub fn introduce_double_not() -> Rewrite<Language, ()> {
    rewrite!("introduce-double-not"; "?a" => "(not (not ?a))")
}

pub fn distribute_or() -> Rewrite<Language, ()> {
    rewrite!("distribute-or"; "(or ?a (and ?b ?c))" => "(and (or ?a ?b) (or ?a ?c))")
}

pub fn reverse_distribute_or() -> Rewrite<Language, ()> {
    rewrite!("reverse-distribute-or"; "(and (or ?a ?b) (or ?a ?c))" => "(or ?a (and ?b ?c))")
}

pub fn distribute_and() -> Rewrite<Language, ()> {
    rewrite!("distribute-and"; "(and ?a (or ?b ?c))" => "(or (and ?a ?b) (and ?a ?c))")
}

pub fn reverse_distribute_and() -> Rewrite<Language, ()> {
    rewrite!("reverse-distribute-and"; "(or (and ?a ?b) (and ?a ?c))" => "(and ?a (or ?b ?c))")
}

pub fn commute_or() -> Rewrite<Language, ()> {
    rewrite!("commute-or"; "(or ?a ?b)" => "(or ?b ?a)")
}

pub fn commute_and() -> Rewrite<Language, ()> {
    rewrite!("commute-and"; "(and ?a ?b)" => "(and ?b ?a)")
}

pub fn absorb_and() -> Rewrite<Language, ()> {
    rewrite!("absorb-and"; "(and ?a (or ?a ?b))" => "?a")
}

pub fn absorb_or() -> Rewrite<Language, ()> {
    rewrite!("absorb-or"; "(or ?a (and ?a ?b))" => "?a")
}

pub fn associate_or() -> Rewrite<Language, ()> {
    rewrite!("associate-or"; "(or ?a (or ?b ?c))" => "(or (or ?a ?b) ?c)")
}

pub fn reverse_associate_or() -> Rewrite<Language, ()> {
    rewrite!("reverse-associate-or"; "(or (or ?a ?b) ?c)" => "(or ?a (or ?b ?c))")
}

pub fn associate_and() -> Rewrite<Language, ()> {
    rewrite!("associate-and"; "(and ?a (and ?b ?c))" => "(and (and ?a ?b) ?c)")
}

// VVV TODO  WAS WRITING HERE WHEN MY BATTERY DIED

pub fn reverse_associate_and() -> Rewrite<Language, ()> {
    rewrite!("reverse-associate-and"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))")
}

// ^^^ TODO  WAS WRITING HERE WHEN MY BATTERY DIED

#[cfg(test)]
mod tests {

    use egg::{CostFunction, EGraph, Runner};

    use super::*;

    /// This test tests the feasibility of running a large set of rewrites to
    /// saturation on a small expression.
    #[test]
    #[ignore = "can't saturate with these rewrites"]
    fn run_all_rewrites_to_saturation_0x87() {
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
        let _x_id = expr.add(Language::Or([g3_id, g4_id]));

        let mut egraph = EGraph::new(());
        let _x_id_in_egraph = egraph.add_expr(&expr);

        let runner = Runner::<_, _, ()>::new(()).with_egraph(egraph).run(&vec![
            demorgans_and(),
            demorgans_or(),
            simplify_double_not(),
            introduce_double_not(),
            associate_and(),
            associate_or(),
            distribute_and(),
            reverse_distribute_and(),
            distribute_or(),
            reverse_distribute_or(),
            absorb_and(),
            absorb_or(),
            commute_and(),
            commute_or(),
        ]);

        runner.print_report();
        assert!(match runner.stop_reason {
            Some(egg::StopReason::Saturated) => true,
            _ => false,
        });
    }

    /// Tests whether DeMorgan rewrites successfully push the Nots to the leaves
    /// of the program.
    #[test]
    fn push_nots_to_leaves_0x87() {
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
        let _x_id = expr.add(Language::Or([g3_id, g4_id]));

        let mut egraph = EGraph::new(());
        let x_id_in_egraph = egraph.add_expr(&expr);

        let runner = Runner::<_, _, ()>::new(()).with_egraph(egraph).run(&vec![
            demorgans_and(),
            demorgans_or(),
            simplify_double_not(),
        ]);

        runner.print_report();
        /// this [`CostFunction`] helps us determine if all nots have been
        /// pushed to the leaves of the program.
        struct OnlyAllowNotsOnLeaves;

        /// This cost enum conveys whether this is an enode where [`Not`]s
        /// appear anywhere other than on literals.
        #[derive(Debug, PartialOrd, PartialEq, Clone)]
        enum OnlyAllowNotsOnLeavesCost {
            /// Represents the case where an enode is a symbol, and thus it is
            /// trivially true that [`Not`]s don't appear on anything but
            /// symbols in this expression (because this expression is just a
            /// single symbol!)
            IsSymbol,
            /// Represents the case where an enode is not a symbol, in which
            /// case, the boolean represents whether this expression contains
            /// [`Language::Not`]s on anything other than symbols.
            IsNotSymbol(bool),
        }

        impl CostFunction<Language> for OnlyAllowNotsOnLeaves {
            type Cost = OnlyAllowNotsOnLeavesCost;

            fn cost<C>(&mut self, enode: &Language, mut costs: C) -> Self::Cost
            where
                C: FnMut(Id) -> Self::Cost,
            {
                match enode {
                    Language::Symbol(_) => OnlyAllowNotsOnLeavesCost::IsSymbol,
                    Language::Not([id]) => match costs(*id) {
                        OnlyAllowNotsOnLeavesCost::IsSymbol => {
                            OnlyAllowNotsOnLeavesCost::IsNotSymbol(false)
                        }
                        _ => OnlyAllowNotsOnLeavesCost::IsNotSymbol(true),
                    },
                    Language::And(ids) | Language::Or(ids) => {
                        OnlyAllowNotsOnLeavesCost::IsNotSymbol(
                            ids.iter()
                                .map(|id| costs(*id))
                                .map(|cost| match cost {
                                    OnlyAllowNotsOnLeavesCost::IsSymbol => false,
                                    OnlyAllowNotsOnLeavesCost::IsNotSymbol(b) => b,
                                })
                                .reduce(|a, b| a || b)
                                .unwrap(),
                        )
                    }
                }
            }
        }

        // Assert that there exists some expression which contains nots only at
        // the leaves.
        let result =
            egg::Extractor::new(&runner.egraph, OnlyAllowNotsOnLeaves).find_best(x_id_in_egraph);
        println!("{}", result.1);
        assert!(match result.0 {
            OnlyAllowNotsOnLeavesCost::IsNotSymbol(true) => false,
            _ => true,
        });
    }

    /// This test compares two versions of the same program to make sure they're
    /// equivalent.
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
