// TODO One bug in this implementation is that the output of OR gates (which are
// just wires) will have another wire attached to them in some cases. This is
// because, e.g. when we're setting up the constraints for an AND, we
// instantiate wires connecting the inputs of the upstream node to the AND gate.
// If the upstream node is an AND, then this is fine, but if the upstream is an
// OR, which is just a wire, we'll add another wire on it.

use std::{
    cmp::{max, Ordering},
    collections::HashMap,
};

use egg::{
    define_language, rewrite, Analysis, CostFunction, EGraph, Id, RecExpr, Rewrite, Runner, Symbol,
};
use z3::{ast::Ast, Context, Solver};

define_language! {
    pub enum Language {
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "not" = Not([Id; 1]),

        "wire" = Wire([Id; 1]),
        // Must take two wires as input. (Can be Wire or WireMerge)
        "gate" = Gate([Id; 2]),
        // Must take two wires as input. (Can be Wire or WireMerge)
        "wire-merge" = WireMerge([Id; 2]),

        Symbol(Symbol),
    }
}

pub fn interpret(expr: &RecExpr<Language>, id: Id, env: &HashMap<Symbol, bool>) -> bool {
    match expr.as_ref()[usize::from(id)] {
        Language::And([a_id, b_id]) => interpret(expr, a_id, env) && interpret(expr, b_id, env),
        Language::Or([a_id, b_id]) => interpret(expr, a_id, env) || interpret(expr, b_id, env),
        Language::Not([id]) => !interpret(expr, id, env),
        Language::Symbol(s) => *env.get(&s).expect("Symbol not found in environment!"),
        _ => panic!(),
    }
}

pub fn lower_and() -> Rewrite<Language, ()> {
    rewrite!("lower-and"; "(and ?a ?b)" => "(gate (wire ?a) (wire ?b))")
}

pub fn lower_or() -> Rewrite<Language, ()> {
    rewrite!("lower-or"; "(or ?a ?b)" => "(wire-merge (wire ?a) (wire ?b))")
}

pub fn simplify_double_wire() -> Rewrite<Language, ()> {
    rewrite!("simplify-double-wire"; "(wire (wire ?a))" => "(wire ?a)")
}

pub fn simplify_wire_merge_into_wire() -> Rewrite<Language, ()> {
    rewrite!("simplify-wire-merge-into-wire"; "(wire (wire-merge ?a ?b))" => "(wire-merge ?a ?b)")
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

struct SymbolAnalysis;
#[derive(Debug, PartialEq)]
enum SymbolName {
    Symbol(String),
    NotSymbol(String),
    None,
}
impl Analysis<Language> for SymbolAnalysis {
    type Data = SymbolName;

    fn make(egraph: &EGraph<Language, Self>, enode: &Language) -> Self::Data {
        match enode {
            Language::Not([id]) => match &egraph[*id].data {
                SymbolName::Symbol(s) => SymbolName::NotSymbol(s.clone()),
                SymbolName::NotSymbol(s) => SymbolName::Symbol(s.clone()),
                SymbolName::None => SymbolName::None,
            },
            Language::Symbol(s) => SymbolName::Symbol(s.as_str().to_string()),
            _ => SymbolName::None,
        }
    }

    fn merge(&self, a: &mut Self::Data, b: Self::Data) -> Option<std::cmp::Ordering> {
        assert_eq!(*a, b);
        Some(Ordering::Equal)
    }
}

/// Create constraints for the given expression. We *should* be doing this for
/// [`EGraph`]s and not [`RecExpr`]s, but I have limited time, so I'm
/// compromising. I think the hard work will be done here; extending this to a
/// full egraph should hopefully not be too hard.
///
/// symbol_constant_value: The value to start at when assigning values to Symbol
/// constants. That is, every symbol (e.g. A or not_A) in the program has a Z3 constant associated with it (giving its species),
pub fn create_constraints_recexpr(
    expr: &RecExpr<Language>,
    top_level_id: Id,
    ctx: &Context,
    solver: &Solver,
    symbol_constant_value: &mut i64,
) {
    // Most program nodes will have associated with them a set of z3 integers
    // representing the output(s) of the node. A node (e.g. an AND) may have
    // multiple outputs as it may have fanout>1.
    let mut outputs: Vec<Vec<z3::ast::Int>> = vec![Vec::default(); expr.as_ref().len()];

    for (id, node) in expr.as_ref().iter().enumerate() {
        match node {
            Language::And([i0_id, i1_id]) => {
                // The set of z3 variables representing the fanned-out outputs
                // of the upstream inputs. We can attach to any of these inputs.
                let i0_inputs = &outputs[usize::from(*i0_id)];
                let i1_inputs = &outputs[usize::from(*i1_id)];

                // Create wires from the upstream gate/symbols i0 and i1. These
                // wires can be connected to ANY of the fanned-out upstream
                // outputs. For each, we make a constraint saying that they must
                // be connected to at least one of the outputs.
                let (_, i0_wire_i_var, i0_wire_o_var) =
                    create_wire(&format!("and_{}_i0_wire", id), ctx);
                let (_, i1_wire_i_var, i1_wire_o_var) =
                    create_wire(&format!("and_{}_i1_wire", id), ctx);
                solver.assert(
                    &i0_inputs
                        .iter()
                        .map(|input| input._eq(&i0_wire_i_var))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );
                solver.assert(
                    &i1_inputs
                        .iter()
                        .map(|input| input._eq(&i1_wire_i_var))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );

                // Create the gate itself, and any "multiplier" gates needed to
                // increase the fanout. If the fanout of AND is greater than 2,
                // then we need to multiply up the output using a binary tree of
                // gates.
                let fanout = get_fanout(expr, id.into());
                assert!(id == top_level_id.into() || fanout >= 1);
                let mut gates = (0..max(1, fanout - 1))
                    .map(|i| create_gate(&format!("and_{}_gate_{}", id, i), ctx))
                    .collect::<Vec<_>>();

                for (gate_i, (_gate_var, gate_i0_var, gate_i1_var, _gate_o0_var, _gate_o1_var)) in
                    gates.iter().enumerate()
                {
                    if gate_i == 0 {
                        // connect it to the inputs
                        solver.assert(&i0_wire_o_var._eq(&gate_i0_var));
                        solver.assert(&i1_wire_o_var._eq(&gate_i1_var));
                    } else {
                        // Connect to parent output
                        let (_, _, _, parent_gate_o0_var, parent_gate_o1_var) =
                            &gates[(gate_i - 1) / 2];
                        let parent_gate_o = if gate_i % 2 == 1 {
                            parent_gate_o0_var
                        } else {
                            parent_gate_o1_var
                        };
                        let (_wire_var, wire_i_var, wire_o_var) =
                            create_wire(&format!("and_{}_gate_{}_input", id, &gate_i), ctx);
                        solver.assert(&wire_i_var._eq(&parent_gate_o));
                        solver.assert(&wire_o_var._eq(&gate_i0_var));
                    }
                }
                // Collect the fanned-out outputs. If fanout is n, we just grab
                // the outputs of the last n/2 gates. If n is odd, we also grab
                // the second output of the n/2+1th gate.
                outputs[id] = gates
                    .drain(..)
                    .rev()
                    .enumerate()
                    .filter_map(|(i, (_, _, _, o0, o1))| {
                        if i == 0 {
                            if fanout == 1 {
                                Some(vec![o0])
                            } else if fanout > 1 {
                                Some(vec![o0, o1])
                            } else {
                                unreachable!()
                            }
                        } else if i < fanout / 2 {
                            Some(vec![o0, o1])
                        } else if i == fanout / 2 && fanout % 2 == 1 {
                            Some(vec![o1])
                        } else {
                            None
                        }
                    })
                    .flatten()
                    .collect::<Vec<_>>();
            }
            Language::Or([i0_id, i1_id]) => {
                // The set of z3 variables representing the fanned-out outputs
                // of the upstream inputs. We can attach to any of these inputs.
                let i0_inputs = &outputs[usize::from(*i0_id)];
                let i1_inputs = &outputs[usize::from(*i1_id)];

                // Create wires from the upstream gate/symbols i0 and i1. These
                // wires can be connected to ANY of the fanned-out upstream
                // outputs. For each, we make a constraint saying that they must
                // be connected to at least one of the outputs.
                let (_, i0_wire_i_var, _i0_wire_o_var) =
                    create_wire(&format!("or_{}_i0_wire", id), ctx);
                let (_, i1_wire_i_var, _i1_wire_o_var) =
                    create_wire(&format!("or_{}_i1_wire", id), ctx);
                solver.assert(
                    &i0_inputs
                        .iter()
                        .map(|input| input._eq(&i0_wire_i_var))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );
                solver.assert(
                    &i1_inputs
                        .iter()
                        .map(|input| input._eq(&i1_wire_i_var))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );
            }
            Language::Symbol(_) | Language::Not(_) => {
                // The name of the symbol, with "not" appended if it's a Not node.
                let name = match node {
                    Language::Symbol(s) => s.as_str().to_string(),
                    Language::Not([id]) => format!(
                        "not_{}",
                        match expr[*id] {
                            Language::Symbol(s) => s.as_str(),
                            _ => panic!("Not node should point to Symbol node"),
                        }
                    ),
                    _ => unreachable!(),
                };

                // Make a constant for the symbol's species, and set it.
                let symbol_const = z3::ast::Int::new_const(ctx, name.clone());
                solver.assert(
                    &symbol_const._eq(&z3::ast::Int::from_i64(ctx, *symbol_constant_value)),
                );
                *symbol_constant_value += 1;

                let fanout = get_fanout(expr, id.into());
                assert!(id == top_level_id.into() || fanout >= 1);
                if fanout == 1 {
                    // If fanout is just 1, we don't need any fancy
                    // multiplication circuitry.
                    outputs[id] = vec![symbol_const];
                } else {
                    // If fanout is >1 we instantiate the multiplier gates for
                    // this node. The number of gates we need is equal to the
                    // fanout-1, if we multiply using a binary tree pattern:
                    //     A    1
                    //      \  /
                    //  1   Gate   1
                    //   \  /  \  /
                    //   Gate  Gate
                    //   /  \  /  \
                    //  A   A  A   A
                    let mut multiplier_gates = (0..(fanout - 1))
                        .map(|i| {
                            create_gate(&format!("symbol_{}_multiplier_gate_{}", &name, i), ctx)
                        })
                        .collect::<Vec<_>>();

                    for (
                        gate_i,
                        (_gate_var, gate_i0_var, _gate_i1_var, _gate_o0_var, _gate_o1_var),
                    ) in multiplier_gates.iter().enumerate()
                    {
                        if gate_i == 0 {
                            // connect it to the symbol
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("symbol_{}_multiplier_gate_{}_input", &name, &gate_i),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&symbol_const));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        } else {
                            // Connect to parent output
                            let (_, _, _, parent_gate_o0_var, parent_gate_o1_var) =
                                &multiplier_gates[(gate_i - 1) / 2];
                            let parent_gate_o = if gate_i % 2 == 1 {
                                parent_gate_o0_var
                            } else {
                                parent_gate_o1_var
                            };
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("symbol_{}_multiplier_gate_{}_input", &name, &gate_i),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&parent_gate_o));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        }
                    }

                    // Collect the fanned-out outputs. If fanout is n, we just
                    // grab the outputs of the last n/2 multiplier gates. If n
                    // is odd, we also grab the second output of the n/2+1th
                    // gate.
                    outputs[id] = multiplier_gates
                        .drain(..)
                        .rev()
                        .enumerate()
                        .filter_map(|(i, (_, _, _, o0, o1))| {
                            if i < fanout / 2 {
                                Some(vec![o0, o1])
                            } else if i == fanout / 2 && fanout % 2 == 1 {
                                Some(vec![o1])
                            } else {
                                None
                            }
                        })
                        .flatten()
                        .collect::<Vec<_>>();
                }
            }
            Language::Gate([i0_id, i1_id]) => {
                match expr[*i0_id] {
                    Language::Wire(_) | Language::WireMerge(_) => (),
                    _ => panic!("Program is ill-formed; inputs to Gate must be wires"),
                }
                match expr[*i1_id] {
                    Language::Wire(_) | Language::WireMerge(_) => (),
                    _ => panic!("Program is ill-formed; inputs to Gate must be wires"),
                }

                // The set of z3 variables representing the fanned-out outputs
                // of the upstream wires. To be clear: these are of type "wire
                // output".
                let i0_wire_outputs = &outputs[usize::from(*i0_id)];
                let i1_wire_outputs = &outputs[usize::from(*i1_id)];

                // Create the gate itself.
                let (_, gate_input_0, gate_input_1, gate_output_0, gate_output_1) =
                    create_gate(&format!("gate_{}", id), ctx);

                // Connect upstream wires to the gate inputs. These wires can be
                // connected to ANY of the fanned-out upstream outputs. For
                // each, we make a constraint saying that they must be connected
                // to at least one of the outputs.
                solver.assert(
                    &i0_wire_outputs
                        .iter()
                        .map(|wire_output| wire_output._eq(&gate_input_0))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );
                solver.assert(
                    &i1_wire_outputs
                        .iter()
                        .map(|wire_output| wire_output._eq(&gate_input_1))
                        .reduce(|a, b| z3::ast::Bool::or(ctx, &[&a, &b]))
                        .unwrap(),
                );

                // The outputs are just the two gate outputs.
                outputs[id] = vec![gate_output_0, gate_output_1];
            }
            Language::Wire([i0_id]) => {
                match expr[*i0_id] {
                    Language::Gate(_) | Language::Symbol(_) | Language::Not(_) => (),
                    _ => panic!("Program is ill-formed; inputs to Wire must Gate, Symbol, or Not"),
                }

                // The outputs of the upstream node.
                let upstream_outputs = &outputs[usize::from(*i0_id)];
                match expr[*i0_id] {
                    Language::Gate(_) => assert_eq!(upstream_outputs.len(), 2),
                    Language::Symbol(_) | Language::Not(_) => {
                        assert_eq!(upstream_outputs.len(), 1)
                    }
                    _ => unreachable!(),
                }

                // Get the fanout of this node; i.e. the number of times this
                // node is requested.
                let fanout = get_fanout(expr, id.into());
                assert!(id == top_level_id.into() || fanout >= 1);

                // The number of additional gates we need to "multiply up" the
                // result. E.g. if we have a requested fanout of 4, but just 1
                // output, then we need 3 gates (arranged in a binary tree) to
                // multiply the 1 output up to 4. If we have 2 outputs and need
                // 3, we just need one extra gate.
                let num_gates_needed = usize::saturating_sub(fanout, upstream_outputs.len());

                let mut gates = (0..num_gates_needed)
                    .map(|gate_i| {
                        create_gate(&format!("multiplier_{}_on_wire_{}", gate_i, id), ctx)
                    })
                    .collect::<Vec<_>>();

                for (gate_i, (_gate_var, gate_i0_var, _gate_i1_var, _gate_o0_var, _gate_o1_var)) in
                    gates.iter().enumerate()
                {
                    // If there's only one upstream output, we're building a
                    // tree like this:
                    //           |  <-- single upstream output
                    //          GATE
                    //          /  \
                    //        GATE  GATE
                    //        / \    / \
                    //       ...
                    if upstream_outputs.len() == 1 {
                        if gate_i == 0 {
                            // Connect to our single upstream output
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("multiplier_{}_on_wire_{}_input", &gate_i, id),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&upstream_outputs[0]));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        } else {
                            // Connect to parent output
                            let (_, _, _, parent_gate_o0_var, parent_gate_o1_var) =
                                &gates[(gate_i - 1) / 2];
                            let parent_gate_o = if gate_i % 2 == 1 {
                                parent_gate_o0_var
                            } else {
                                parent_gate_o1_var
                            };
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("multiplier_{}_on_wire_{}_input", &gate_i, id),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&parent_gate_o));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        }
                    } else if upstream_outputs.len() == 2 {
                        // If there's two upstream outputs, we're building a tree
                        // like this:
                        //           |             | <-- dual upstream outputs
                        //          GATE          GATE
                        //          /  \          /  \
                        //        GATE  GATE    GATE  GATE
                        //        / \    / \
                        //       ...
                        if gate_i == 0 {
                            // Connect to our first upstream output
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("multiplier_{}_on_wire_{}_input", &gate_i, id),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&upstream_outputs[0]));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        } else if gate_i == 1 {
                            // Connect to our second upstream output
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("multiplier_{}_on_wire_{}_input", &gate_i, id),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&upstream_outputs[1]));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        } else {
                            // Connect to parent output (Note that this
                            // calculation is different in the 2 upstream
                            // outputs case!)
                            let (_, _, _, parent_gate_o0_var, parent_gate_o1_var) =
                                &gates[(gate_i + 1 - 1) / 2 - 1];
                            // This is also different! == 1 became == 0.
                            let parent_gate_o = if gate_i % 2 == 0 {
                                parent_gate_o0_var
                            } else {
                                parent_gate_o1_var
                            };
                            let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                                &format!("multiplier_{}_on_wire_{}_input", gate_i, id),
                                ctx,
                            );
                            solver.assert(&wire_i_var._eq(&parent_gate_o));
                            solver.assert(&wire_o_var._eq(&gate_i0_var));
                        }
                    } else {
                        unreachable!()
                    }
                }

                if num_gates_needed > 0 && num_gates_needed >= upstream_outputs.len() {
                    // All of our outputs come from the multiplier gates.
                    outputs[id] = gates
                        .drain(..)
                        .rev()
                        .enumerate()
                        .filter_map(|(i, (_, _, _, o0, o1))| {
                            if i < fanout / 2 {
                                Some(vec![o0, o1])
                            } else if i == fanout / 2 && fanout % 2 == 1 {
                                Some(vec![o1])
                            } else {
                                None
                            }
                        })
                        .flatten()
                        // On every gate output, instantiate a wire and return
                        // its output.
                        .enumerate()
                        .map(|(i, gate_output)| {
                            let (_, wire_i, wire_o) =
                                create_wire(&format!("wire_{}_output_{}", id, i), ctx);
                            solver.assert(&wire_i._eq(&gate_output));
                            wire_o
                        })
                        .collect::<Vec<_>>();
                } else if num_gates_needed == 0 {
                    assert!(fanout <= upstream_outputs.len());
                    // All of our outputs come from the upstream outputs; no
                    // multiplier gates needed.
                    outputs[id] = upstream_outputs
                        .iter()
                        .take(fanout)
                        .enumerate()
                        .map(|(i, output)| {
                            let (_, wire_i, wire_o) =
                                create_wire(&format!("wire_{}_output_{}", id, i), ctx);
                            solver.assert(&wire_i._eq(&output));
                            wire_o
                        })
                        .collect::<Vec<_>>();
                } else {
                    // Our outputs come from a mix of upstream outputs and
                    // multiplier gates. I think this is only possible if:
                    assert_eq!(upstream_outputs.len(), 2);
                    assert_eq!(fanout, 3);
                    assert_eq!(num_gates_needed, 1);
                    assert_eq!(gates.len(), 1);
                    // In which case we can hard code this:
                    outputs[id] = gates
                        .drain(..)
                        .flat_map(|(_, _, _, o0, o1)| vec![o0, o1])
                        .chain(std::iter::once(upstream_outputs[1].clone()))
                        .enumerate()
                        .map(|(i, gate_output)| {
                            let (_, wire_i, wire_o) =
                                create_wire(&format!("wire_{}_output_{}", id, i), ctx);
                            solver.assert(&wire_i._eq(&gate_output));
                            wire_o
                        })
                        .collect::<Vec<_>>();
                }

                assert_eq!(outputs[id].len(), fanout);
            }
            Language::WireMerge([i0_id, i1_id]) => {
                match expr[*i0_id] {
                    Language::Wire(_) | Language::WireMerge(_) => (),
                    _ => panic!(
                        "Program is ill-formed; inputs to WireMerge must be Wire or WireMerge"
                    ),
                };
                match expr[*i1_id] {
                    Language::Wire(_) | Language::WireMerge(_) => (),
                    _ => panic!(
                        "Program is ill-formed; inputs to WireMerge must be Wire or WireMerge"
                    ),
                };

                // In a WireMerge, we're ensuring that one of the pairs fanning
                // out from two wire nodes are the same, which implements OR
                // logic. Here, we make a big OR statement that basically says,
                // for each pair of outputs from the two fanned-out wires, that
                // at least one of the pairs are equal to each other (and equal
                // to a third variable, upstream_output)
                let upstream_output =
                    z3::ast::Int::new_const(ctx, format!("wiremerge_{}_merged_wire_output", id));
                let mut or_statement = z3::ast::Bool::from_bool(ctx, false);
                for wire_output_from_i0 in &outputs[usize::from(*i0_id)] {
                    for wire_output_from_i1 in &outputs[usize::from(*i1_id)] {
                        or_statement = z3::ast::Bool::or(
                            ctx,
                            &[
                                &or_statement,
                                &z3::ast::Bool::and(
                                    ctx,
                                    &[
                                        &upstream_output._eq(&wire_output_from_i0),
                                        &upstream_output._eq(&wire_output_from_i1),
                                    ],
                                ),
                            ],
                        )
                    }
                }

                // Get the fanout of this node; i.e. the number of times this
                // node is requested.
                let fanout = get_fanout(expr, id.into());
                assert!(
                    id == top_level_id.into() || fanout >= 1,
                    "{}, {}",
                    id,
                    fanout
                );

                // The number of additional gates we need to "multiply up" the
                // result. E.g. if we have a requested fanout of 4, then we need
                // 3 gates (arranged in a binary tree) to multiply the 1 output
                // up to 4.
                let num_gates_needed = usize::saturating_sub(fanout, 1);

                let mut gates = (0..num_gates_needed)
                    .map(|gate_i| {
                        create_gate(&format!("multiplier_{}_on_wiremerge_{}", gate_i, id), ctx)
                    })
                    .collect::<Vec<_>>();

                for (gate_i, (_gate_var, gate_i0_var, _gate_i1_var, _gate_o0_var, _gate_o1_var)) in
                    gates.iter().enumerate()
                {
                    // We're building a tree like this:
                    //           |  <-- single upstream output
                    //          GATE
                    //          /  \
                    //        GATE  GATE
                    //        / \    / \
                    //       ...
                    if gate_i == 0 {
                        // Connect to our single upstream output
                        let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                            &format!("multiplier_{}_on_wiremerge_{}_input", &gate_i, id),
                            ctx,
                        );
                        solver.assert(&wire_i_var._eq(&upstream_output));
                        solver.assert(&wire_o_var._eq(&gate_i0_var));
                    } else {
                        // Connect to parent output
                        let (_, _, _, parent_gate_o0_var, parent_gate_o1_var) =
                            &gates[(gate_i - 1) / 2];
                        let parent_gate_o = if gate_i % 2 == 1 {
                            parent_gate_o0_var
                        } else {
                            parent_gate_o1_var
                        };
                        let (_wire_var, wire_i_var, wire_o_var) = create_wire(
                            &format!("multiplier_{}_on_wiremerge_{}_input", &gate_i, id),
                            ctx,
                        );
                        solver.assert(&wire_i_var._eq(&parent_gate_o));
                        solver.assert(&wire_o_var._eq(&gate_i0_var));
                    }
                }

                let our_outputs = if fanout == 1 {
                    vec![upstream_output]
                } else {
                    gates
                        .drain(..)
                        .rev()
                        .enumerate()
                        .filter_map(|(i, (_, _, _, o0, o1))| {
                            if i < fanout / 2 {
                                Some(vec![o0, o1])
                            } else if i == fanout / 2 && fanout % 2 == 1 {
                                Some(vec![o1])
                            } else {
                                None
                            }
                        })
                        .flatten()
                        // On every gate output, instantiate a wire and return
                        // its output.
                        .enumerate()
                        .map(|(i, gate_output)| {
                            let (_, wire_i, wire_o) =
                                create_wire(&format!("wiremerge_{}_output_{}", id, i), ctx);
                            solver.assert(&wire_i._eq(&gate_output));
                            wire_o
                        })
                        .collect::<Vec<_>>()
                };

                assert_eq!(our_outputs.len(), fanout);

                outputs[id] = our_outputs;
            }
        }
    }
}

/// Creates the variables and constraints representing a gate.
fn create_gate<'a>(
    name: &str,
    ctx: &'a Context,
) -> (
    z3::ast::Int<'a>,
    z3::ast::Int<'a>,
    z3::ast::Int<'a>,
    z3::ast::Int<'a>,
    z3::ast::Int<'a>,
) {
    let gate_var = z3::ast::Int::new_const(ctx, format!("gate_{}", name));
    let gate_i0_var = z3::ast::Int::new_const(ctx, format!("gate_{}_i0", name));
    let gate_i1_var = z3::ast::Int::new_const(ctx, format!("gate_{}_i1", name));
    let gate_o0_var = z3::ast::Int::new_const(ctx, format!("gate_{}_o0", name));
    let gate_o1_var = z3::ast::Int::new_const(ctx, format!("gate_{}_o1", name));
    (gate_var, gate_i0_var, gate_i1_var, gate_o0_var, gate_o1_var)
}

fn create_wire<'a>(
    name: &str,
    ctx: &'a Context,
) -> (z3::ast::Int<'a>, z3::ast::Int<'a>, z3::ast::Int<'a>) {
    let wire_var = z3::ast::Int::new_const(ctx, format!("wire_{}", name));
    let wire_i_var = z3::ast::Int::new_const(ctx, format!("wire_{}_i", name));
    let wire_o_var = z3::ast::Int::new_const(ctx, format!("wire_{}_o", name));
    (wire_var, wire_i_var, wire_o_var)
}

/// Get the fanout of a subexpression---that is, the number of times it is used.
/// In an [`EGraph`], this can be done with the (hidden) field `parents`. Will
/// not work if there are loops. Only considers usages by OR and AND nodes when
/// calculating fanout.
fn get_fanout(expr: &RecExpr<Language>, id: Id) -> usize {
    let mut count = 0;
    for node in expr.as_ref() {
        match node {
            Language::And([a_id, b_id])
            | Language::Or([a_id, b_id])
            | Language::Gate([a_id, b_id])
            | Language::WireMerge([a_id, b_id]) => {
                if *a_id == id {
                    count += 1
                }
                if *b_id == id {
                    count += 1
                }
            }
            Language::Wire([a_id]) => {
                if *a_id == id {
                    count += 1
                }
            }
            _ => (),
        }
    }
    count
}

pub fn lower(expr: RecExpr<Language>) -> RecExpr<Language> {
    let mut egraph = EGraph::new(());
    let id_in_egraph = egraph.add_expr(&expr);

    let runner = Runner::<_, _, ()>::new(()).with_egraph(egraph).run(&vec![
        lower_and(),
        lower_or(),
        simplify_double_wire(),
        simplify_wire_merge_into_wire(),
    ]);

    // A cost function which extracts the smallest program, banning "high level"
    // constructs like And and Or.
    struct LowerCostFunction;
    impl CostFunction<Language> for LowerCostFunction {
        type Cost = usize;

        fn cost<C>(&mut self, enode: &Language, mut costs: C) -> Self::Cost
        where
            C: FnMut(Id) -> Self::Cost,
        {
            match enode {
                Language::Gate([a, b]) | Language::WireMerge([a, b]) => {
                    usize::saturating_add(1, usize::saturating_add(costs(*a), costs(*b)))
                }
                Language::Wire([a]) | Language::Not([a]) => usize::saturating_add(1, costs(*a)),
                Language::Symbol(_) => 1,
                Language::And(_) | Language::Or(_) => usize::MAX,
            }
        }
    }

    let (cost, new_expr) =
        egg::Extractor::new(&runner.egraph, LowerCostFunction).find_best(id_in_egraph);
    assert!(cost < usize::MAX);

    new_expr
}

pub fn push_nots_to_leaves(expr: RecExpr<Language>) -> RecExpr<Language> {
    let mut egraph = EGraph::new(());
    let id_in_egraph = egraph.add_expr(&expr);

    let runner = Runner::<_, _, ()>::new(()).with_egraph(egraph).run(&vec![
        demorgans_and(),
        demorgans_or(),
        simplify_double_not(),
    ]);

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
                Language::And(ids)
                | Language::Or(ids)
                | Language::Gate(ids)
                | Language::WireMerge(ids) => OnlyAllowNotsOnLeavesCost::IsNotSymbol(
                    ids.iter()
                        .map(|id| costs(*id))
                        .map(|cost| match cost {
                            OnlyAllowNotsOnLeavesCost::IsSymbol => false,
                            OnlyAllowNotsOnLeavesCost::IsNotSymbol(b) => b,
                        })
                        .reduce(|a, b| a || b)
                        .unwrap(),
                ),
                Language::Wire(ids) => OnlyAllowNotsOnLeavesCost::IsNotSymbol(
                    ids.iter()
                        .map(|id| costs(*id))
                        .map(|cost| match cost {
                            OnlyAllowNotsOnLeavesCost::IsSymbol => false,
                            OnlyAllowNotsOnLeavesCost::IsNotSymbol(b) => b,
                        })
                        .reduce(|a, b| a || b)
                        .unwrap(),
                ),
            }
        }
    }

    // Assert that there exists some expression which contains nots only at
    // the leaves.
    let (cost, new_expr) =
        egg::Extractor::new(&runner.egraph, OnlyAllowNotsOnLeaves).find_best(id_in_egraph);
    assert!(match cost {
        OnlyAllowNotsOnLeavesCost::IsNotSymbol(true) => false,
        _ => true,
    });

    new_expr
}

#[cfg(test)]
mod tests {

    use egg::{EGraph, Runner};
    use z3::Config;

    use super::*;

    fn get_0x87() -> RecExpr<Language> {
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

        expr
    }

    #[test]
    fn test_get_fanout() {
        let expr = get_0x87();
        // Fanout of not_a is 1
        assert_eq!(get_fanout(&expr, From::from(3)), 1);
        // Fanout of not_c is 2
        assert_eq!(get_fanout(&expr, From::from(5)), 2);
    }

    #[test]
    fn test_get_fanout_0x87_lowered() {
        let expr = get_0x87();
        let expr = push_nots_to_leaves(expr);
        let expr = lower(expr);
        println!("{}", expr.pretty(80));
        println!("{:?}", expr);
        // Fanout of a is 1
        assert_eq!(get_fanout(&expr, From::from(0)), 1);
        // Fanout of not_a is 1
        assert_eq!(get_fanout(&expr, From::from(5)), 1);
        // Fanout of wire(a) is 1
        assert_eq!(get_fanout(&expr, From::from(2)), 1);
        // Fanout of wire(not_a) is 1
        assert_eq!(get_fanout(&expr, From::from(6)), 1);
        // fanout of (wire-merge (wire (gate (wire (not A)) (wire (not B)))) (wire C)) is 2
        assert_eq!(get_fanout(&expr, From::from(13)), 2);
    }

    #[test]
    fn create_constraints() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let mut symbol_constant_value = 0;

        let mut expr = RecExpr::default();
        let a = expr.add(Language::Symbol(Symbol::from("a")));
        let b = expr.add(Language::Symbol(Symbol::from("b")));
        let and0 = expr.add(Language::And([a, b]));
        let and1 = expr.add(Language::And([a, b]));
        let and2 = expr.add(Language::And([a, b]));
        let or0 = expr.add(Language::Or([and0, and1]));
        let _or1 = expr.add(Language::Or([or0, and2]));

        let expr = push_nots_to_leaves(expr);
        let expr = lower(expr);
        println!("{}", expr.pretty(80));

        create_constraints_recexpr(
            &expr,
            (expr.as_ref().len() - 1).into(),
            &ctx,
            &solver,
            &mut symbol_constant_value,
        );

        println!("{:?}", solver);

        println!("{:?}", solver.check());
        println!("{:?}", solver.get_model());
    }

    #[test]
    fn create_constraints_recexpr_0x87() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let mut symbol_constant_value = 0;

        let expr = get_0x87();
        let expr = push_nots_to_leaves(expr);
        let expr = lower(expr);
        println!("{}", expr.pretty(80));

        create_constraints_recexpr(
            &expr,
            From::from(expr.as_ref().len() - 1),
            &ctx,
            &solver,
            &mut symbol_constant_value,
        );

        println!("{:?}", solver);
    }

    /// This test tests the feasibility of running a large set of rewrites to
    /// saturation on a small expression.
    #[test]
    #[ignore = "can't saturate with these rewrites"]
    fn run_all_rewrites_to_saturation_0x87() {
        let expr = get_0x87();
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
        let expr = get_0x87();
        push_nots_to_leaves(expr);
    }

    /// Tests lowering.
    #[test]
    fn lower_0x87() {
        let expr = get_0x87();
        println!("{}", expr.pretty(40));
        let expr = push_nots_to_leaves(expr);
        println!("{}", expr.pretty(40));
        let expr = lower(expr);
        println!("{}", expr.pretty(40));
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
