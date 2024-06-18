use crate::{Block, BlockId, Exit, FuncId, Function, Module, Type, TypeId, Typedef};

struct Tape {
    func: TypeId,
    blocks: Vec<TypeId>,
}

fn tape(old: &Module) -> (Module, Vec<Tape>) {
    let mut new = Module {
        types: old.types.clone(),
        funcs: vec![],
    };
    let tapes = old
        .funcs
        .iter()
        .map(|func| {
            let mut variants = vec![];
            let blocks = func
                .blocks
                .iter()
                .map(|block| {
                    let tape = new.new_type(Typedef::Struct {
                        fields: block
                            .instrs
                            .iter()
                            .flat_map(|instr| &instr.vars)
                            .flat_map(|&var| {
                                let t = func.var_type(var);
                                [t, t]
                            })
                            .collect(),
                    });
                    if let Exit::Return { .. } = block.exit {
                        variants.push(Type::Ref { id: tape });
                    }
                    tape
                })
                .collect();
            let exit = new.new_type(Typedef::Enum { variants });
            Tape { func: exit, blocks }
        })
        .collect();
    (new, tapes)
}

fn get_two_mut<T>(xs: &mut [T], i: usize, j: usize) -> (&mut T, &mut T) {
    if i < j {
        let (ys, zs) = xs.split_at_mut(j);
        (&mut ys[i], &mut zs[0])
    } else {
        let (ys, zs) = xs.split_at_mut(i);
        (&mut zs[0], &mut ys[j])
    }
}

fn get_two_funcs_mut(
    funcs: &mut [Function],
    fwd_id: FuncId,
    bwd_id: FuncId,
) -> (&mut Function, &mut Function) {
    get_two_mut(funcs, fwd_id.0, bwd_id.0)
}

pub fn ad(old: &Module) -> (Module, Vec<(FuncId, FuncId)>) {
    let (mut new, tapes) = tape(old);
    let funcs: Vec<_> = old
        .funcs
        .iter()
        .zip(tapes.iter())
        .map(|(func, tape)| {
            let mut fwd_dom = func.dom.clone();
            fwd_dom.extend(func.dom.iter());
            let mut fwd_cod = func.cod.clone();
            fwd_cod.extend(func.cod.iter());
            fwd_cod.push(Type::Ref { id: tape.func });
            let fwd = new.new_func(Function {
                dom: fwd_dom,
                cod: fwd_cod,
                vars: vec![],
                blocks: vec![],
                entry: func.entry,
            });

            let mut bwd_dom = func.cod.clone();
            bwd_dom.push(Type::Ref { id: tape.func });
            let bwd_cod = func.dom.clone();
            let bwd = new.new_func(Function {
                dom: bwd_dom,
                cod: bwd_cod,
                vars: vec![],
                blocks: vec![],
                entry: BlockId(0),
            });

            (fwd, bwd)
        })
        .collect();
    for (func, &(fwd_id, bwd_id)) in old.funcs.iter().zip(funcs.iter()) {
        let (fwd, bwd) = get_two_funcs_mut(&mut new.funcs, fwd_id, bwd_id);
        for block in &func.blocks {
            let fwd_block = Block {
                params: vec![],
                instrs: vec![],
                exit: Exit::Return { values: vec![] },
            };
        }
    }
    (new, funcs)
}
