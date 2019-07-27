#![feature(test, slice_patterns)]
#![warn(clippy::all)]

#[macro_use]
extern crate derivative;
extern crate test;

mod store;

use itertools::Itertools;
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::rc::Rc;
use std::str::CharIndices;

macro_rules! catch {
    ($($code:tt)+) => {
        (|| Some({ $($code)+ }))()
    };
}

struct AstStorePhantom;
type AstKey = store::Key<AstStorePhantom>;
type AstStore<'a> = store::Store<AstStorePhantom, AstNode<'a>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum ExprType {
    Int,
    String,
    Bool,
    Void,
}

impl ExprType {
    fn into_value_type(self) -> ValueType {
        match self {
            ExprType::Int => ValueType::Int,
            ExprType::String => ValueType::String,
            ExprType::Bool => ValueType::Bool,
            ExprType::Void => panic!("Void is not a Value"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum ExprSlot {
    Value { name: &'static str },
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
struct ExprShape {
    slots: Vec<ExprSlot>,
    #[derivative(Debug = "ignore")]
    build_expr: fn(&AstStore, &[AstKey]) -> AstExpr,
}

#[derive(Clone, Debug)]
struct ExprDecl {
    name: &'static str,
    symbol: char,
    shapes: Vec<ExprShape>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Int(i64),
    String(Rc<String>),
    Bool(bool),
}

impl Value {
    fn expr_type(&self) -> ExprType {
        match self {
            Value::Int(_) => ExprType::Int,
            Value::String(_) => ExprType::String,
            Value::Bool(_) => ExprType::Bool,
        }
    }

    #[allow(dead_code)]
    fn value_type(&self) -> ValueType {
        match self {
            Value::Int(_) => ValueType::Int,
            Value::String(_) => ValueType::String,
            Value::Bool(_) => ValueType::Bool,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum AstExpr {
    Constant(Value),
    Add(AstKey, AstKey),
    Print(AstKey),
    ReadLine,
    If(AstKey, AstKey, AstKey),
    Compare(Ordering, AstKey, AstKey),
    Repeat(AstKey, AstKey),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TypeErrorDirection {
    Up,   // Parent's requirement did this
    Down, // Child/self didn't match
}

#[derive(Clone, Debug)]
struct TypeError {
    position: usize,
    code: String,
    direction: TypeErrorDirection,
    param_expected: Option<Vec<ExprType>>,
    param_found: Option<ExprType>,
    param_position: usize,
    my_type: Option<ExprType>,
    my_expected_type: Option<Vec<ExprType>>,
    explanation: &'static str,
    because: Option<Box<TypeError>>,
}

impl TypeError {
    fn for_node(node: &AstNode, expected_type: Option<&[ExprType]>) -> Self {
        TypeError {
            position: node.position,
            code: node.code.to_owned(),
            direction: TypeErrorDirection::Up,
            param_expected: None,
            param_found: None,
            param_position: 0,
            my_type: None,
            my_expected_type: expected_type.map(|v| v.iter().unique().cloned().collect()),
            explanation: "Expression type mismatch",
            because: None,
        }
    }

    fn wrong_param(
        mut self,
        position: usize,
        expected: Option<&[ExprType]>,
        found: Option<ExprType>,
    ) -> Self {
        self.param_position = position;
        self.param_expected = expected.map(|v| v.iter().unique().cloned().collect());
        self.param_found = found;
        self
    }

    fn down(mut self) -> Self {
        self.direction = TypeErrorDirection::Down;
        self
    }

    fn my_type(mut self, real: Option<ExprType>) -> Self {
        self.my_type = real;
        self
    }

    fn map_up(self, f: impl Fn(&TypeError) -> TypeError) -> TypeError {
        match self.direction {
            TypeErrorDirection::Up => {
                let mut v = f(&self);
                v.because = Some(Box::new(self));
                v
            }
            TypeErrorDirection::Down => self,
        }
    }

    fn create_map_up(
        f: impl Fn(&TypeError) -> TypeError,
    ) -> impl FnOnce(Box<TypeError>) -> TypeError {
        move |e| e.map_up(f)
    }
}

#[derive(Clone, Debug, PartialEq)]
struct AstNode<'a> {
    expr: AstExpr,
    position: usize,
    code: &'a str,
}

impl<'a> AstNode<'a> {
    fn print(&self, store: &AstStore, level: usize) -> String {
        use AstExpr::*;
        let t = self
            .expr_type(store, None)
            .map(|x| format!("{:?}", x))
            .ok()
            .unwrap_or_else(|| "!".into());
        match &self.expr {
            Constant(c) => format!("{}{:?}", "  ".repeat(level), c),
            Add(l, r) => format!(
                "{}Add<{}>(\n{},\n{})",
                "  ".repeat(level),
                t,
                store.get(*l).print(store, level + 1),
                store.get(*r).print(store, level + 1)
            ),
            Print(v) => format!(
                "{}Print<{}>(\n{})",
                "  ".repeat(level),
                t,
                store.get(*v).print(store, level + 1),
            ),
            ReadLine => format!("{}ReadLine", "  ".repeat(level),),
            If(c, l, r) => format!(
                "{}If<{}>(\n{},\n{},\n{})",
                "  ".repeat(level),
                t,
                store.get(*c).print(store, level + 1),
                store.get(*l).print(store, level + 1),
                store.get(*r).print(store, level + 1)
            ),
            Compare(o, l, r) => format!(
                "{}Compare[{:?}]<{}>(\n{},\n{})",
                "  ".repeat(level),
                o,
                t,
                store.get(*l).print(store, level + 1),
                store.get(*r).print(store, level + 1)
            ),
            Repeat(c, b) => format!(
                "{}Repeat(\n{},\n{})",
                "  ".repeat(level),
                store.get(*c).print(store, level + 1),
                store.get(*b).print(store, level + 1)
            ),
        }
    }

    fn expr_type(
        &self,
        store: &AstStore,
        read_as: Option<&[ExprType]>,
    ) -> Result<ExprType, Box<TypeError>> {
        use AstExpr::*;
        match &self.expr {
            Constant(c) => {
                let t = c.expr_type();
                if catch! { read_as?.contains(&t) } == Some(false) {
                    return Err(TypeError {
                        my_type: Some(t),
                        ..TypeError::for_node(self, read_as)
                    }
                    .into());
                }
                Ok(t)
            }
            Add(l, r) => {
                let allowv = read_as
                    .unwrap_or(&[ExprType::Int, ExprType::String, ExprType::Bool])
                    .iter()
                    .filter(|x| **x != ExprType::Void)
                    .cloned()
                    .collect::<Vec<_>>();
                let allow = Some(&allowv[..]);
                let lt =
                    store
                        .get(*l)
                        .expr_type(store, allow)
                        .map_err(TypeError::create_map_up(|e| {
                            TypeError::for_node(self, read_as).wrong_param(0, allow, e.my_type)
                        }))?;
                let rtarget = if allowv.contains(&ExprType::String) {
                    [lt, ExprType::String]
                } else {
                    [lt, lt]
                };
                let rt =
                    store
                        .get(*r)
                        .expr_type(store, allow)
                        .map_err(TypeError::create_map_up(|e| {
                            TypeError::for_node(self, read_as).wrong_param(1, allow, e.my_type)
                        }))?;
                if lt == ExprType::String || rt == ExprType::String {
                    Ok(ExprType::String)
                } else {
                    store.get(*r).expr_type(store, Some(&rtarget)).map_err(
                        TypeError::create_map_up(|e| {
                            TypeError::for_node(self, read_as)
                                .wrong_param(1, Some(&rtarget), e.my_type)
                                .down()
                        }),
                    )?;
                    Ok(lt)
                }
            }
            Print(value) => store.get(*value).expr_type(store, read_as),
            ReadLine => {
                if catch! { read_as?.contains(&ExprType::String) } == Some(false) {
                    return Err(TypeError::for_node(self, read_as)
                        .my_type(Some(ExprType::String))
                        .into());
                }
                Ok(ExprType::String)
            }
            If(c, t, e) => {
                store
                    .get(*c)
                    .expr_type(store, Some(&[ExprType::Bool]))
                    .map_err(TypeError::create_map_up(|e| {
                        TypeError::for_node(self, read_as)
                            .wrong_param(0, Some(&[ExprType::Bool]), e.my_type)
                            .down()
                    }))?;
                let tt =
                    store
                        .get(*t)
                        .expr_type(store, read_as)
                        .map_err(TypeError::create_map_up(|e| {
                            TypeError::for_node(self, read_as)
                                .wrong_param(0, read_as, e.my_type)
                                .down()
                        }))?;
                store
                    .get(*e)
                    .expr_type(store, Some(&[tt]))
                    .map_err(TypeError::create_map_up(|e| TypeError {
                        direction: if read_as.is_some() {
                            TypeErrorDirection::Up
                        } else {
                            TypeErrorDirection::Down
                        },
                        ..TypeError::for_node(self, read_as)
                            .wrong_param(2, read_as, e.my_type)
                            .my_type(e.my_type)
                    }))?;
                Ok(tt)
            }
            Compare(o, l, r) => {
                if catch! { read_as?.contains(&ExprType::Bool) } == Some(false) {
                    return Err(TypeError::for_node(self, read_as)
                        .my_type(Some(ExprType::Bool))
                        .into());
                }
                let target: &[ExprType] = if *o == Ordering::Equal {
                    &[ExprType::Bool, ExprType::Int, ExprType::String]
                } else {
                    &[ExprType::Int]
                };
                let lt = store.get(*l).expr_type(store, Some(target)).map_err(
                    TypeError::create_map_up(|e| {
                        TypeError::for_node(self, read_as)
                            .wrong_param(0, Some(target), e.my_type)
                            .my_type(Some(ExprType::Bool))
                            .down()
                    }),
                )?;
                store
                    .get(*r)
                    .expr_type(store, Some(&[lt]))
                    .map_err(TypeError::create_map_up(|e| {
                        TypeError::for_node(self, read_as)
                            .wrong_param(1, Some(&[lt]), e.my_type)
                            .my_type(Some(ExprType::Bool))
                            .down()
                    }))?;
                match lt {
                    ExprType::Int => Ok(ExprType::Bool),
                    ExprType::String | ExprType::Bool => Ok(ExprType::Bool),
                    ExprType::Void => unreachable!("Void type"),
                }
            }
            Repeat(c, b) => {
                if catch! { read_as?.contains(&ExprType::Void) } == Some(false) {
                    return Err(TypeError::for_node(self, read_as)
                        .my_type(Some(ExprType::Void))
                        .into());
                }
                store
                    .get(*c)
                    .expr_type(store, Some(&[ExprType::Int]))
                    .map_err(TypeError::create_map_up(|e| {
                        TypeError::for_node(self, read_as)
                            .wrong_param(0, Some(&[ExprType::Int]), e.my_type)
                            .my_type(Some(ExprType::Void))
                            .down()
                    }))?;
                store
                    .get(*b)
                    .expr_type(store, None)
                    .map_err(TypeError::create_map_up(|e| {
                        TypeError::for_node(self, read_as)
                            .wrong_param(1, None, e.my_type)
                            .my_type(Some(ExprType::Bool))
                            .down()
                    }))?;
                Ok(ExprType::Void)
            }
        }
    }
}

struct ParserContext<'a> {
    builtins: Vec<ExprDecl>,
    code: &'a str,
    code_iter: std::cell::RefCell<std::iter::Peekable<CharIndices<'a>>>,
}

#[derive(Clone, Debug)]
struct Parser<'a> {
    ast_store: AstStore<'a>,
}

#[derive(Clone, Debug, PartialEq)]
enum ParseErrorReason {
    UnknownSymbol(char),
    UnknownShape,
    End,
}

#[derive(Clone, Debug, PartialEq)]
struct ParseError {
    reason: ParseErrorReason,
    position: Option<usize>,
}

type ParseResult<T> = Result<T, ParseError>;

impl<'a> ParserContext<'a> {
    fn new(builtins: Vec<ExprDecl>, code: &'a str) -> Self {
        ParserContext {
            builtins,
            code,
            code_iter: std::cell::RefCell::new(code.char_indices().peekable()),
        }
    }

    fn next_symbol(&self) -> ParseResult<&ExprDecl> {
        let (pos, symbol) = self.next_char()?;
        self.builtins
            .iter()
            .find(|x| x.symbol == symbol)
            .ok_or_else(|| ParseError {
                reason: ParseErrorReason::UnknownSymbol(symbol),
                position: Some(pos),
            })
    }

    fn peek_char(&self) -> ParseResult<(usize, char)> {
        self.code_iter
            .borrow_mut()
            .peek()
            .cloned()
            .ok_or_else(|| ParseError {
                reason: ParseErrorReason::End,
                position: None,
            })
    }

    fn next_char(&self) -> ParseResult<(usize, char)> {
        self.code_iter
            .borrow_mut()
            .next()
            .ok_or_else(|| ParseError {
                reason: ParseErrorReason::End,
                position: None,
            })
    }
}

impl<'a> Parser<'a> {
    fn new() -> Self {
        Parser {
            ast_store: AstStore::new(),
        }
    }

    fn read_all_expressions(&mut self, context: &ParserContext<'a>) -> ParseResult<Vec<AstKey>> {
        let mut res = Vec::new();
        'top: loop {
            loop {
                let c = context.peek_char();
                match c {
                    Ok((_, c)) => {
                        if c.is_whitespace() {
                            context.next_char()?;
                        } else {
                            break;
                        }
                    }
                    Err(_) => {
                        break 'top;
                    }
                }
            }

            res.push(self.read_expr(context)?);
        }
        Ok(res)
    }

    fn read_expr(&mut self, context: &ParserContext<'a>) -> ParseResult<AstKey> {
        while context.peek_char()?.1.is_whitespace() {
            context.next_char()?;
        }
        if context.peek_char()?.1 == '"' {
            return self.read_string(context);
        }
        if context.peek_char()?.1.is_ascii_digit() {
            return self.read_integer(context);
        }

        let start = context.peek_char()?.0;
        let decl = context.next_symbol()?;
        let mut slots_read = Vec::new();

        // Once more slot types exist, this'll loop.
        #[allow(clippy::never_loop)]
        for shape in &decl.shapes {
            for (_slot_idx, slot) in shape.slots.iter().enumerate() {
                match slot {
                    ExprSlot::Value { .. } => {
                        slots_read.push(self.read_expr(context)?);
                    }
                }
            }

            let end = context
                .peek_char()
                .map(|x| x.0)
                .unwrap_or_else(|_| context.code.len());

            let node = AstNode {
                expr: (shape.build_expr)(&self.ast_store, &slots_read),
                position: start,
                code: &context.code[start..end],
            };
            // println!("{:?}", node);
            return Ok(self.ast_store.insert(node));
        }

        Err(ParseError {
            reason: ParseErrorReason::UnknownShape,
            position: Some(start),
        })
    }

    fn read_integer(&mut self, context: &ParserContext<'a>) -> ParseResult<AstKey> {
        let mut result = 0i64;
        let start = context.peek_char()?.0;
        let mut end = None;
        while let Ok((idx, c)) = context.peek_char() {
            let digit = match c.to_digit(10) {
                Some(d) => d,
                None => {
                    end = Some(idx);
                    break;
                }
            };
            context.next_char()?;
            result = result * 10 + i64::from(digit);
        }
        let node = AstNode {
            expr: AstExpr::Constant(Value::Int(result)),
            position: start,
            code: &context.code[start..end.unwrap_or_else(|| context.code.len())],
        };
        // println!("{:?}", node);
        Ok(self.ast_store.insert(node))
    }

    fn read_string(&mut self, context: &ParserContext<'a>) -> ParseResult<AstKey> {
        let mut result = String::new();
        let start = context.peek_char()?.0;
        let mut end = None;
        context.next_char()?;
        while let Ok((idx, mut c)) = context.peek_char() {
            context.next_char()?;
            if c == '"' {
                end = Some(idx + 1);
                break;
            };
            if c == '\\' {
                c = context.next_char()?.1;
                if c == 'n' {
                    c = '\n';
                }
            }
            result.push(c);
        }
        let node = AstNode {
            expr: AstExpr::Constant(Value::String(Rc::new(result))),
            position: start,
            code: &context.code[start..end.unwrap_or_else(|| context.code.len())],
        };
        // println!("{:?}", node);
        Ok(self.ast_store.insert(node))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ValueType {
    Int,
    String,
    Bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Instruction {
    LoadConstant(Value),
    Add(ValueType),
    Sub(ValueType),
    ToString(ValueType),
    Print(ValueType),
    Copy(ValueType),
    Drop(ValueType),
    ReadLine,
    CompareZero(Ordering),
    CompareEqual(ValueType),
    CondJump(usize, bool),
    Jump(usize),
    Halt,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BBJump {
    Halt,
    Jump(usize),
    Branch(usize, usize), // on_true, on_false
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BasicBlock {
    end: BBJump,
    instructions: Vec<Instruction>,
    position: Option<usize>,
}

impl BasicBlock {
    fn new() -> Self {
        BasicBlock {
            end: BBJump::Halt,
            instructions: Vec::new(),
            position: None,
        }
    }
}

#[derive(Clone, Debug)]
struct BasicBlockBuilder {
    blocks: Vec<BasicBlock>,
    curremt_block: usize,
}

impl BasicBlockBuilder {
    fn new() -> Self {
        BasicBlockBuilder {
            blocks: vec![BasicBlock::new()],
            curremt_block: 0,
        }
    }

    fn push(&mut self, ins: Instruction) -> usize {
        let block = &mut self.blocks[self.curremt_block];
        block.instructions.push(ins);
        block.instructions.len() - 1
    }

    fn new_block(&mut self) -> usize {
        if self.blocks[self.curremt_block].end == BBJump::Halt {
            self.set_target(BBJump::Jump(self.blocks.len()));
        }
        self.blocks.push(BasicBlock::new());
        self.curremt_block = self.blocks.len() - 1;
        self.curremt_block
    }

    fn set_target(&mut self, jump: BBJump) {
        self.blocks[self.curremt_block].end = jump;
    }

    fn build_statement(
        &mut self,
        store: &AstStore,
        node: AstKey,
    ) -> Result<ExprType, Box<TypeError>> {
        store.get(node).expr_type(
            store,
            Some(&[
                ExprType::Bool,
                ExprType::Int,
                ExprType::String,
                ExprType::Void,
            ]),
        )?;
        let t = self.build_instructions(store, node)?;
        if t != ExprType::Void {
            self.push(Instruction::Drop(t.into_value_type()));
        }
        Ok(t)
    }

    fn build_instructions(
        &mut self,
        store: &AstStore,
        node: AstKey,
    ) -> Result<ExprType, Box<TypeError>> {
        use Instruction::*;
        let expr = store.get(node);
        Ok(match &expr.expr {
            AstExpr::Constant(v) => {
                self.push(LoadConstant(v.clone()));
                v.expr_type()
            }
            AstExpr::Add(l, r) => {
                let r_type = expr.expr_type(store, None)?;
                let is_string = r_type == ExprType::String;

                let lt = self.build_instructions(store, *l)?;
                if is_string && lt == ExprType::Int {
                    self.push(ToString(ValueType::Int));
                }
                if is_string && lt == ExprType::Bool {
                    self.push(ToString(ValueType::Bool));
                }

                let rt = self.build_instructions(store, *r)?;
                if is_string && rt == ExprType::Int {
                    self.push(ToString(ValueType::Int));
                }
                if is_string && rt == ExprType::Bool {
                    self.push(ToString(ValueType::Bool));
                }

                self.push(Add(r_type.into_value_type()));
                r_type
            }
            AstExpr::Print(v) => {
                let t = self.build_instructions(store, *v)?;
                // This likely requires special handling for future types
                match t {
                    ExprType::Int => {
                        self.push(Print(ValueType::Int));
                    }
                    ExprType::Bool => {
                        self.push(Print(ValueType::Bool));
                    }
                    ExprType::String => {
                        self.push(Print(ValueType::String));
                    }
                    ExprType::Void => {
                        unreachable!("Void value");
                    }
                }
                t
            }
            AstExpr::ReadLine => {
                self.push(ReadLine);
                ExprType::String
            }
            AstExpr::If(c, l, r) => {
                let r_type = expr.expr_type(store, None)?;

                self.build_instructions(store, *c)?;
                let start_block = self.curremt_block;

                let then_block = self.new_block();
                self.build_instructions(store, *l)?;
                let after_then_block = self.curremt_block;

                let else_block = self.new_block();
                self.build_instructions(store, *r)?;
                let end = self.new_block();

                self.blocks[start_block].end = BBJump::Branch(then_block, else_block);
                self.blocks[after_then_block].end = BBJump::Jump(end);

                r_type
            }
            AstExpr::Compare(o, l, r) => {
                self.build_instructions(store, *l)?;
                let rt = self.build_instructions(store, *r)?;
                if *o == Ordering::Equal {
                    self.push(CompareEqual(rt.into_value_type()));
                } else if rt == ExprType::Int {
                    self.push(Sub(ValueType::Int));
                    self.push(CompareZero(*o));
                }
                ExprType::Bool
            }
            AstExpr::Repeat(c, b) => {
                self.build_instructions(store, *c)?;

                let start = self.new_block();
                self.push(LoadConstant(Value::Int(1)));
                self.push(Sub(ValueType::Int));
                self.push(Copy(ValueType::Int));
                self.push(CompareZero(Ordering::Less));

                let loop_body = self.new_block();

                let t = self.build_instructions(store, *b)?;
                if t != ExprType::Void {
                    self.push(Drop(t.into_value_type()));
                }
                let after_loop_body = self.curremt_block;

                let end = self.new_block();
                self.push(Drop(ValueType::Int));

                self.blocks[start].end = BBJump::Branch(end, loop_body);
                self.blocks[after_loop_body].end = BBJump::Jump(start);
                ExprType::Void
            }
        })
    }
}

#[derive(Clone, Debug, Default)]
struct ControlFlowNode {
    to: Vec<usize>,
    from: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
struct ControlFlowGraph {
    nodes: Vec<ControlFlowNode>,
}

impl ControlFlowNode {
    fn new() -> Self {
        ControlFlowNode {
            from: Vec::with_capacity(10),
            to: Vec::with_capacity(2),
        }
    }
}

impl ControlFlowGraph {
    fn for_blocks(blocks: &[BasicBlock]) -> Self {
        let mut graph = ControlFlowGraph {
            nodes: blocks.iter().map(|_| ControlFlowNode::new()).collect(),
        };

        for (i, block) in blocks.iter().enumerate() {
            match block.end {
                BBJump::Jump(target) => {
                    graph.nodes[target].from.push(i);
                    graph.nodes[i].to.push(target);
                }
                BBJump::Branch(true_target, false_target) => {
                    graph.nodes[true_target].from.push(i);
                    graph.nodes[i].to.push(true_target);
                    graph.nodes[false_target].from.push(i);
                    graph.nodes[i].to.push(false_target);
                }
                BBJump::Halt => {}
            }
        }

        graph
    }

    fn dominance_ordering(&self) -> Vec<usize> {
        let mut ordering = Vec::new();
        let mut seen = Vec::new();

        let mut stack = vec![self.nodes.len() - 1];
        while let Some(block_idx) = stack.pop() {
            let mut pushed = false;
            for from in self.nodes[block_idx].from.iter().rev() {
                if !seen.contains(from) {
                    if !pushed {
                        stack.push(block_idx);
                        pushed = true;
                    }
                    seen.push(*from);
                    stack.push(*from);
                }
            }

            if !pushed {
                // for to in self.nodes[block_idx].to.iter() {
                //     if !seen.contains(to) {
                //         seen.push(*to);
                //         stack.push(*to);
                //     }
                // }
                ordering.push(block_idx);
            }
        }

        ordering
    }
}

fn remove_duplicates(blocks: &mut Vec<BasicBlock>) {
    let mut idx = 0usize;
    while idx < blocks.len() {
        let is_dup_with = (idx + 1..blocks.len()).find(|i| blocks[idx] == blocks[*i]);
        if let Some(other) = is_dup_with {
            blocks.remove(idx);
            reassign_blocks(blocks, idx, other);
        } else {
            idx += 1;
        }
    }
}

fn remove_empty(blocks: &mut Vec<BasicBlock>) {
    let mut idx = 0usize;
    while idx < blocks.len() {
        if let (0, BBJump::Jump(target)) = (blocks[idx].instructions.len(), blocks[idx].end) {
            blocks.remove(idx);
            reassign_blocks(blocks, idx, target);
        } else {
            idx += 1;
        }
    }
}

fn reassign_blocks(blocks: &mut Vec<BasicBlock>, original: usize, new: usize) {
    let reassign = |t: &mut usize| {
        if *t == original {
            *t = new;
        }
        if *t >= original {
            *t -= 1;
        }
    };

    for block in blocks.iter_mut() {
        match &mut block.end {
            BBJump::Jump(t) => {
                reassign(t);
            }
            BBJump::Branch(t, e) => {
                reassign(t);
                reassign(e);
            }
            BBJump::Halt => {}
        }
    }
}

struct InstructionSetBuilder {
    blocks: Vec<BasicBlock>,
    result: Vec<Instruction>,
}

impl InstructionSetBuilder {
    fn from_bb(blocks: Vec<BasicBlock>) -> Self {
        InstructionSetBuilder {
            blocks,
            result: Vec::new(),
        }
    }

    fn into_instructions(mut self) -> Vec<Instruction> {
        let ordering = ControlFlowGraph::for_blocks(&self.blocks).dominance_ordering();
        for block_idx in ordering {
            if self.block_position(block_idx).is_some() {
                continue;
            }

            self.build_block(block_idx);

            match self.blocks[block_idx].end {
                BBJump::Halt => {
                    self.result.push(Instruction::Halt);
                }
                BBJump::Jump(bidx) => {
                    self.result.push(Instruction::Jump(bidx));
                }
                BBJump::Branch(t_idx, f_idx) => {
                    self.result.push(Instruction::CondJump(f_idx, false));
                    self.result.push(Instruction::Jump(t_idx));
                }
            }
        }

        for inst in self.result.iter_mut() {
            match inst {
                Instruction::CondJump(target, _) => {
                    *target = self.blocks[*target].position.unwrap();
                }
                Instruction::Jump(target) => {
                    *target = self.blocks[*target].position.unwrap();
                }
                _ => {}
            }
        }

        let mut idx = 0usize;
        while idx < self.result.len() {
            let fix = match &self.result[idx] {
                Instruction::CondJump(t, _) | Instruction::Jump(t) => *t == idx + 1,
                _ => false,
            };
            if fix {
                self.result.remove(idx);
                for inst in self.result.iter_mut() {
                    match inst {
                        Instruction::CondJump(t, _) | Instruction::Jump(t) => {
                            if *t > idx {
                                *t -= 1;
                            }
                        }
                        _ => {}
                    }
                }
            } else {
                idx += 1;
            }
        }

        self.result
    }

    fn block_position(&self, block_idx: usize) -> Option<usize> {
        self.blocks[block_idx].position
    }

    fn build_block(&mut self, block_idx: usize) -> usize {
        if let Some(pos) = self.block_position(block_idx) {
            return pos;
        }

        let block = &mut self.blocks[block_idx];
        let pos = self.result.len();
        block.position = Some(pos);
        for inst in block.instructions.drain(..) {
            self.result.push(inst);
        }

        pos
    }
}

trait ValueCheck {
    fn on_miss() -> !;
}
#[allow(dead_code)]
struct UncheckedValues;
#[allow(dead_code)]
struct CheckedValues;
impl ValueCheck for UncheckedValues {
    fn on_miss() -> ! {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
impl ValueCheck for CheckedValues {
    fn on_miss() -> ! {
        unreachable!("Value check");
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
struct VMFrame<Check> {
    val_stack: VMStack<Check>,
    execution_pointer: usize,
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
struct VMStack<Check> {
    int_values: Vec<i64>,
    string_values: Vec<Rc<String>>,
    bool_values: Vec<bool>,
    _check: PhantomData<fn(&Check) -> ()>,
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
struct VM<Check> {
    instructions: Vec<Instruction>,
    val_stack: VMStack<Check>,
    execution_pointer: usize,
    stack_frames: Vec<VMFrame<Check>>,
    instruction_counter: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum VMStep {
    Ok,
    End,
}

#[derive(Debug)]
enum VMError {
    TypeError(Box<TypeError>),
    IO(std::io::Error),
}

impl From<std::io::Error> for Box<VMError> {
    fn from(v: std::io::Error) -> Self {
        Box::new(VMError::IO(v))
    }
}

impl From<Box<TypeError>> for Box<VMError> {
    fn from(v: Box<TypeError>) -> Self {
        Box::new(VMError::TypeError(v))
    }
}

type VMResult<T> = Result<T, Box<VMError>>;

macro_rules! vm_values {
    (
        $(
            $type:ty: $stack:tt
            $(pop $pop:block)?
            $(push $push:block)?
            $(peek_mut $peekmut:block)?
         ),*
    ) => {
$(
impl<C> VMPop<C> for $type where C: ValueCheck {
    #[inline(always)]
    fn peek(stack: &VMStack<C>) -> &Self {
        stack.$stack.last().unwrap_or_else(|| C::on_miss())
    }

    #[inline(always)]
    fn peek_mut(stack: &mut VMStack<C>) -> &mut Self {
        #![allow(unused_parens)]
        $(($peekmut))?(stack.$stack.last_mut().unwrap_or_else(|| C::on_miss()))
    }

    #[inline(always)]
    fn pop(stack: &mut VMStack<C>) -> Self {
        #![allow(unused_parens)]
        $(($pop))?(stack.$stack.pop().unwrap_or_else(|| C::on_miss()))
    }

    #[inline(always)]
    fn push(stack: &mut VMStack<C>, val: Self) {
        #![allow(unused_parens)]
        stack.$stack.push($(($push))?(val));
    }
}
)*
    };
}

trait VMPop<Check>: Sized
where
    Check: ValueCheck,
{
    fn peek(stack: &VMStack<Check>) -> &Self;
    fn peek_mut(stack: &mut VMStack<Check>) -> &mut Self;
    fn pop(stack: &mut VMStack<Check>) -> Self;
    fn push(stack: &mut VMStack<Check>, val: Self);
}

vm_values! {
    String: string_values
        pop { |v: Rc<String>| Rc::try_unwrap(v).unwrap_or_else(|v| (&*v).clone()) }
        push { |v| Rc::new(v) }
        peek_mut { |v| Rc::make_mut(v) },
    Rc<String>: string_values,
    i64: int_values,
    bool: bool_values
}

impl<Check> VMStack<Check>
where
    Check: ValueCheck,
{
    #[inline(always)]
    fn peek<T>(&self) -> &T
    where
        T: VMPop<Check>,
    {
        T::peek(self)
    }

    #[allow(dead_code)]
    #[inline(always)]
    fn peek_mut<T>(&mut self) -> &mut T
    where
        T: VMPop<Check>,
    {
        T::peek_mut(self)
    }

    #[inline(always)]
    fn pop<T>(&mut self) -> T
    where
        T: VMPop<Check>,
    {
        T::pop(self)
    }

    #[inline(always)]
    fn push<T>(&mut self, val: T)
    where
        T: VMPop<Check>,
    {
        T::push(self, val)
    }
}

macro_rules! vm_for_all {
    (#type $t:expr,
     $(#stack $stack:ident,
       $(#pop $pop:pat,)?
       $(#peek $peek:ident,)?
     )?
     $thing:block) => {
        match $t {
            ValueType::Int => {
                $(let stack = &mut *$stack;
                  $(let $pop = stack.pop::<i64>();)?
                  $(let $peek = stack.peek::<i64>();)?
                )?
                $thing
            },
            ValueType::Bool => {
                $(let stack = &mut *$stack;
                  $(let $pop = stack.pop::<bool>();)?
                  $(let $peek = stack.peek::<bool>();)?
                )?
                $thing
            },
            ValueType::String => {
                $(let stack = &mut *$stack;
                  $(let $pop = stack.pop::<Rc<String>>();)?
                  $(let $peek = stack.peek::<Rc<String>>();)?
                )?
                $thing
            },
        }
    };
    (#value $v:ident, $thing:block) => {
        match $v {
            Value::Int($v) => {$thing},
            Value::Bool($v) => {$thing},
            Value::String($v) => {$thing},
        }
    };
}

impl<Check> VM<Check>
where
    Check: ValueCheck,
{
    fn new(instructions: Vec<Instruction>) -> Self {
        VM {
            instructions,
            val_stack: VMStack {
                int_values: Vec::with_capacity(1024),
                string_values: Vec::with_capacity(1024),
                bool_values: Vec::with_capacity(1024),
                _check: PhantomData,
            },
            execution_pointer: 0,
            stack_frames: Vec::new(),
            instruction_counter: 0,
        }
    }

    fn run(&mut self, trace: bool) -> VMResult<VMStep> {
        loop {
            let pos = self.execution_pointer;
            let r = self.step()?;
            if r != VMStep::Ok {
                return Ok(r);
            }
            if trace {
                self.stack_frames.push(VMFrame {
                    val_stack: self.val_stack.clone(),
                    execution_pointer: pos,
                });
            }
        }
    }

    #[inline(always)]
    fn step(&mut self) -> VMResult<VMStep> {
        #![allow(clippy::clone_on_copy)]
        type VMString = Rc<String>;

        let stack = &mut self.val_stack;

        let jump = match &self.instructions[self.execution_pointer..] {
            [Instruction::LoadConstant(Value::Int(v)), Instruction::Sub(ValueType::Int), ..] => {
                let a = stack.peek_mut::<i64>();
                *a -= v;
                2
            }
            [Instruction::Copy(ValueType::Int), Instruction::CompareZero(c), ..] => {
                let a = stack.peek::<i64>();
                let r = a.cmp(&0) == *c;
                stack.push(r);
                2
            }
            _ => 0,
        };

        if jump > 0 {
            self.instruction_counter += jump;
            self.execution_pointer += jump;
            return Ok(VMStep::Ok);
        }

        let instruction = &self
            .instructions
            .get(self.execution_pointer)
            .unwrap_or_else(|| Check::on_miss());

        self.execution_pointer += 1;
        self.instruction_counter += 1;

        match instruction {
            Instruction::LoadConstant(v) => vm_for_all!(#value v, { stack.push(v.clone()); }),
            Instruction::Add(t) => match t {
                ValueType::Int => {
                    let b = stack.pop::<i64>();
                    let a = stack.peek_mut::<i64>();
                    *a += b;
                }
                ValueType::String => {
                    let b = stack.pop::<VMString>();
                    let a = stack.peek_mut::<String>();
                    *a += &*b;
                }
                ValueType::Bool => {
                    let b = stack.pop::<bool>();
                    let a = stack.peek_mut::<bool>();
                    *a = *a || b;
                }
            },
            Instruction::Sub(t) => match t {
                ValueType::Int => {
                    let b = stack.pop::<i64>();
                    let a = stack.peek_mut::<i64>();
                    *a -= b;
                }
                ValueType::String => {
                    unreachable!("Sub(String)");
                }
                ValueType::Bool => {
                    unreachable!("Sub(Bool)");
                }
            },
            Instruction::ToString(t) => vm_for_all!(#type t, #stack stack, #pop v, { stack.push(v.to_string()); }),
            Instruction::Print(t) => vm_for_all!(#type t, #stack stack, #peek v, { print!("{}", v); }),
            Instruction::Copy(t) => vm_for_all!(#type t, #stack stack, #peek v, { let v = v.clone(); stack.push(v); }),
            Instruction::Drop(t) => vm_for_all!(#type t, #stack stack, #pop _, { }),
            Instruction::ReadLine => {
                use std::io::Write;
                let mut buf = String::new();
                std::io::stdout().flush()?;
                std::io::stdin().read_line(&mut buf)?;
                buf = buf.trim_end_matches(|c| c == '\r' || c == '\n').into();
                stack.push(buf);
            }
            Instruction::CompareEqual(k) => match k {
                ValueType::Int => {
                    let b: i64 = stack.pop();
                    let a: i64 = stack.pop();
                    stack.push(a == b);
                }
                ValueType::String => {
                    let b: VMString = stack.pop();
                    let a: VMString = stack.pop();
                    stack.push(a == b);
                }
                ValueType::Bool => {
                    let b: bool = stack.pop();
                    let a = stack.peek_mut::<bool>();
                    *a = *a == b;
                }
            },
            Instruction::CompareZero(c) => {
                let a: i64 = stack.pop();
                stack.push(a.cmp(&0) == *c);
            }
            Instruction::CondJump(target, truthy) => {
                let c: bool = stack.pop();
                if c == *truthy {
                    self.execution_pointer = *target;
                }
            }
            Instruction::Jump(target) => {
                self.execution_pointer = *target;
            }
            Instruction::Halt => {
                return Ok(VMStep::End);
            }
        }

        Ok(VMStep::Ok)
    }
}

fn measure<T>(f: impl FnOnce() -> T) -> (T, std::time::Duration) {
    let start = std::time::Instant::now();
    let v = test::black_box(f());
    (v, start.elapsed())
}

fn main() {
    let builtins = vec![
        ExprDecl {
            name: "Add",
            symbol: '+',
            shapes: vec![ExprShape {
                slots: vec![ExprSlot::Value { name: "a" }, ExprSlot::Value { name: "b" }],
                build_expr: |_, k| AstExpr::Add(k[0], k[1]),
            }],
        },
        ExprDecl {
            name: "CompareLT",
            symbol: '<',
            shapes: vec![ExprShape {
                slots: vec![ExprSlot::Value { name: "a" }, ExprSlot::Value { name: "b" }],
                build_expr: |_, k| AstExpr::Compare(Ordering::Less, k[0], k[1]),
            }],
        },
        ExprDecl {
            name: "CompareGT",
            symbol: '>',
            shapes: vec![ExprShape {
                slots: vec![ExprSlot::Value { name: "a" }, ExprSlot::Value { name: "b" }],
                build_expr: |_, k| AstExpr::Compare(Ordering::Greater, k[0], k[1]),
            }],
        },
        ExprDecl {
            name: "CompareEqual",
            symbol: '=',
            shapes: vec![ExprShape {
                slots: vec![ExprSlot::Value { name: "a" }, ExprSlot::Value { name: "b" }],
                build_expr: |_, k| AstExpr::Compare(Ordering::Equal, k[0], k[1]),
            }],
        },
        ExprDecl {
            name: "Print",
            symbol: 'P',
            shapes: vec![ExprShape {
                slots: vec![ExprSlot::Value { name: "value" }],
                build_expr: |_, k| AstExpr::Print(k[0]),
            }],
        },
        ExprDecl {
            name: "ReadLine",
            symbol: 'R',
            shapes: vec![ExprShape {
                slots: vec![],
                build_expr: |_, _| AstExpr::ReadLine,
            }],
        },
        ExprDecl {
            name: "If",
            symbol: '?',
            shapes: vec![ExprShape {
                slots: vec![
                    ExprSlot::Value { name: "condition" },
                    ExprSlot::Value { name: "then" },
                    ExprSlot::Value { name: "else" },
                ],
                build_expr: |_, k| AstExpr::If(k[0], k[1], k[2]),
            }],
        },
        ExprDecl {
            name: "True",
            symbol: 't',
            shapes: vec![ExprShape {
                slots: vec![],
                build_expr: |_, _| AstExpr::Constant(Value::Bool(true)),
            }],
        },
        ExprDecl {
            name: "False",
            symbol: 'f',
            shapes: vec![ExprShape {
                slots: vec![],
                build_expr: |_, _| AstExpr::Constant(Value::Bool(false)),
            }],
        },
        ExprDecl {
            name: "Repeat",
            symbol: '#',
            shapes: vec![ExprShape {
                slots: vec![
                    ExprSlot::Value { name: "count" },
                    ExprSlot::Value { name: "body" },
                ],
                build_expr: |_, k| AstExpr::Repeat(k[0], k[1]),
            }],
        },
    ];

    let mut parser = Parser::new();
    let code = std::env::args()
        .nth(1)
        .unwrap_or_else(|| r#"P"Hello, world""#.to_owned());
    let context = ParserContext::new(builtins, &code);

    let (res, total_time) = measure(|| -> VMResult<()> {
        let (keys, parsing_time) = measure(|| parser.read_all_expressions(&context));

        let keys = match keys {
            Ok(keys) => keys,
            Err(e) => {
                println!(
                    "Error at position {}",
                    if let Some(p) = e.position {
                        p.to_string()
                    } else {
                        "EOF".to_owned()
                    }
                );
                println!("  {:?}", e.reason);
                return Ok(());
            }
        };

        println!("Code: {}", code);
        println!("\nParsing duration: {} ns", parsing_time.as_nanos());
        println!(
            "Ast:\n{}\n",
            keys.iter()
                .map(|key| parser.ast_store.get(*key).print(&parser.ast_store, 0))
                .join("\n")
        );

        let (res, bb_build_time) = measure(|| -> Result<_, Box<TypeError>> {
            let mut blocks = BasicBlockBuilder::new();
            keys.iter()
                .try_for_each(|k| blocks.build_statement(&parser.ast_store, *k).map(|_| ()))?;
            Ok(blocks.blocks)
        });
        let mut blocks = res?;

        println!("BlockSet build duration: {} ns", bb_build_time.as_nanos());
        println!("BlockSet (unoptimized)");
        for (i, block) in blocks.iter().enumerate() {
            println!("  #{} -> {:?}", i, block.end);
            for ins in &block.instructions {
                println!("    {:?}", ins);
            }
        }

        let (_, optimize_time) = measure(|| {
            remove_duplicates(&mut blocks);
            remove_empty(&mut blocks);
        });

        println!(
            "BlockSet optimization duration: {} ns",
            optimize_time.as_nanos()
        );
        println!("BlockSet");
        for (i, block) in blocks.iter().enumerate() {
            println!("  #{} -> {:?}", i, block.end);
            for ins in &block.instructions {
                println!("    {:?}", ins);
            }
        }

        let (instructions, inst_build_time) =
            measure(move || InstructionSetBuilder::from_bb(blocks).into_instructions());

        println!(
            "InstructionSet build duration: {} ns",
            bb_build_time.as_nanos()
        );
        println!("InstructionSet");
        for (i, ins) in instructions.iter().enumerate() {
            println!("  {:04}: {:?}", i, ins);
        }

        println!("\nExecution:");
        let mut vm = VM::<UncheckedValues>::new(instructions);
        let (res, exec_time) = measure(|| {
            vm.run(
                std::env::args()
                    .nth(2)
                    .map(|x| x.chars().nth(0) == Some('y'))
                    .unwrap_or(false),
            )
        });
        res?;

        println!("\n\nTrace:");
        for frame in &vm.stack_frames {
            println!(
                "{: <3} {: <30} -> Int: {:?}, Bool: {:?}, String: {:?}",
                frame.execution_pointer,
                format!("{:?}", &vm.instructions[frame.execution_pointer]),
                frame.val_stack.int_values,
                frame.val_stack.bool_values,
                frame.val_stack.string_values,
            );
        }

        println!("\nInstructions executed:        {}", vm.instruction_counter);
        println!("Execution duration:           {} µs", exec_time.as_micros());
        println!(
            "Total duration (excl. debug): {} µs",
            parsing_time.as_micros()
                + bb_build_time.as_micros()
                + optimize_time.as_micros()
                + inst_build_time.as_micros()
                + exec_time.as_micros()
        );

        Ok(())
    });
    match res.map_err(|v| *v) {
        Ok(()) => {}
        Err(VMError::IO(e)) => {
            println!("IO error: {:?}", e);
        }
        Err(VMError::TypeError(e)) => {
            print_type_error(&code, &e);
        }
    }

    println!(
        "Total duration:               {} µs",
        total_time.as_micros()
    );
}

fn print_type_error(code: &str, e: &TypeError) {
    println!(
        "Type error in\n  {}\n  {}{}\n{}",
        code,
        " ".repeat(e.position),
        "^".repeat(e.code.len()),
        e.explanation,
    );
    if e.param_found.is_some()
        && !e
            .param_expected
            .iter()
            .zip(e.param_found.iter())
            .all(|(e, f)| e.contains(f))
    {
        println!(
            "Expected param {0}: {1}\nFound    param {0}: {2}",
            e.param_position,
            e.param_expected
                .iter()
                .map(|g| g.iter().map(|v| format!("{:?}", v)).join(" | "))
                .join(", "),
            e.param_found.iter().map(|v| format!("{:?}", v)).join(", ")
        );
    }
    if e.my_expected_type.is_some()
        && e.my_type.is_some()
        && !e
            .my_expected_type
            .as_ref()
            .unwrap()
            .contains(e.my_type.as_ref().unwrap())
    {
        println!(
            "Expected type: {}\nActual   type: {:?}",
            e.my_expected_type
                .as_ref()
                .unwrap()
                .iter()
                .map(|v| format!("{:?}", v))
                .join(" | "),
            e.my_type.as_ref().unwrap()
        );
    }
    if let Some(e) = &e.because {
        println!("\nCaused by:");
        print_type_error(code, e);
    }
}
