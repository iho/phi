use chumsky::prelude::*;
use crate::ast::*;
use crate::lexer::Token;

type Error = Simple<Token>;

pub fn parser() -> impl Parser<Token, Module, Error = Error> {
    let proper_id = filter_map(|span, tok| match tok {
        Token::ProperName(name) => Ok(name),
        _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
    });
    let var_id = filter_map(|span, tok| match tok {
        Token::VarIdent(name) => Ok(name),
        _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
    });
    let op_id = filter_map(|span, tok| match tok {
        Token::Operator(op) => Ok(op),
        _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
    });
    let parens_op = op_id.delimited_by(just(Token::LeftParen), just(Token::RightParen));
    let var_or_op = var_id.or(parens_op.clone());

    let qual_proper = proper_id.separated_by(just(Token::Dot)).at_least(1).map(|parts| parts.join("."));

    let type_ = type_parser();
    let binder = binder_parser(type_.clone());
    let expr = expr_parser(type_.clone(), binder.clone());
    let decl = decl_parser(type_.clone(), binder.clone(), expr.clone());

    let export = choice((
        just(Token::Module).ignore_then(qual_proper.clone()).map(Export::Module),
        just(Token::Class).ignore_then(qual_proper.clone()).map(Export::Class),
        qual_proper.clone().then(just(Token::LeftParen).ignore_then(choice((
            just(Token::TwoDots).to((None, true)),
            qual_proper.clone().separated_by(just(Token::Comma)).at_least(1).map(|cs| (Some(cs), false)),
            empty().to((Some(vec![]), false)),
        ))).then_ignore(just(Token::RightParen)).or_not()).map(|(n, res)| {
            let (cs, has_all) = res.unwrap_or((None, false));
            Export::Type(n, cs, has_all)
        }),
        var_or_op.clone().map(Export::Var),
    ));

    just(Token::Module)
        .ignore_then(qual_proper)
        .then(export.separated_by(just(Token::Comma)).delimited_by(just(Token::LeftParen), just(Token::RightParen)).or_not())
        .then_ignore(just(Token::Where))
        .then(decl.separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)))
        .map(|((name, exports), declarations)| Module {
            name,
            exports,
            declarations,
        })
        .then_ignore(end())
}

fn type_parser() -> impl Parser<Token, Type, Error = Error> + Clone {
    recursive(|type_| {
        let proper_id = filter_map(|span, tok| match tok {
            Token::ProperName(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let var_id = filter_map(|span, tok| match tok {
            Token::VarIdent(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });

        let qual_proper = proper_id.separated_by(just(Token::Dot)).at_least(1).map(|parts| parts.join("."));

        let record_field = var_id
            .then_ignore(just(Token::DoubleColon))
            .then(type_.clone())
            .map(|(name, ty)| Field { name: Some(name), ty });

        let atomic = choice((
            qual_proper.map(Type::Constructor),
            var_id.map(Type::Var),
            just(Token::Unit).to(Type::Unit),
            type_.clone()
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|t| Type::List(Box::new(t))),
            type_.clone()
                .separated_by(just(Token::Comma))
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .map(|ts: Vec<Type>| if ts.len() == 1 { ts[0].clone() } else { Type::Tuple(ts) }),
            record_field.separated_by(just(Token::Comma))
                .delimited_by(just(Token::LeftBrace), just(Token::RightBrace))
                .map(Type::Record),
        ));

        let app = atomic.clone()
            .then(atomic.repeated())
            .foldl(|f, a| Type::App(Box::new(f), Box::new(a)));

        let constrained = app.clone()
            .separated_by(just(Token::Comma))
            .delimited_by(just(Token::LeftParen), just(Token::RightParen))
            .or(app.clone().map(|t| vec![t]))
            .then_ignore(just(Token::DoubleArrow))
            .then(type_.clone())
            .map(|(cs, t)| Type::Constrained(cs, Box::new(t)));

        let forall = just(Token::Forall)
            .ignore_then(var_id.repeated().at_least(1))
            .then_ignore(just(Token::Dot))
            .then(type_.clone())
            .map(|(vars, t)| Type::Forall(vars, Box::new(t)));

        let arrow = app.clone()
            .then(just(Token::Arrow).ignore_then(type_.clone()).or_not())
            .map(|(dom, cod)| match cod {
                Some(c) => Type::Arrow(Box::new(dom), Box::new(c)),
                None => dom,
            });

        choice((forall, constrained, arrow))
    })
}

fn binder_parser(
    type_: impl Parser<Token, Type, Error = Error> + Clone + 'static,
) -> impl Parser<Token, Binder, Error = Error> + Clone {
    recursive(|binder| {
        let var_id = filter_map(|span, tok| match tok {
            Token::VarIdent(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let proper_id = filter_map(|span, tok| match tok {
            Token::ProperName(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let qual_proper = proper_id.separated_by(just(Token::Dot)).at_least(1).map(|parts| parts.join("."));

        let num = filter_map(|span, tok| match tok {
            Token::Number(n) => Ok(n),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let string = filter_map(|span, tok| match tok {
            Token::String(s) => Ok(s),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let char_ptr = filter_map(|span, tok| match tok {
            Token::Char(c) => Ok(c),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let atom = filter_map(|span, tok| match tok {
            Token::Atom(a) => Ok(a),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });

        let atomic = choice((
            var_id.map(Binder::Var),
            qual_proper.clone().map(|n| Binder::Constructor(n, vec![])),
            just(Token::Wildcard).to(Binder::Wildcard),
            num.map(Binder::Number),
            string.map(Binder::String),
            char_ptr.map(Binder::Char),
            atom.map(Binder::Atom),
            binder.clone()
                .separated_by(just(Token::Comma))
                .at_least(1)
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .map(|bs: Vec<Binder>| if bs.len() == 1 { bs[0].clone() } else { Binder::Tuple(bs) }),
            binder.clone()
                .separated_by(just(Token::Comma))
                .then(just(Token::Pipe).ignore_then(binder.clone()).or_not())
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|(bs, tail)| {
                     let mut res = bs;
                     if let Some(t) = tail {
                         res.push(t);
                         Binder::List(res)
                     } else {
                         Binder::List(res)
                     }
                }),
            just(Token::Operator("<<".to_string()))
                .ignore_then(binder.clone().separated_by(just(Token::Comma)))
                .then_ignore(just(Token::Operator(">>".to_string())))
                .map(Binder::Binary),
        ));

        let app = qual_proper.clone()
            .then(atomic.clone().repeated())
            .map(|(n, bs)| if bs.is_empty() { Binder::Constructor(n, vec![]) } else { Binder::Constructor(n, bs) })
            .or(atomic.clone());

        let named = var_id.then_ignore(just(Token::Operator("@".to_string()))).then(app.clone()).map(|(n, b)| Binder::Named(n, Box::new(b))).or(app);

        named.then(just(Token::DoubleColon).ignore_then(type_).or_not()).map(|(b, t)| match t {
            Some(ty) => Binder::TypeAnn(Box::new(b), ty),
            None => b,
        })
    })
}

fn expr_parser(
    type_: impl Parser<Token, Type, Error = Error> + Clone + 'static,
    binder: impl Parser<Token, Binder, Error = Error> + Clone + 'static,
) -> impl Parser<Token, Expr, Error = Error> + Clone {
    recursive(|expr| {
        let var_id = filter_map(|span, tok| match tok {
            Token::VarIdent(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let proper_id = filter_map(|span, tok| match tok {
            Token::ProperName(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let op_id = filter_map(|span, tok| match tok {
            Token::Operator(op) => Ok(op),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let parens_op = op_id.delimited_by(just(Token::LeftParen), just(Token::RightParen));
        
        let qual_var = proper_id.then_ignore(just(Token::Dot)).repeated().then(var_id).map(|(parts, name)| {
            if parts.is_empty() { name } else { format!("{}.{}", parts.join("."), name) }
        });
        let qual_proper = proper_id.separated_by(just(Token::Dot)).at_least(1).map(|parts| parts.join("."));
        let qual_var_or_op = qual_var.or(parens_op.clone());

        let num = filter_map(|span, tok| match tok {
            Token::Number(n) => Ok(n),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let float = filter_map(|span, tok| match tok {
            Token::Float(f) => Ok(f),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let string = filter_map(|span, tok| match tok {
            Token::String(s) => Ok(s),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let char_ptr = filter_map(|span, tok| match tok {
            Token::Char(c) => Ok(c),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let atom = filter_map(|span, tok| match tok {
            Token::Atom(a) => Ok(a),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });

        let decl = decl_parser(type_.clone(), binder.clone(), expr.clone());

        let record_field = var_id.then_ignore(just(Token::Equals)).then(expr.clone());

        let backtick_op = var_id.delimited_by(just(Token::Backtick), just(Token::Backtick));

        let comp_stmt = choice((
            binder.clone().then_ignore(just(Token::LeftArrow)).then(expr.clone()).map(|(p, e)| CompStmt::Bind(p, e)),
            just(Token::Let).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).map(CompStmt::Let),
            expr.clone().map(CompStmt::Guard),
        ));

        let atomic = choice((
            qual_var_or_op.clone().map(Expr::Var),
            qual_proper.clone().map(Expr::Var),
            num.map(Expr::Number),
            float.map(Expr::Float),
            string.map(Expr::String),
            char_ptr.map(Expr::Char),
            atom.map(Expr::Atom),
            just(Token::Unit).to(Expr::Unit),
            expr.clone()
                .separated_by(just(Token::Comma))
                .at_least(1)
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .map(|es: Vec<Expr>| if es.len() == 1 { es[0].clone() } else { Expr::Tuple(es) }),
            expr.clone()
                .then(just(Token::Pipe).ignore_then(comp_stmt.separated_by(just(Token::Comma))))
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|(head, stmts)| Expr::Comprehension(Box::new(head), stmts)),
            expr.clone()
                .then_ignore(just(Token::TwoDots))
                .then(expr.clone())
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|(start, end)| Expr::Range(Box::new(start), Box::new(end))),
            expr.clone()
                .separated_by(just(Token::Comma))
                .then(just(Token::Pipe).ignore_then(expr.clone()).or_not())
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|(es, tail)| Expr::List(es, tail.map(Box::new))),
            record_field.clone().separated_by(just(Token::Comma))
                .delimited_by(just(Token::LeftBrace), just(Token::RightBrace))
                .map(Expr::Record),
            expr.clone()
                .separated_by(just(Token::Comma))
                .delimited_by(just(Token::Operator("<<".to_string())), just(Token::Operator(">>".to_string())))
                .map(Expr::Binary),
        ));

        let lam = just(Token::Backslash)
            .ignore_then(binder.clone().repeated().at_least(1))
            .then_ignore(just(Token::Arrow))
            .then(expr.clone())
            .map(|(pats, body)| Expr::Lam(pats, Box::new(body)));

        let if_ = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Then))
            .then(expr.clone())
            .then_ignore(just(Token::Else))
            .then(expr.clone())
            .map(|((c, t), e)| Expr::If(Box::new(c), Box::new(t), Box::new(e)));

        let branch = binder.clone()
            .separated_by(just(Token::Comma))
            .then(just(Token::Pipe).ignore_then(expr.clone()).repeated())
            .then_ignore(just(Token::Arrow))
            .then(expr.clone())
            .map(|((binders, guards), body)| CaseBranch { binders, guards, body });

        let case = just(Token::Case)
            .ignore_then(expr.clone().separated_by(just(Token::Comma)))
            .then_ignore(just(Token::Of))
            .then(branch.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)))
            .map(|(es, bs)| Expr::Case(es, bs));

        let let_ = just(Token::Let)
            .ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)))
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|(ds, e)| Expr::Let(ds, Box::new(e)));

        let do_stmt = choice((
            binder.clone().then_ignore(just(Token::LeftArrow)).then(expr.clone()).map(|(p, e)| DoStatement::Bind(p, e)),
            just(Token::Let).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).map(DoStatement::Let),
            expr.clone().map(DoStatement::Expr),
        ));

        let do_ = just(Token::Do)
            .ignore_then(do_stmt.separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)))
            .map(Expr::Do);

        let receive = just(Token::Receive)
            .ignore_then(branch.separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)))
            .then(just(Token::After).ignore_then(expr.clone()).then_ignore(just(Token::Arrow)).then(expr.clone()).or_not())
            .map(|(branches, after)| Expr::Receive(branches, after.map(|(t, b)| Box::new(AfterClause { timeout: Box::new(t), body: b }))));

        let high_precedence_rhs = choice((lam.clone(), if_.clone(), case.clone(), let_.clone(), do_.clone(), receive.clone()));
        
        let app_arg = choice((atomic.clone(), high_precedence_rhs.clone()));

        let app = atomic.clone()
            .then(app_arg.repeated())
            .foldl(|f, a| Expr::App(Box::new(f), Box::new(a)));

        let negate = just(Token::Operator("-".to_string()))
            .ignore_then(app.clone())
            .map(|e| Expr::Negate(Box::new(e)))
            .or(app);

        let record_or_field = negate.clone()
            .then(choice((
                record_field.separated_by(just(Token::Comma)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)).map(|fs| (None, Some(fs))),
                just(Token::Dot).ignore_then(var_id).map(|v| (Some(v), None)),
            )).repeated())
            .foldl(|lhs, (v, fs)| match (v, fs) {
                (Some(v), _) => Expr::FieldAccess(Box::new(lhs), v),
                (_, Some(fs)) => Expr::RecordUpdate(Box::new(lhs), fs),
                _ => unreachable!(),
            });

        let binop = record_or_field.clone()
            .then(op_id.or(backtick_op).then(high_precedence_rhs.or(record_or_field.clone())).repeated())
            .foldl(|lhs, (op, rhs)| Expr::BinOp(Box::new(lhs), op, Box::new(rhs)));

        let type_ann = binop.clone().then(just(Token::DoubleColon).ignore_then(type_.clone()).or_not()).map(|(e, t)| match t {
            Some(t) => Expr::TypeAnn(Box::new(e), t),
            None => e,
        });

        choice((lam, if_, case, let_, do_, receive, type_ann))
    })
}

fn decl_parser(
    type_: impl Parser<Token, Type, Error = Error> + Clone + 'static,
    binder: impl Parser<Token, Binder, Error = Error> + Clone + 'static,
    expr: impl Parser<Token, Expr, Error = Error> + Clone + 'static,
) -> impl Parser<Token, Decl, Error = Error> + Clone {
    recursive(|decl| {
        let var_id = filter_map(|span, tok| match tok {
            Token::VarIdent(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let proper_id = filter_map(|span, tok| match tok {
            Token::ProperName(name) => Ok(name),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let op_id = filter_map(|span, tok| match tok {
            Token::Operator(op) => Ok(op),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let parens_op = op_id.delimited_by(just(Token::LeftParen), just(Token::RightParen));
        let var_or_op = var_id.or(parens_op.clone());
        let qual_proper = proper_id.separated_by(just(Token::Dot)).at_least(1).map(|parts| parts.join("."));
        let num = filter_map(|span, tok| match tok {
            Token::Number(n) => Ok(n),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });
        let string = filter_map(|span, tok| match tok {
            Token::String(s) => Ok(s),
            _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
        });

        let import_item = choice((
            just(Token::Class).ignore_then(qual_proper.clone()).map(ImportItem::Class),
            qual_proper.clone().then(just(Token::LeftParen).ignore_then(choice((
                just(Token::TwoDots).to((None, true)),
                qual_proper.clone().separated_by(just(Token::Comma)).at_least(1).map(|cs| (Some(cs), false)),
                empty().to((Some(vec![]), false)),
            ))).then_ignore(just(Token::RightParen)).or_not()).map(|(n, res)| {
                let (cs, has_all) = res.unwrap_or((None, false));
                ImportItem::Type(n, cs, has_all)
            }),
            var_or_op.clone().map(ImportItem::Var),
        ));

        let import = just(Token::Import)
            .ignore_then(qual_proper.clone())
            .then(import_item.clone().separated_by(just(Token::Comma)).delimited_by(just(Token::LeftParen), just(Token::RightParen)).or_not())
            .then(just(Token::Hiding).ignore_then(import_item.clone().separated_by(just(Token::Comma)).delimited_by(just(Token::LeftParen), just(Token::RightParen))).or_not())
            .then(just(Token::As).ignore_then(qual_proper.clone()).or_not())
            .map(|(((name, items), hiding), alias)| {
                let is_hiding = hiding.is_some();
                let actual_items = if is_hiding { hiding } else { items };
                Decl::Import(name, actual_items, alias, is_hiding)
            });

        let field = var_id.then_ignore(just(Token::DoubleColon)).or_not().then(type_.clone()).map(|(name, ty)| Field { name, ty });

        // Atomic type for positional constructor fields: a single constructor name, type variable,
        // list, tuple, or record type — without consuming adjacent types as type applications.
        // E.g. `Shutdown ExitReason st` → two fields: ExitReason and st (not App(ExitReason, st)).
        let atomic_type = choice((
            qual_proper.clone().map(Type::Constructor),
            var_id.clone().map(Type::Var),
            just(Token::Unit).to(Type::Unit),
            type_.clone()
                .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                .map(|t| Type::List(Box::new(t))),
            type_.clone()
                .separated_by(just(Token::Comma))
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .map(|ts: Vec<Type>| if ts.len() == 1 { ts[0].clone() } else { Type::Tuple(ts) }),
        ));
        let positional_field = atomic_type.map(|ty| Field { name: None, ty });

        let constructor = qual_proper.clone()
            .then(choice((
                field.clone().separated_by(just(Token::Comma)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace)),
                positional_field.repeated(),
            )))
            .map(|(name, fields)| Constructor { name, fields });

        let data = just(Token::Data)
            .ignore_then(qual_proper.clone())
            .then(var_id.repeated())
            .then(just(Token::Equals).ignore_then(constructor.clone().separated_by(just(Token::Pipe))).or_not())
            .map(|((name, params), constructors)| Decl::Data(name, params, constructors.unwrap_or_default()));

        let type_alias = just(Token::TypeKw)
            .ignore_then(qual_proper.clone())
            .then(var_id.repeated())
            .then_ignore(just(Token::Equals))
            .then(type_.clone())
            .map(|((name, params), t)| Decl::TypeAlias(name, params, t));

        let newtype = just(Token::Newtype)
            .ignore_then(qual_proper.clone())
            .then(var_id.repeated())
            .then_ignore(just(Token::Equals))
            .then(constructor.clone())
            .map(|((name, params), constr)| Decl::Newtype(name, params, constr));

        let fundep = var_id.repeated().at_least(1).then_ignore(just(Token::Arrow)).then(var_id.repeated().at_least(1)).map(|(f, t)| Fundep { from: f, to: t });

        let atomic_type = choice((
            qual_proper.clone().map(Type::Constructor),
            var_id.map(Type::Var),
            just(Token::Unit).to(Type::Unit),
            type_.clone().delimited_by(just(Token::LeftSquare), just(Token::RightSquare)).map(|t| Type::List(Box::new(t))),
            type_.clone().separated_by(just(Token::Comma)).delimited_by(just(Token::LeftParen), just(Token::RightParen)).map(|ts| if ts.len() == 1 { ts[0].clone() } else { Type::Tuple(ts) }),
        ));
        let app_type = atomic_type.clone().then(atomic_type.clone().repeated()).foldl(|f, a| Type::App(Box::new(f), Box::new(a)));

        let single_constraint = app_type.clone().then_ignore(just(Token::DoubleArrow)).map(|t| vec![t]);
        let tuple_constraints = app_type.clone().separated_by(just(Token::Comma)).at_least(1).delimited_by(just(Token::LeftParen), just(Token::RightParen)).then_ignore(just(Token::DoubleArrow));
        let constraints = choice((tuple_constraints, single_constraint));

        let class = just(Token::Class)
            .ignore_then(constraints.clone().or_not())
            .then(qual_proper.clone())
            .then(var_id.repeated())
            .then(just(Token::Pipe).ignore_then(fundep.separated_by(just(Token::Comma))).or_not())
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|((((constraints, name), params), fundeps), methods)| {
                Decl::Class(constraints.unwrap_or_default(), name, params, methods.unwrap_or_default(), fundeps.unwrap_or_default())
            });

        let instance = just(Token::Else).or_not()
            .then_ignore(just(Token::Instance))
            .then(constraints.or_not())
            .then(qual_proper.clone())
            .then(type_.clone().repeated())
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|((((is_else, constraints), name), types), methods)| {
                Decl::Instance(constraints.unwrap_or_default(), name, types, methods.unwrap_or_default(), is_else.is_some())
            });

        // Atomic binder for function argument positions.
        // Does NOT allow top-level constructor application (e.g. `Ctor arg1 arg2`);
        // constructor patterns with arguments must be parenthesised: `(Ctor arg1 arg2)`.
        // This prevents `f Query _from st` from being mis-parsed as `f` with one binder
        // `Query(_from, st)` instead of three binders `Query`, `_from`, `st`.
        let arg_binder = {
            let var_id_a = filter_map(|span, tok| match tok {
                Token::VarIdent(n) => Ok(n),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let proper_id_a = filter_map(|span, tok| match tok {
                Token::ProperName(n) => Ok(n),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let num_a = filter_map(|span, tok| match tok {
                Token::Number(n) => Ok(n),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let string_a = filter_map(|span, tok| match tok {
                Token::String(s) => Ok(s),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let char_a = filter_map(|span, tok| match tok {
                Token::Char(c) => Ok(c),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let atom_a = filter_map(|span, tok| match tok {
                Token::Atom(a) => Ok(a),
                _ => Err(Error::expected_input_found(span, Vec::new(), Some(tok))),
            });
            let qual_proper_a = proper_id_a.separated_by(just(Token::Dot)).at_least(1).map(|parts: Vec<String>| parts.join("."));

            let atomic_b = choice((
                var_id_a.clone().map(Binder::Var),
                qual_proper_a.clone().map(|n| Binder::Constructor(n, vec![])),
                just(Token::Wildcard).to(Binder::Wildcard),
                num_a.map(Binder::Number),
                string_a.map(Binder::String),
                char_a.map(Binder::Char),
                atom_a.map(Binder::Atom),
                binder.clone()
                    .separated_by(just(Token::Comma))
                    .at_least(1)
                    .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                    .map(|bs: Vec<Binder>| if bs.len() == 1 { bs[0].clone() } else { Binder::Tuple(bs) }),
                binder.clone()
                    .separated_by(just(Token::Comma))
                    .then(just(Token::Pipe).ignore_then(binder.clone()).or_not())
                    .delimited_by(just(Token::LeftSquare), just(Token::RightSquare))
                    .map(|(bs, tail): (Vec<Binder>, Option<Binder>)| {
                        let mut res = bs;
                        if let Some(t) = tail { res.push(t); }
                        Binder::List(res)
                    }),
                just(Token::Operator("<<".to_string()))
                    .ignore_then(binder.clone().separated_by(just(Token::Comma)))
                    .then_ignore(just(Token::Operator(">>".to_string())))
                    .map(Binder::Binary),
            ));
            let named_a = var_id_a.then_ignore(just(Token::Operator("@".to_string()))).then(atomic_b.clone()).map(|(n, b)| Binder::Named(n, Box::new(b))).or(atomic_b);
            named_a.then(just(Token::DoubleColon).ignore_then(type_.clone()).or_not()).map(|(b, t)| match t {
                Some(ty) => Binder::TypeAnn(Box::new(b), ty),
                None => b,
            })
        };

        let val_guard = just(Token::Pipe)
            .ignore_then(expr.clone().separated_by(just(Token::Comma)))
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .map(|(conditions, body)| ValGuard { conditions, body });

        let value_guarded = var_or_op.clone()
            .then(arg_binder.clone().repeated())
            .then(val_guard.repeated().at_least(1))
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|(((name, pats), guards), where_decls)| {
                Decl::ValueGuarded(name, pats, guards, where_decls.unwrap_or_default())
            });

        let value = var_or_op.clone()
            .then(arg_binder.clone().repeated())
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|(((name, pats), body), where_decls)| {
                Decl::Value(name, pats, body, where_decls.unwrap_or_default())
            });

        let infix_val = binder.clone()
            .then(op_id)
            .then(binder.clone())
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|((((lhs, op), rhs), body), where_decls)| {
                Decl::Value(op, vec![lhs, rhs], body, where_decls.unwrap_or_default())
            });

        let pat_bind = binder.clone()
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .then(just(Token::Where).ignore_then(decl.clone().separated_by(just(Token::Semicolon)).delimited_by(just(Token::LeftBrace), just(Token::RightBrace))).or_not())
            .map(|((p, body), where_decls)| Decl::PatBind(p, body, where_decls.unwrap_or_default()));

        let foreign = just(Token::Foreign).ignore_then(just(Token::Import)).ignore_then(choice((
            just(Token::Data).ignore_then(qual_proper.clone()).then_ignore(just(Token::DoubleColon)).then(type_.clone()).map(|(n, t)| Decl::ForeignData(n, t)),
            string.or(var_id).then(var_or_op.clone().or_not()).then_ignore(just(Token::DoubleColon)).then(type_.clone()).map(|((orig, local), t)| {
                let l = local.unwrap_or_else(|| orig.clone());
                Decl::ForeignImport(orig, l, t)
            })
        )));

        let infix = choice((just(Token::Infix), just(Token::Infixl), just(Token::Infixr)))
            .then(num)
            .then(var_or_op.clone().or(op_id))
            .then_ignore(just(Token::As))
            .then(var_or_op.clone().or(op_id))
            .map(|(((tok, prec), op), alias)| {
                let assoc = match tok {
                    Token::Infixl => Assoc::Left,
                    Token::Infixr => Assoc::Right,
                    _ => Assoc::None,
                };
                Decl::Infix(assoc, prec as i32, op, alias)
            });

        choice((
            import,
            data,
            type_alias,
            newtype,
            class,
            instance,
            foreign,
            infix,
            var_or_op.clone().then_ignore(just(Token::DoubleColon)).then(type_.clone()).map(|(n, t)| Decl::TypeSignature(n, t)),
            infix_val,
            value_guarded,
            value,
            pat_bind,
        ))
    })
}
