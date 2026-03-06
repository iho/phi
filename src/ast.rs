#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Module {
    pub name: String,
    pub exports: Option<Vec<Export>>,
    pub declarations: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Export {
    Var(String),
    Type(String, Option<Vec<String>>, bool), // name, constructor list, has_all (..)
    Class(String),
    Module(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decl {
    TypeSignature(String, Type),
    Value(String, Vec<Binder>, Expr, Vec<Decl>),
    ValueGuarded(String, Vec<Binder>, Vec<ValGuard>, Vec<Decl>),
    PatBind(Binder, Expr, Vec<Decl>),
    Data(String, Vec<String>, Vec<Constructor>),
    TypeAlias(String, Vec<String>, Type),
    Newtype(String, Vec<String>, Constructor),
    Class(Vec<Type>, String, Vec<String>, Vec<Decl>, Vec<Fundep>),
    Instance(Vec<Type>, String, Vec<Type>, Vec<Decl>, bool),
    Import(String, Option<Vec<ImportItem>>, Option<String>, bool),
    ForeignImport(String, String, Type),
    ForeignData(String, Type),
    Infix(Assoc, i32, String, String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValGuard {
    pub conditions: Vec<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fundep {
    pub from: Vec<String>,
    pub to: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Assoc {
    Left,
    Right,
    None,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ImportItem {
    Var(String),
    Type(String, Option<Vec<String>>, bool),
    Class(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Constructor {
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub name: Option<String>,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(String),
    Constructor(String),
    App(Box<Type>, Box<Type>),
    Arrow(Box<Type>, Box<Type>),
    Forall(Vec<String>, Box<Type>),
    Constrained(Vec<Type>, Box<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Record(Vec<Field>),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(String),
    Number(i64),
    Float(String),
    String(String),
    Char(char),
    Atom(String),
    Binary(Vec<Expr>),
    App(Box<Expr>, Box<Expr>),
    BinOp(Box<Expr>, String, Box<Expr>),
    Negate(Box<Expr>),
    Range(Box<Expr>, Box<Expr>),
    Lam(Vec<Binder>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Case(Vec<Expr>, Vec<CaseBranch>),
    Let(Vec<Decl>, Box<Expr>),
    Do(Vec<DoStatement>),
    Receive(Vec<CaseBranch>, Option<Box<AfterClause>>),
    List(Vec<Expr>, Option<Box<Expr>>),
    Comprehension(Box<Expr>, Vec<CompStmt>),
    Record(Vec<(String, Expr)>),
    RecordUpdate(Box<Expr>, Vec<(String, Expr)>),
    FieldAccess(Box<Expr>, String), // NEW: expr.field
    Tuple(Vec<Expr>),
    TypeAnn(Box<Expr>, Type),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CompStmt {
    Bind(Binder, Expr),
    Guard(Expr),
    Let(Vec<Decl>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CaseBranch {
    pub binders: Vec<Binder>,
    pub guards: Vec<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DoStatement {
    Expr(Expr),
    Bind(Binder, Expr),
    Let(Vec<Decl>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AfterClause {
    pub timeout: Box<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Binder {
    Var(String),
    Constructor(String, Vec<Binder>),
    Wildcard,
    Number(i64),
    String(String),
    Char(char),
    Atom(String),
    Tuple(Vec<Binder>),
    List(Vec<Binder>),
    Binary(Vec<Binder>),
    Named(String, Box<Binder>),
    TypeAnn(Box<Binder>, Type),
}
