use logos::Logos;

#[derive(Logos, Debug, PartialEq, Eq, Hash, Clone)]
#[logos(skip r"[ \t\r\n]+")] // Skip whitespace
#[logos(skip r"--[^\n]*")]   // Skip line comments
#[logos(skip r"\{-([^-\}]|-[^\}]|\}[^-])*-\}")] // Simple block comments
pub enum Token {
    // Special Symbols
    #[token("()")]
    Unit,
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("[")]
    LeftSquare,
    #[token("]")]
    RightSquare,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token(",")]
    Comma,
    #[regex(";+")]
    Semicolon,
    #[token("`")]
    Backtick,
    #[token("::")]
    DoubleColon,
    #[token("->")]
    Arrow,
    #[token("=>")]
    DoubleArrow,
    #[token("<-")]
    LeftArrow,
    #[token("\\")]
    Backslash,
    #[token("..", priority = 4)]
    TwoDots,

    // Keywords
    #[token("module")]
    Module,
    #[token("where")]
    Where,
    #[token("import")]
    Import,
    #[token("as")]
    As,
    #[token("hiding")]
    Hiding,
    #[token("type")]
    TypeKw,
    #[token("data")]
    Data,
    #[token("newtype")]
    Newtype,
    #[token("class")]
    Class,
    #[token("instance")]
    Instance,
    #[token("foreign")]
    Foreign,
    #[token("infix")]
    Infix,
    #[token("infixl")]
    Infixl,
    #[token("infixr")]
    Infixr,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("do")]
    Do,
    #[token("receive")]
    Receive,
    #[token("after")]
    After,
    #[token("forall")]
    Forall,

    // Identifiers
    #[token("_", priority = 3)]
    Wildcard,

    #[regex("[a-z_][a-zA-Z0-9_']*", |lex| lex.slice().to_string(), priority = 2)]
    VarIdent(String),

    #[regex("[A-Z][a-zA-Z0-9_']*", |lex| lex.slice().to_string())]
    ProperName(String),

    // Literals
    #[regex("[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Number(i64),

    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().to_string())]
    Float(String),

    #[regex(r#""([^"\\]|\\.)*""#, |lex| {
        let s = lex.slice();
        s[1..s.len()-1].to_string()
    })]
    String(String),

    #[regex(r#"'([^'\\]|\\.)'"#, |lex| {
        let s = lex.slice();
        s.chars().nth(1).unwrap()
    })]
    Char(char),

    #[regex(r#":([a-zA-Z_][a-zA-Z0-9_']*|#?"([^"\\]|\\.)*")"#, |lex| {
        let s = lex.slice();
        s[1..].to_string()
    })]
    Atom(String),

    // Operators
    #[token("=", priority = 3)]
    Equals,
    #[token("|", priority = 3)]
    Pipe,
    #[token(".", priority = 5)]
    Dot,
    #[regex(r"[=|<>\+\-\*/%^&!\$#@:\?\.]+", |lex| lex.slice().to_string(), priority = 2)]
    Operator(String),
}
