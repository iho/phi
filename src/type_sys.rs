use std::fmt;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MonoType {
    Var(usize),             // Unification variable (e.g., v1, v2)
    BoundVar(String),       // Bound type variable (e.g., 'a' from forall)
    Con(String),            // Type Constructor (e.g., Int, String)
    App(Box<MonoType>, Box<MonoType>), // Type Application (e.g., List a)
    #[allow(dead_code)]
    RowEmpty,               // Empty row for records
    #[allow(dead_code)]
    RowExtend(String, Box<MonoType>, Box<MonoType>), // Row extension
    Constrained(String, Vec<MonoType>, Box<MonoType>), // Type class constraint (e.g., Eq a => a)
}

impl MonoType {
    pub fn arrow(domain: MonoType, codomain: MonoType) -> MonoType {
        MonoType::App(
            Box::new(MonoType::App(
                Box::new(MonoType::Con("->".to_string())),
                Box::new(domain),
            )),
            Box::new(codomain),
        )
    }

    pub fn ty_int() -> MonoType {
        MonoType::Con("Integer".to_string())
    }

    pub fn ty_bool() -> MonoType {
        MonoType::Con("Boolean".to_string())
    }

    pub fn ty_string() -> MonoType {
        MonoType::Con("String".to_string())
    }
}

// Display implementation for better debugging/error messages
impl fmt::Display for MonoType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MonoType::Var(id) => write!(f, "?{}", id),
            MonoType::BoundVar(name) => write!(f, "{}", name),
            MonoType::Con(name) => write!(f, "{}", name),
            MonoType::App(func, arg) => {
                // Formatting -> nicely
                if let MonoType::App(inner_f, inner_arg) = &**func {
                    if let MonoType::Con(n) = &**inner_f {
                        if n == "->" {
                            return write!(f, "({} -> {})", inner_arg, arg);
                        }
                    }
                }
                write!(f, "({} {})", func, arg)
            }
            MonoType::RowEmpty => write!(f, "()"),
            MonoType::RowExtend(l, t, r) => write!(f, "({}: {} | {})", l, t, r),
            MonoType::Constrained(c, args, ty) => {
                write!(f, "({} ", c)?;
                for a in args {
                    write!(f, "{} ", a)?;
                }
                write!(f, "=> {})", ty)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyType {
    pub vars: HashSet<String>,
    pub ty: MonoType,
}

impl PolyType {
    pub fn mono(ty: MonoType) -> Self {
        PolyType { vars: HashSet::new(), ty }
    }
}

impl fmt::Display for PolyType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "forall")?;
            let mut sorted: Vec<&String> = self.vars.iter().collect();
            sorted.sort();
            for v in sorted {
                write!(f, " {}", v)?;
            }
            write!(f, ". {}", self.ty)
        }
    }
}
