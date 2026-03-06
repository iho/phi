use crate::type_sys::PolyType;
// use crate::ast::Decl;

// Persistent hash-map: clone is O(1) (structural sharing).
// This is the core enabler for cheap env.clone() on every lambda/let/case scope.
pub type IMap<K, V> = im::HashMap<K, V>;

#[derive(Debug, Clone)]
pub struct ClassInfo {
    pub args: Vec<String>,
    pub members: Vec<crate::ast::Decl>, // TypeSignature decls
}

#[derive(Debug, Clone)]
pub struct InstanceInfo {
    pub types: Vec<crate::type_sys::MonoType>,
    pub dict_name: String,
    pub members: Vec<crate::ast::Decl>, // Value decls
    pub constraints: Vec<crate::type_sys::MonoType>,
    pub module: String,
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    // Variable/Function name -> (Module where defined, Type Scheme)
    pub bindings: IMap<String, (String, PolyType)>,
    // Type alias -> Type
    pub aliases: IMap<String, crate::type_sys::MonoType>,
    // Class name -> Class info
    pub classes: IMap<String, ClassInfo>,
    // Class name -> List of instances
    pub instances: IMap<String, Vec<InstanceInfo>>,
    // Member name -> Class name
    pub member_to_class: IMap<String, String>,
    // Operator/Term alias -> Fully qualified name
    pub term_aliases: IMap<String, String>,
    // Module alias -> Real module name
    pub module_aliases: IMap<String, String>,
    // Class name -> List of member fully qualified names
    pub class_to_members: IMap<String, Vec<String>>,
    // Locally-bound schemes for the current inference scope.
    // Only populated during type inference (module == "local").
    // Used by generalize() to find env free vars without scanning all 20k global bindings.
    pub local_schemes: im::Vector<PolyType>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    /// Extends the environment with a new binding. 
    /// If `mod_name` is provided, also adds a fully qualified binding.
    pub fn extend(&mut self, module: &str, name: &str, scheme: PolyType, mod_name: Option<&str>) {
        self.bindings.insert(name.to_string(), (module.to_string(), scheme.clone()));
        if let Some(m) = mod_name {
            let fqdn = format!("{}.{}", m, name);
            self.bindings.insert(fqdn, (module.to_string(), scheme.clone()));
        }
        if module == "local" {
            self.local_schemes.push_back(scheme);
        }
    }

    pub fn add_alias(&mut self, name: &str, ty: crate::type_sys::MonoType) {
        self.aliases.insert(name.to_string(), ty);
    }

    pub fn lookup(&self, name: &str) -> Option<&(String, PolyType)> {
        self.bindings.get(name)
    }

    pub fn lookup_alias(&self, name: &str) -> Option<&crate::type_sys::MonoType> {
        self.aliases.get(name)
    }

    pub fn resolve_term_alias(&self, name: &str) -> String {
        let parts: Vec<&str> = name.split('.').collect();
        if parts.len() == 1 {
            self.term_aliases.get(name).cloned().unwrap_or_else(|| name.to_string())
        } else {
            let member = parts.last().unwrap();
            let mod_parts = &parts[..parts.len() - 1];
            let mod_name = mod_parts.join(".");
            
            if let Some(full_mod) = self.module_aliases.get(&mod_name) {
                format!("{}.{}", full_mod, member)
            } else {
                self.term_aliases.get(name).cloned().unwrap_or_else(|| name.to_string())
            }
        }
    }
}
