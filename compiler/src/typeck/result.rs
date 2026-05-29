use std::collections::HashMap;

use crate::ast::NodeId;
use crate::typeck::types::{EffectSet, Ty};

pub struct TypeCheckResult {
    pub type_map: HashMap<NodeId, Ty>,
    pub effect_map: HashMap<NodeId, EffectSet>,
    pub warnings: Vec<crate::diagnostic::Diagnostic>,
}

impl TypeCheckResult {
    pub fn new(
        type_map: HashMap<NodeId, Ty>,
        effect_map: HashMap<NodeId, EffectSet>,
        warnings: Vec<crate::diagnostic::Diagnostic>,
    ) -> Self {
        Self {
            type_map,
            effect_map,
            warnings,
        }
    }

    pub fn empty() -> Self {
        Self {
            type_map: HashMap::new(),
            effect_map: HashMap::new(),
            warnings: Vec::new(),
        }
    }
}
