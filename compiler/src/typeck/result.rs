use rustc_hash::FxHashMap;

use crate::ast::NodeId;
use crate::typeck::types::{EffectSet, Ty};

pub struct TypeCheckResult {
    pub type_map: FxHashMap<NodeId, Ty>,
    pub effect_map: FxHashMap<NodeId, EffectSet>,
    pub warnings: Vec<crate::diagnostic::Diagnostic>,
}

impl TypeCheckResult {
    pub fn new(
        type_map: FxHashMap<NodeId, Ty>,
        effect_map: FxHashMap<NodeId, EffectSet>,
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
            type_map: FxHashMap::default(),
            effect_map: FxHashMap::default(),
            warnings: Vec::new(),
        }
    }
}
