use std::collections::BTreeSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Bool,
    Int(IntKind),
    Float(FloatKind),
    Str,
    Void,
    Never,
    Tuple(Vec<Ty>),
    Array(Box<Ty>),
    Optional(Box<Ty>),
    Result {
        ok: Box<Ty>,
        err: Box<Ty>,
    },
    Named {
        name: String,
        args: Vec<Ty>,
    },
    Ref {
        cap: Capability,
        inner: Box<Ty>,
    },
    Fn {
        params: Vec<Ty>,
        ret: Box<Ty>,
        effects: EffectSet,
    },
    Actor(String),
    TypeVar(u32),
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    ISize,
    USize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatKind {
    F32,
    F64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    Iso,
    Val,
    Ref,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Effect {
    IO,
    Net,
    Time,
    System,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EffectSet {
    effects: BTreeSet<Effect>,
}

impl EffectSet {
    pub fn empty() -> Self {
        Self {
            effects: BTreeSet::new(),
        }
    }

    pub fn pure() -> Self {
        Self::empty()
    }

    pub fn new(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
        }
    }

    pub fn insert(&mut self, effect: Effect) {
        self.effects.insert(effect);
    }

    pub fn union(&self, other: &EffectSet) -> EffectSet {
        EffectSet {
            effects: self.effects.union(&other.effects).copied().collect(),
        }
    }

    pub fn is_subset_of(&self, other: &EffectSet) -> bool {
        self.effects.is_subset(&other.effects)
    }

    pub fn is_pure(&self) -> bool {
        self.effects.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = Effect> + '_ {
        self.effects.iter().copied()
    }

    pub fn contains(&self, effect: Effect) -> bool {
        self.effects.contains(&effect)
    }

    pub fn len(&self) -> usize {
        self.effects.len()
    }

    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }
}

impl Ty {
    pub fn is_sendable(&self) -> bool {
        match self {
            Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Void | Ty::Never | Ty::Error => {
                true
            }
            Ty::Tuple(elements) => elements.iter().all(|t| t.is_sendable()),
            Ty::Array(inner) => inner.is_sendable(),
            Ty::Optional(inner) => inner.is_sendable(),
            Ty::Result { ok, err } => ok.is_sendable() && err.is_sendable(),
            Ty::Named { args, .. } => args.iter().all(|t| t.is_sendable()),
            Ty::Ref { cap, inner } => match cap {
                Capability::Iso => true,
                Capability::Val => inner.is_sendable(),
                Capability::Ref => false,
            },
            Ty::Fn { .. } => false,
            Ty::Actor(_) => true,
            Ty::TypeVar(_) => true,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Ty::Int(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Ty::Float(_))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Int(k) => write!(f, "{}", k),
            Ty::Float(k) => write!(f, "{}", k),
            Ty::Str => write!(f, "str"),
            Ty::Void => write!(f, "void"),
            Ty::Never => write!(f, "never"),
            Ty::Tuple(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
            Ty::Array(inner) => write!(f, "[{}]", inner),
            Ty::Optional(inner) => write!(f, "{}?", inner),
            Ty::Result { ok, err } => write!(f, "Result<{}, {}>", ok, err),
            Ty::Named { name, args } => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Ty::Ref { cap, inner } => match cap {
                Capability::Iso => write!(f, "^{}", inner),
                Capability::Val => write!(f, "#{}", inner),
                Capability::Ref => write!(f, "&{}", inner),
            },
            Ty::Fn {
                params,
                ret,
                effects,
            } => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")?;
                if !effects.is_pure() {
                    write!(f, " throws {:?}", effects)?;
                }
                write!(f, " -> {}", ret)
            }
            Ty::Actor(name) => write!(f, "actor {}", name),
            Ty::TypeVar(v) => write!(f, "?{}", v),
            Ty::Error => write!(f, "<error>"),
        }
    }
}

impl fmt::Display for IntKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntKind::I8 => write!(f, "i8"),
            IntKind::I16 => write!(f, "i16"),
            IntKind::I32 => write!(f, "i32"),
            IntKind::I64 => write!(f, "i64"),
            IntKind::U8 => write!(f, "u8"),
            IntKind::U16 => write!(f, "u16"),
            IntKind::U32 => write!(f, "u32"),
            IntKind::U64 => write!(f, "u64"),
            IntKind::ISize => write!(f, "isize"),
            IntKind::USize => write!(f, "usize"),
        }
    }
}

impl fmt::Display for FloatKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FloatKind::F32 => write!(f, "f32"),
            FloatKind::F64 => write!(f, "f64"),
        }
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Effect::IO => write!(f, "IO"),
            Effect::Net => write!(f, "Net"),
            Effect::Time => write!(f, "Time"),
            Effect::System => write!(f, "System"),
        }
    }
}

impl fmt::Debug for EffectSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.effects.is_empty() {
            write!(f, "Pure")
        } else {
            write!(f, "{{")?;
            for (i, e) in self.effects.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", e)?;
            }
            write!(f, "}}")
        }
    }
}

pub fn int_kind_from_name(name: &str) -> Option<IntKind> {
    match name {
        "i8" => Some(IntKind::I8),
        "i16" => Some(IntKind::I16),
        "i32" => Some(IntKind::I32),
        "i64" => Some(IntKind::I64),
        "u8" => Some(IntKind::U8),
        "u16" => Some(IntKind::U16),
        "u32" => Some(IntKind::U32),
        "u64" => Some(IntKind::U64),
        "isize" => Some(IntKind::ISize),
        "usize" => Some(IntKind::USize),
        _ => None,
    }
}

pub fn float_kind_from_name(name: &str) -> Option<FloatKind> {
    match name {
        "f32" => Some(FloatKind::F32),
        "f64" => Some(FloatKind::F64),
        _ => None,
    }
}

pub fn can_coerce_int_literal(kind: IntKind, value: i64) -> bool {
    match kind {
        IntKind::I8 => value >= i8::MIN as i64 && value <= i8::MAX as i64,
        IntKind::I16 => value >= i16::MIN as i64 && value <= i16::MAX as i64,
        IntKind::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
        IntKind::I64 => true,
        IntKind::U8 => value >= 0 && value <= u8::MAX as i64,
        IntKind::U16 => value >= 0 && value <= u16::MAX as i64,
        IntKind::U32 => value >= 0 && value <= u32::MAX as i64,
        IntKind::U64 => value >= 0,
        IntKind::ISize => value >= isize::MIN as i64 && value <= isize::MAX as i64,
        IntKind::USize => value >= 0 && value <= usize::MAX as i64,
    }
}
