use std::collections::BTreeSet;
use std::fmt;

/// A type as inferred by the type checker.
///
/// [`Ty::TypeVar`] stands for an as-yet-unknown type; such variables are
/// numbered and resolved by the unifier in [`crate::typeck::unification`].
/// [`Ty::Error`] is the poison value used to keep checking after an error has
/// already been reported.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    /// The `bool` type.
    Bool,
    /// A signed or unsigned integer of the given width.
    Int(IntKind),
    /// A floating point type of the given width.
    Float(FloatKind),
    /// The string type.
    Str,
    /// The type of a function that returns nothing meaningful.
    Void,
    /// The bottom type: no value inhabits it.
    Never,
    /// A heterogeneous tuple of the given element types.
    Tuple(Vec<Ty>),
    /// A homogeneous array of `inner`.
    Array(Box<Ty>),
    /// An optional (`inner?`) value.
    Optional(Box<Ty>),
    /// A fallible computation with separate success and error types.
    Result {
        /// Type of the success value.
        ok: Box<Ty>,
        /// Type of the error value.
        err: Box<Ty>,
    },
    /// A user-defined or builtin named type applied to `args`.
    Named {
        /// The type's name as written in the source.
        name: String,
        /// Type arguments, empty for a non-generic type.
        args: Vec<Ty>,
    },
    /// A capability-guarded reference to `inner`.
    Ref {
        /// The capability the reference is held at.
        cap: Capability,
        /// The referent type.
        inner: Box<Ty>,
    },
    /// A function type.
    Fn {
        /// Parameter types.
        params: Vec<Ty>,
        /// Return type.
        ret: Box<Ty>,
        /// Effects the function is declared to perform.
        effects: EffectSet,
    },
    /// A reference to an actor of the named type.
    Actor(String),
    /// An unresolved inference variable, identified by its index.
    TypeVar(u32),
    /// The type produced after a reported error; suppresses cascading errors.
    Error,
}

/// The width and signedness of a [`Ty::Int`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntKind {
    /// Signed 8-bit integer (`i8`).
    I8,
    /// Signed 16-bit integer (`i16`).
    I16,
    /// Signed 32-bit integer (`i32`).
    I32,
    /// Signed 64-bit integer (`i64`).
    I64,
    /// Unsigned 8-bit integer (`u8`).
    U8,
    /// Unsigned 16-bit integer (`u16`).
    U16,
    /// Unsigned 32-bit integer (`u32`).
    U32,
    /// Unsigned 64-bit integer (`u64`).
    U64,
    /// Pointer-sized signed integer (`isize`).
    ISize,
    /// Pointer-sized unsigned integer (`usize`).
    USize,
}

/// The width of a [`Ty::Float`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatKind {
    /// 32-bit floating point (`f32`).
    F32,
    /// 64-bit floating point (`f64`).
    F64,
}

/// The capability a reference is held at.
///
/// Stronger capabilities can be weakened but not the reverse, so moving out of
/// an `Iso` reference is allowed while moving out of a `Ref` is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    /// Unique, transferable ownership; may be moved.
    Iso,
    /// Shared read-only access to a value owned elsewhere.
    Val,
    /// A borrowed reference; ownership stays with the issuer.
    Ref,
}

/// A tracked side effect that a function must declare before performing it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Effect {
    /// Performing file, console, or other blocking I/O.
    IO,
    /// Performing network I/O.
    Net,
    /// Reading the clock or sleeping.
    Time,
    /// Touching process-level facilities such as the environment.
    System,
}

/// An immutable set of [`Effect`]s, ordered so sets compare canonically.
///
/// An empty set means the function is `pure`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EffectSet {
    effects: BTreeSet<Effect>,
}

impl EffectSet {
    /// Creates the empty (pure) effect set.
    pub fn empty() -> Self {
        Self {
            effects: BTreeSet::new(),
        }
    }

    /// Creates the empty (pure) effect set, exactly as [`EffectSet::empty`] does.
    pub fn pure() -> Self {
        Self::empty()
    }

    /// Creates a set containing the given effects; duplicates are collapsed.
    pub fn new(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
        }
    }

    /// Adds `effect` to the set.
    pub fn insert(&mut self, effect: Effect) {
        self.effects.insert(effect);
    }

    /// Returns a set containing every effect in either set.
    pub fn union(&self, other: &EffectSet) -> EffectSet {
        EffectSet {
            effects: self.effects.union(&other.effects).copied().collect(),
        }
    }

    /// Returns `true` if every effect in this set also appears in `other`.
    ///
    /// This is the check used to decide whether a call is permitted.
    pub fn is_subset_of(&self, other: &EffectSet) -> bool {
        self.effects.is_subset(&other.effects)
    }

    /// Returns `true` if the set is empty, i.e. the function is pure.
    pub fn is_pure(&self) -> bool {
        self.effects.is_empty()
    }

    /// Iterates the effects in ascending declaration order.
    pub fn iter(&self) -> impl Iterator<Item = Effect> + '_ {
        self.effects.iter().copied()
    }

    /// Returns `true` if `effect` is a member of the set.
    pub fn contains(&self, effect: Effect) -> bool {
        self.effects.contains(&effect)
    }

    /// Returns the number of effects in the set.
    pub fn len(&self) -> usize {
        self.effects.len()
    }

    /// Returns `true` if the set contains no effects.
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }
}

impl Ty {
    /// Returns `true` if values of this type may cross an actor boundary.
    ///
    /// Function values and `Ref`-capability references may not; an `Iso`
    /// reference may, because sending it transfers ownership.
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

    /// Returns `true` for [`Ty::Int`] and [`Ty::Float`].
    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Float(_))
    }

    /// Returns `true` for [`Ty::Int`].
    pub fn is_int(&self) -> bool {
        matches!(self, Ty::Int(_))
    }

    /// Returns `true` for [`Ty::Float`].
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

/// Parses a source-level integer type name such as `"i32"` or `"usize"`.
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

/// Parses a source-level float type name, `"f32"` or `"f64"`.
pub fn float_kind_from_name(name: &str) -> Option<FloatKind> {
    match name {
        "f32" => Some(FloatKind::F32),
        "f64" => Some(FloatKind::F64),
        _ => None,
    }
}

/// Returns `true` if the literal `value` fits in an integer of type `kind`.
///
/// Used when an unsuffixed integer literal is checked against a contextual
/// type. `i64` always accepts, and `u64` accepts every non-negative value.
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
