use crate::ids::ActorId;
use std::sync::Arc as StdArc;

/// An immutable, cheaply clonable UTF-8 string.
///
/// Cloning shares the underlying buffer, so copies are O(1) regardless of the
/// string's length.
#[derive(Debug, Clone)]
pub struct MorphString {
    data: StdArc<str>,
}

impl MorphString {
    /// Creates a string sharing a new copy of `s`.
    pub fn new(s: &str) -> Self {
        MorphString { data: s.into() }
    }

    /// Borrows the string contents.
    pub fn as_str(&self) -> &str {
        &self.data
    }

    /// Returns the length in bytes (not characters).
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the string has zero length.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl std::fmt::Display for MorphString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl PartialEq for MorphString {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl std::borrow::Borrow<str> for MorphString {
    fn borrow(&self) -> &str {
        &self.data
    }
}

/// A struct instance: a type name plus its named field values.
///
/// Field order is preserved as given at construction.
#[derive(Debug, Clone)]
pub struct MorphStruct {
    /// The name of the struct type this value was created from.
    pub type_name: String,
    /// Field name/value pairs in declaration order.
    pub fields: Vec<(String, MorphValue)>,
}

impl MorphStruct {
    /// Creates a struct value named `type_name` with the given fields.
    pub fn new(type_name: &str, fields: Vec<(String, MorphValue)>) -> Self {
        MorphStruct {
            type_name: type_name.to_string(),
            fields,
        }
    }

    /// Looks up a field by name, returning `None` if it is not present.
    pub fn get_field(&self, name: &str) -> Option<&MorphValue> {
        self.fields.iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }
}

/// An enum instance: a type name, the chosen variant, and optional payload.
#[derive(Debug, Clone)]
pub struct MorphEnum {
    /// The name of the enum type this value was created from.
    pub type_name: String,
    /// The name of the selected variant.
    pub variant: String,
    /// The variant's single payload, if the variant carries one.
    pub payload: Option<Box<MorphValue>>,
}

impl MorphEnum {
    /// Creates an enum value for variant `variant`, with an optional payload.
    pub fn new(type_name: &str, variant: &str, payload: Option<MorphValue>) -> Self {
        MorphEnum {
            type_name: type_name.to_string(),
            variant: variant.to_string(),
            payload: payload.map(Box::new),
        }
    }
}

/// A reference to a function, identified by its unique `id` and source name.
#[derive(Debug, Clone)]
pub struct FunctionRef {
    /// Unique id used to dispatch calls.
    pub id: u64,
    /// The function's source-level name, for diagnostics.
    pub name: String,
}

impl FunctionRef {
    /// Creates a reference to the function with id `id` named `name`.
    pub fn new(id: u64, name: &str) -> Self {
        FunctionRef {
            id,
            name: name.to_string(),
        }
    }
}

/// A machine address, tagged by how it may be dereferenced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pointer {
    /// An untracked raw address.
    Raw(u64),
    /// An address of a reference-counted handle, keeping its target alive.
    ArcHandle(u64),
}

/// The body of a message sent between actors.
#[derive(Debug, Clone, PartialEq)]
pub enum MessagePayload {
    /// An ordinary value to be handed to the receiving actor.
    Value(MorphValue),
    /// A control signal rather than data.
    Signal(SignalType),
}

/// A control signal that can interrupt an actor's message loop.
#[derive(Debug, Clone, PartialEq)]
pub enum SignalType {
    /// Invalidate the actor so that it stops accepting work.
    Poison,
    /// Ask the actor to shut down.
    Terminate,
    /// A user-defined signal carrying its own name.
    Custom(String),
}

/// Any value that a Morph program manipulates at runtime.
#[derive(Debug, Clone)]
pub enum MorphValue {
    /// A boolean.
    Bool(bool),
    /// A signed 8-bit integer.
    Int8(i8),
    /// A signed 16-bit integer.
    Int16(i16),
    /// A signed 32-bit integer.
    Int32(i32),
    /// A signed 64-bit integer.
    Int64(i64),
    /// An unsigned 8-bit integer.
    UInt8(u8),
    /// An unsigned 16-bit integer.
    UInt16(u16),
    /// An unsigned 32-bit integer.
    UInt32(u32),
    /// An unsigned 64-bit integer.
    UInt64(u64),
    /// A 32-bit floating point number.
    Float32(f32),
    /// A 64-bit floating point number.
    Float64(f64),
    /// An immutable string.
    String(MorphString),
    /// The absence of a value.
    Unit,
    /// An optional value, `None` when absent.
    Optional(Option<Box<MorphValue>>),
    /// A result carrying either an `Ok` or an `Err` value.
    Result(Result<Box<MorphValue>, Box<MorphValue>>),
    /// A struct instance.
    Struct(MorphStruct),
    /// An enum instance.
    Enum(MorphEnum),
    /// A homogeneous, dynamically sized array.
    Array(Vec<MorphValue>),
    /// A fixed-size heterogeneous tuple.
    Tuple(Vec<MorphValue>),
    /// A callable function reference.
    Function(FunctionRef),
    /// A reference to a spawned actor.
    ActorRef(ActorId),
    /// A machine pointer.
    Pointer(Pointer),
}

impl MorphValue {
    /// Returns the Morph source-level type name of this value.
    pub fn type_name(&self) -> &'static str {
        match self {
            MorphValue::Bool(_) => "bool",
            MorphValue::Int8(_) => "i8",
            MorphValue::Int16(_) => "i16",
            MorphValue::Int32(_) => "i32",
            MorphValue::Int64(_) => "i64",
            MorphValue::UInt8(_) => "u8",
            MorphValue::UInt16(_) => "u16",
            MorphValue::UInt32(_) => "u32",
            MorphValue::UInt64(_) => "u64",
            MorphValue::Float32(_) => "f32",
            MorphValue::Float64(_) => "f64",
            MorphValue::String(_) => "str",
            MorphValue::Unit => "void",
            MorphValue::Optional(_) => "optional",
            MorphValue::Result(_) => "result",
            MorphValue::Struct(_) => "struct",
            MorphValue::Enum(_) => "enum",
            MorphValue::Array(_) => "array",
            MorphValue::Tuple(_) => "tuple",
            MorphValue::Function(_) => "function",
            MorphValue::ActorRef(_) => "actor",
            MorphValue::Pointer(_) => "pointer",
        }
    }

    /// Returns whether this value is truthy in a boolean context.
    ///
    /// Zero, `Unit`, an empty string, an empty array, and a missing optional
    /// are falsy; every other variant is truthy.
    pub fn is_truthy(&self) -> bool {
        match self {
            MorphValue::Bool(b) => *b,
            MorphValue::Int64(n) => *n != 0,
            MorphValue::UInt64(n) => *n != 0,
            MorphValue::Float64(f) => *f != 0.0,
            MorphValue::String(s) => !s.as_str().is_empty(),
            MorphValue::Unit => false,
            MorphValue::Optional(opt) => opt.is_some(),
            MorphValue::Array(arr) => !arr.is_empty(),
            _ => true,
        }
    }

    /// Returns the contained boolean, or `None` for any other variant.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            MorphValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Returns the contained value widened to `i64`.
    ///
    /// Only the signed integer variants convert; anything else returns `None`.
    pub fn as_int64(&self) -> Option<i64> {
        match self {
            MorphValue::Int8(v) => Some(*v as i64),
            MorphValue::Int16(v) => Some(*v as i64),
            MorphValue::Int32(v) => Some(*v as i64),
            MorphValue::Int64(v) => Some(*v),
            _ => None,
        }
    }

    /// Returns the contained value widened to `f64`.
    ///
    /// Only the floating point variants convert; anything else returns `None`.
    pub fn as_float64(&self) -> Option<f64> {
        match self {
            MorphValue::Float32(v) => Some(*v as f64),
            MorphValue::Float64(v) => Some(*v),
            _ => None,
        }
    }
}

impl PartialEq for MorphValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (MorphValue::Bool(a), MorphValue::Bool(b)) => a == b,
            (MorphValue::Int8(a), MorphValue::Int8(b)) => a == b,
            (MorphValue::Int16(a), MorphValue::Int16(b)) => a == b,
            (MorphValue::Int32(a), MorphValue::Int32(b)) => a == b,
            (MorphValue::Int64(a), MorphValue::Int64(b)) => a == b,
            (MorphValue::UInt8(a), MorphValue::UInt8(b)) => a == b,
            (MorphValue::UInt16(a), MorphValue::UInt16(b)) => a == b,
            (MorphValue::UInt32(a), MorphValue::UInt32(b)) => a == b,
            (MorphValue::UInt64(a), MorphValue::UInt64(b)) => a == b,
            (MorphValue::Float32(a), MorphValue::Float32(b)) => a == b,
            (MorphValue::Float64(a), MorphValue::Float64(b)) => a == b,
            (MorphValue::String(a), MorphValue::String(b)) => a == b,
            (MorphValue::Unit, MorphValue::Unit) => true,
            (MorphValue::ActorRef(a), MorphValue::ActorRef(b)) => a == b,
            (MorphValue::Pointer(a), MorphValue::Pointer(b)) => a == b,
            (MorphValue::Array(a), MorphValue::Array(b)) => a == b,
            (MorphValue::Tuple(a), MorphValue::Tuple(b)) => a == b,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_type_names() {
        assert_eq!(MorphValue::Bool(true).type_name(), "bool");
        assert_eq!(MorphValue::Int32(42).type_name(), "i32");
        assert_eq!(MorphValue::Float64(3.15).type_name(), "f64");
        assert_eq!(MorphValue::Unit.type_name(), "void");
        assert_eq!(
            MorphValue::String(MorphString::new("hi")).type_name(),
            "str"
        );
        assert_eq!(MorphValue::Array(vec![]).type_name(), "array");
    }

    #[test]
    fn test_value_truthiness() {
        assert!(MorphValue::Bool(true).is_truthy());
        assert!(!MorphValue::Bool(false).is_truthy());
        assert!(!MorphValue::Int64(0).is_truthy());
        assert!(MorphValue::Int64(1).is_truthy());
        assert!(!MorphValue::Unit.is_truthy());
        assert!(!MorphValue::String(MorphString::new("")).is_truthy());
        assert!(MorphValue::String(MorphString::new("x")).is_truthy());
    }

    #[test]
    fn test_value_equality() {
        assert_eq!(MorphValue::Int32(42), MorphValue::Int32(42));
        assert_ne!(MorphValue::Int32(42), MorphValue::Int64(42));
        assert_eq!(
            MorphValue::Array(vec![MorphValue::Int32(1), MorphValue::Int32(2)]),
            MorphValue::Array(vec![MorphValue::Int32(1), MorphValue::Int32(2)])
        );
    }

    #[test]
    fn test_struct_field_access() {
        let s = MorphStruct::new(
            "Point",
            vec![
                ("x".to_string(), MorphValue::Float64(1.0)),
                ("y".to_string(), MorphValue::Float64(2.0)),
            ],
        );
        assert_eq!(s.get_field("x").unwrap().as_float64(), Some(1.0));
        assert_eq!(s.get_field("y").unwrap().as_float64(), Some(2.0));
        assert!(s.get_field("z").is_none());
    }
}
